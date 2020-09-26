(* Utilities for binary sequences (the Cantor space) *)

From set_theory Require Import lib fn set.

(* Cantor space *)
Definition C := nat -> bool.

(* A branch in the Cantor space *)
Definition Branch m (α β : C) := ∀i, i < m -> α i = β i.

Definition zeros (i : nat) := false.
Definition ones (i : nat) := true.
Definition pre m (α β : C) i := if i <? m then α i else β i.
Definition shift m (α : C) i := if i <? m then false else α (i - m).
Definition del m (α : C) i := α (m + i).

Notation "'{0}'" := (Singleton zeros).

Lemma Branch_refl m α : Branch m α α.
Proof. easy. Qed.

Lemma Branch_sym m α β : Branch m α β -> Branch m β α.
Proof. intros H i Hi. symmetry. auto. Qed.

Lemma Branch_trans m α β γ : Branch m α β -> Branch m β γ -> Branch m α γ.
Proof. intros H1 H2 i Hi. etransitivity. all: auto. Qed.

Lemma Branch_pre m α β : Branch m α (pre m α β).
Proof. intros i Hi. unfold pre. now apply ltb_lt in Hi; rewrite Hi. Qed.

Lemma Branch_restrict m n α β : m <= n -> Branch n α β -> Branch m α β.
Proof. intros Hle H i Hi. apply H. lia. Qed.

Lemma Branch_eq m α β :
  Branch m α β -> Branch m α = Branch m β.
Proof.
intros; apply incl_eq; intros γ Hγ; eapply Branch_trans.
apply Branch_sym, H. easy. apply H. easy.
Qed.

Lemma C_neq (α β : C) :
  (∃i, α i ≠ β i) <-> α ≠ β.
Proof.
split. intros [i Hi]. intros H. now subst.
intros H1. apply not_all_ex_not. intros H2; apply H1.
now extensionality i.
Qed.

Lemma del_zeros m : del m zeros = zeros.
Proof. now extensionality i. Qed.

Lemma del_ones m : del m ones = ones.
Proof. now extensionality i. Qed.

Lemma del_pre_neq m α β γ :
  del m β ≠ del m γ -> pre m α β ≠ γ.
Proof.
intros H. apply C_neq in H as [i Hi]. unfold del in Hi.
apply C_neq. exists (m + i). unfold pre. replace (m + i <? m) with false.
easy. symmetry. b_lia.
Qed.

(* Find the least shared branch of two different sequences. *)
Lemma neq_least_shared_branch α β :
  α ≠ β -> ∃m, Branch m α β /\ α m ≠ β m.
Proof.
intros H; apply C_neq in H as [i Hi].
revert Hi; revert α β; induction i; intros. now exists 0.
destruct (IHi (del 1 α) (del 1 β)) as [m [H1m H2m]]. easy.
destruct (bool_dec (α 0) (β 0)).
- exists (S m); split. intros j Hj; destruct j. easy.
  apply succ_lt_mono in Hj; now apply H1m in Hj. easy.
- now exists 0.
Qed.

(* A surjective enumeration of all branches in C using BinPos. *)
Require Import BinPos Pnat.
Section Enumerate_branches.

(* Convert prefix to positive number. *)
Fixpoint pre_encode n α :=
  match n with
  | 0 => xH
  | S m =>
    match α 0 with
    | false => xO (pre_encode m (del 1 α))
    | true => xI (pre_encode m (del 1 α))
    end
  end.

(* Ignore the last bit (xH). *)
Definition pre_size p := pred (Pos.size_nat p).
Definition pre_bit p i := if i <? pre_size p
  then Pos.testbit_nat p i else false.

(* Decode a natural number as a branch in the Cantor space. *)
Definition pre_decode (n : nat) : nat * C :=
  let p := Pos.of_nat (S n) in (pre_size p, pre_bit p).

Lemma pre_size_xO p : pre_size (xO p) = S (pre_size p).
Proof. unfold pre_size; now destruct p. Qed.

Lemma pre_size_xI p : pre_size (xI p) = S (pre_size p).
Proof. unfold pre_size; now destruct p. Qed.

Lemma ltb_S m n : (S m <? S n) = (m <? n).
Proof. intros; destruct (m <? n) eqn:E; b_lia. Qed.

Lemma pre_size_S p n :
  Pos.size_nat p = S n -> pre_size p = n.
Proof.
unfold pre_size; destruct p; simpl; intros.
1-2: now apply eq_add_S. lia.
Qed.

Lemma pre_size_encode n α :
  pre_size (pre_encode n α) = n.
Proof.
apply pre_size_S.
revert α; induction n; simpl; intros. easy.
destruct (α 0); simpl. all: apply eq_S, IHn.
Qed.

Lemma Branch_pre_bit_encode m α :
  Branch m α (pre_bit (pre_encode m α)).
Proof.
revert α; induction m; intros. easy. intros i Hi. destruct i.
- simpl; destruct (α 0); unfold pre_bit.
  now rewrite pre_size_xI. now rewrite pre_size_xO.
- apply succ_lt_mono in Hi; apply IHm with (α:=del 1 α) in Hi.
  clear IHm. unfold del in Hi at 1; simpl in Hi.
  unfold pre_bit in *; simpl. destruct (α 0); simpl.
  now rewrite pre_size_xI, ltb_S. now rewrite pre_size_xO, ltb_S.
Qed.

Lemma pre_decode_to_nat p :
  pre_decode (pred (Pos.to_nat p)) = (pre_size p, pre_bit p).
Proof.
assert(H := Pos2Nat.is_pos p). destruct (Pos.to_nat p) eqn:E. easy.
unfold pre_decode; now rewrite ?pred_succ, <-E, Pos2Nat.id.
Qed.

Theorem pre_decode_surj m α :
  ∃n, fst (pre_decode n) = m /\ Branch m α (snd (pre_decode n)).
Proof.
exists (pred (Pos.to_nat (pre_encode m α))).
rewrite pre_decode_to_nat; simpl; split.
apply pre_size_encode. apply Branch_pre_bit_encode.
Qed.

End Enumerate_branches.
