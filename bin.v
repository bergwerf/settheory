(* Utilities for binary sequences (the Cantor space) *)

From set_theory Require Import lib fn set.

(* Cantor space as a notation (to avoid problems with unfolding) *)
Notation "'C'" := (nat -> bool).

(* A branch in the Cantor space *)
Definition Branch m (α β : C) := ∀i, i < m -> α i = β i.

Definition const (b : bool) (i : nat) := b.
Definition zeros := const false.
Definition ones := const true.
Definition del m (α : C) i := α (m + i).
Definition shift m (α : C) i := if i <? m then false else α (i - m).
Definition pre m (α β : C) i := if i <? m then α i else β i.

Notation "'{0}'" := (Singleton zeros).
Notation "n >> α" := (shift n α) (at level 20, format "n >> α").
Notation "n << α" := (del n α) (at level 20, format "n << α").

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

Lemma Branch_del m n α β : Branch (m + n) α β -> Branch n (m<<α) (m<<β).
Proof. intros H i Hi; unfold del. apply H; lia. Qed.

Lemma Branch_eq m α β :
  Branch m α β -> Branch m α = Branch m β.
Proof.
intros; apply incl_eq; intros γ Hγ; eapply Branch_trans.
apply Branch_sym, H. easy. apply H. easy.
Qed.

Lemma Branch_S m α β :
  Branch m α β -> α m = β m -> Branch (S m) α β.
Proof.
intros Hm HS i Hi. apply Lt.le_lt_or_eq in Hi as [Hi|Hi].
apply Hm; lia. now replace i with m by lia.
Qed.

Lemma pre_m_mth m α β : pre m α β m = β m.
Proof. unfold pre; now rewrite ltb_irrefl. Qed.

Lemma pre_pre m α β γ : pre m (pre m α β) γ = pre m α γ.
Proof. extensionality i; unfold pre. now destruct (i <? m). Qed.

Lemma shift_m_mth m α : (m>>α) m = α 0.
Proof. unfold shift; now rewrite ltb_irrefl, sub_diag. Qed.

Lemma del_const b m : m<<(const b) = const b.
Proof. now extensionality i. Qed.

Lemma del_add m n α : (m + n)<<α = m<<(n<<α).
Proof. extensionality i; unfold del. now rewrite (add_comm m), add_assoc. Qed.

Lemma del_shift m α :
  m<<(m>>α) = α.
Proof.
extensionality i; unfold del, shift.
replace (m + i <? m) with false by b_lia.
now replace (m + i - m) with i by b_lia.
Qed.

(* Find the least shared branch of two different sequences. *)
Lemma find_first_split α β i :
  α i ≠ β i -> ∃m, Branch m α β /\ α m ≠ β m.
Proof.
revert α β; induction i; intros. now exists 0.
destruct (IHi (1<<α) (1<<β)) as [m [H1m H2m]]. easy.
destruct (bool_dec (α 0) (β 0)).
- exists (S m); split. intros j Hj; destruct j. easy.
  apply succ_lt_mono in Hj; now apply H1m in Hj. easy.
- now exists 0.
Qed.

(*
Properties that rely on classical logic. We could avoid using classical logic
for these properties by defining a strong apartness relation.
*)
Section Intensional_equality.

Lemma C_neq (α β : C) :
  (∃i, α i ≠ β i) <-> α ≠ β.
Proof.
split. intros [i Hi]. intros H. now subst.
intros H1. apply not_all_ex_not. intros H2; apply H1.
now extensionality i.
Qed.

Lemma del_pre_neq m α β γ :
  m<<β ≠ m<<γ -> pre m α β ≠ γ.
Proof.
intros H. apply C_neq in H as [i Hi]. unfold del in Hi.
apply C_neq. exists (m + i). unfold pre. replace (m + i <? m) with false.
easy. symmetry. b_lia.
Qed.

End Intensional_equality.

(* A surjective enumeration of all branches in C using BinPos. *)
Require Import BinPos Pnat.
Section Enumerate_branches.

(* Convert prefix to positive number. *)
Fixpoint pre_encode n α :=
  match n with
  | 0 => xH
  | S m =>
    match α 0 with
    | false => xO (pre_encode m (1<<α))
    | true => xI (pre_encode m (1<<α))
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
- apply succ_lt_mono in Hi; apply IHm with (α:=1<<α) in Hi.
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
