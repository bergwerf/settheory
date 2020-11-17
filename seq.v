(* Sequence manipulation. *)

From set_theory Require Import lib set.

Section Preliminaries.

Lemma lt_S m n : m < S n -> m < n \/ m = n.
Proof. lia. Qed.

End Preliminaries.

Section Sequences.

Variable T : Type.
Variable dec : ∀x y : T, {x = y} + {x ≠ y}.

Definition Eqn m (α β : nat -> T) := ∀i, i < m -> α i = β i.
Definition const (x : T) (i : nat) := x.
Definition del m (α : nat -> T) i := α (m + i).
Definition shift m x (α : nat -> T) i := if i <? m then x else α (i - m).
Definition pre m (α β : nat -> T) i := if i <? m then α i else β i.
Definition set n v (α : nat -> T) i := if i =? n then v else α i.

Lemma eqn_refl m α : Eqn m α α.
Proof. easy. Qed.

Lemma eqn_sym m α β : Eqn m α β -> Eqn m β α.
Proof. intros H i Hi. symmetry. auto. Qed.

Lemma eqn_trans m α β γ : Eqn m α β -> Eqn m β γ -> Eqn m α γ.
Proof. intros H1 H2 i Hi. etransitivity. all: auto. Qed.

Lemma eqn_pre m α β : Eqn m α (pre m α β).
Proof. intros i Hi. unfold pre. now apply ltb_lt in Hi; rewrite Hi. Qed.

Lemma eqn_incl m n α : m <= n -> Eqn n α ⊆ Eqn m α.
Proof. intros Hle β H i Hi. apply H. lia. Qed.

Lemma eqn_del m n α β : Eqn (m + n) α β -> Eqn n (del m α) (del m β).
Proof. intros H i Hi; unfold del. apply H; lia. Qed.

Lemma eqn_eq m α β :
  Eqn m α β -> Eqn m α = Eqn m β.
Proof.
intros; apply incl_eq; intros γ Hγ; eapply eqn_trans.
apply eqn_sym, H. easy. apply H. easy.
Qed.

Lemma eqn_S m α β :
  Eqn m α β -> α m = β m -> Eqn (S m) α β.
Proof.
intros Hm HS i Hi. apply lt_S in Hi as [Hi|Hi].
now apply Hm. now subst.
Qed.

Lemma pre_0 α β : pre 0 α β = β.
Proof. extensionality i. now replace (i <? 0) with false by b_lia. Qed.

Lemma pre_m_mth m α β : pre m α β m = β m.
Proof. unfold pre; now rewrite ltb_irrefl. Qed.

Lemma pre_pre1 m α β γ : pre m (pre m α β) γ = pre m α γ.
Proof. extensionality i; unfold pre. now destruct (i <? m). Qed.

Lemma pre_pre2 m n α β γ :
  m < n -> pre n α (pre m β γ) = pre n α γ.
Proof.
intros; extensionality i; unfold pre.
destruct (i <? n) eqn:E. easy. now replace (i <? m) with false by b_lia.
Qed.

Lemma shift_m_mth m x α : (shift m x α) m = α 0.
Proof. unfold shift; now rewrite ltb_irrefl, sub_diag. Qed.

Lemma del_const b m : del m (const b) = const b.
Proof. now extensionality i. Qed.

Lemma del_add m n α : del (m + n) α = del m (del n α).
Proof. extensionality i; unfold del. now rewrite (add_comm m), add_assoc. Qed.

Lemma del_shift m x α :
  del m (shift m x α) = α.
Proof.
extensionality i; unfold del, shift.
replace (m + i <? m) with false by b_lia.
now replace (m + i - m) with i by b_lia.
Qed.

Lemma set_get1 n x α : set n x α n = x.
Proof. unfold set; now rewrite eqb_refl. Qed.

Lemma set_get2 n x α i : i ≠ n -> set n x α i = α i.
Proof. intros; unfold set; now replace (i =? n) with false by b_lia. Qed.

Lemma set_override n x y α : set n x (set n y α) = set n x α.
Proof. extensionality i; unfold set. now destruct (i =? n). Qed.

Lemma set_eqn m x n α : m <= n -> Eqn m α (set n x α).
Proof. intros H i Hi; unfold set. now replace (i =? n) with false by b_lia. Qed.

Lemma set_comm m n x y α :
  m ≠ n -> set m x (set n y α) = set n y (set m x α).
Proof.
intros; extensionality i; unfold set.
destruct (i =? m) eqn:H1, (i =? n) eqn:H2; try easy. b_lia.
Qed.

Lemma set_eq_pre_pre_const n x α :
  set n x α = pre (S n) (pre n α (const x)) α.
Proof.
extensionality i; unfold set, pre, shift.
destruct (i =? n) eqn:E; b_Prop.
subst; rewrite ltb_irrefl. now replace (n <? S n) with true by b_lia.
apply not_eq in E as [E|E]. replace (i <? S n) with true by b_lia.
now replace (i <? n) with true by b_lia.
now replace (i <? S n) with false by b_lia.
Qed.

(* Find the least shared eqn of two different sequences. *)
Lemma find_first_split α β i :
  α i ≠ β i -> ∃m, m <= i /\ Eqn m α β /\ α m ≠ β m.
Proof.
revert α β; induction i; intros. now exists 0.
destruct (IHi (del 1 α) (del 1 β)) as [m [H1m [H2m H3m]]]. easy.
destruct (dec (α 0) (β 0)).
- exists (S m); repeat split. lia. intros j Hj; destruct j. easy.
  apply succ_lt_mono in Hj; now apply H2m in Hj. easy.
- exists 0; repeat split. lia. all: easy.
Qed.

(*
Properties that rely on classical logic. We could avoid using classical logic
for these properties by defining a strong apartness relation.
*)
Section Intensional_equality.

Lemma seq_neq (α β : nat -> T) :
  (∃i, α i ≠ β i) <-> α ≠ β.
Proof.
split. intros [i Hi]. intros H. now subst.
intros H1. apply not_all_ex_not. intros H2; apply H1.
now extensionality i.
Qed.

Lemma del_pre_neq m α β γ :
  del m β ≠ del m γ -> pre m α β ≠ γ.
Proof.
intros H. apply seq_neq in H as [i Hi]. unfold del in Hi.
apply seq_neq. exists (m + i). unfold pre. replace (m + i <? m) with false.
easy. symmetry. b_lia.
Qed.

End Intensional_equality.

End Sequences.

Arguments Eqn {_}.
Arguments const  {_}.
Arguments del {_}.
Arguments shift {_}.
Arguments pre {_}.
Arguments set {_}.

Notation "n << α" := (del n α) (at level 20, format "n << α").
Notation "α ; n := x" := (set n x α)
  (at level 25, left associativity, format "α ; n := x").
