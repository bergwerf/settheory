(* The `derived set' containing limit points of a set X : P C *)

From set_theory Require Import lib fn bin set.

(* All non-isolated points: distinct points exist within any branch of α. *)
Definition D (X : P C) α := ∀m, ∃β, α ≠ β /\ X β /\ Branch m α β.

(* Limit of any set transformer. *)
Definition Lim (F : P C -> P C) X := ⋂ (λ n, (F ↑ n) X).

(* A closed set contains its own limit points. *)
Definition Closed X := D X ⊆ X.

(* A countable union of closed sets is closed. *)
Lemma ωIsect_Closed X :
  (∀n, Closed (X n)) -> Closed (⋂ X).
Proof.
intros H α Hα n. apply H. intros m.
destruct (Hα m) as [β Hβ]; now exists β.
Qed.

(* The derived set is closed. *)
Theorem D_Closed X :
  Closed (D X).
Proof.
(* First find γ ∈ D(X) in the desired branch of α. *)
intros α Hα m. destruct (Hα m) as [γ [Hαγ [Hγ Hi]]].
(* Find  where γ splits from α, and find β ∈ X in this branch. *)
apply C_neq in Hαγ as [n Hn]. destruct (Hγ (S n)) as [β [Hγβ [Hβ Hj]]].
(* Now β is apart from α but still in the desired branch. *)
exists β; repeat split. apply C_neq; exists n. rewrite <-Hj. easy. lia. easy.
assert(m <= n). { apply not_gt. intros H'. now apply Hi in H'. }
eapply Branch_trans. apply Hi. eapply Branch_restrict. 2: apply Hj. auto.
Qed.

(* An element in the complement of a closed set has a disjoint branch. *)
Theorem Closed_complement X α :
  Closed X -> ¬X α -> ∃m, X ∩ Branch m α = ∅.
Proof.
intros HX Hα. apply not_all_not_ex; intros Hn. apply Hα, HX.
intros m. destruct (not_empty _ _ (Hn m)) as [β [H1β H2β]]; exists β.
repeat split. intros H; now subst. all: easy.
Qed.

(* Shift α ∈ C to the m-th branch of zeros (prefix 0^m ++ 1). *)
Definition shift_branch m α := shift m (pre 1 ones (shift 1 α)).

(* Copy X ⊆ C at the given branch of zeros. *)
Definition Shift m X α := ∃β, X β /\ α = shift_branch m β.

(* Copy X ⊆ C at every branch of zeros. *)
Definition Shifts X := ⋃ λ m, Shift m X.

(* Shifting and removing isolated points commute. *)
Lemma D_Shift_comm m :
  D ∘ (Shift m) = (Shift m) ∘ D.
Proof.
Abort.

(* α ∈ X iff shift_branch m α ∈ Shifts X. *)
Lemma shift_branch_Shifts (X : P C) m α :
  (Shifts X) (shift_branch m α) = X α.
Proof.
Abort.

(*
For every natural number n, there exists a set X ⊆ C such that {0} is left
after n applications of D (n times removing isolated points).
*)
Theorem D_n_ex n :
  ∃X, (D ↑ n) X = {0}.
Proof.
induction n. now exists {0}.
destruct IHn as [X HX]; exists (Shifts X).
apply incl_eq; unfold Singleton; intros α Hα.
- (* zeros is a limit point. *)
  subst; intros m. exists (shift_branch m zeros); repeat split.
  + apply C_neq; exists m. unfold shift_branch, shift, pre.
    replace (m <? m) with false by b_lia;
    replace (m - m <? 1) with true by b_lia.
    now unfold zeros, ones.
  + admit.
  + intros i Hi. unfold shift_branch, shift.
    now replace (i <? m) with true by b_lia.
- (* any other point is not a limit point. *)
  apply NNPP; intros H; apply C_neq in H as [i Hi].
  unfold zeros in Hi; apply not_eq_sym, not_false_iff_true in Hi.
  simpl in Hα; destruct (Hα (S i)) as [β [H1β [H2β H3β]]].
  (* β cannot exist because all branches of zeros are empty. *)
Abort.

(* Take the limit of D once. *)
Theorem Lim_D_ex :
  ∃X, Lim D X = {0}.
Proof.
Abort.

(*
This one is more difficult to understand. Note that the operation we take the
limit of, L D, means ``limit of applying D to the input set''. If we call the
first limit ω, then the outer limit is ω times ω which is sometimes denoted as
ω squared. It helps to expand the first few terms:

Lim (Lim D) X = (⋂ (D ↑ n) X) ∩ (⋂ (D ↑ n) (⋂ (D ↑ n) X)) ∩ ...
*)
Theorem Lim_Lim_D_ex :
  ∃X, Lim (Lim D) X = {0}.
Proof.
Abort.

(*
Note that Lim (Lim D) = (Lim ↑ 2) D. As with hyper-operations, we can keep
iterating this principle over and over again. I believe this corresponds to
ω^ω^ω^... I do not know if this theorem actually holds, but I suspect it does.
*)
Theorem Lim_n_D_ex n :
  ∃X, (Lim ↑ n) D X = {0}.
Proof.
Abort.
