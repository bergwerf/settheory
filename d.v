(* The `derived set' with limit points of a set X : P C. *)

From set_theory Require Import lib fn set seq bin.

(* All non-isolated points: distinct points exist within any branch of α. *)
Definition D (X : P C) α := ∀m, ∃β, α ≠ β /\ (Branch m α ∩ X) β.

(* Limit of any set transformer. *)
Definition Lim (F : P C -> P C) X := ⋂ (λ n, (F ↑ n) X).

(* A closed set contains its own limit points. *)
Definition Closed X := D X ⊆ X.

(* A perfect set contains exactly its own limit points. *)
Definition Perfect X := X ⊆ D X.

(* The derived set is closed. *)
Theorem closed_D X :
  Closed (D X).
Proof.
(* First find γ ∈ D(X) in the desired branch of α. *)
intros α Hα m. destruct (Hα m) as [γ [Hαγ [Hm Hγ]]].
(* Find  where γ splits from α, and find β ∈ X in this branch. *)
apply seq_neq in Hαγ as [n Hn]. destruct (Hγ (S n)) as [β [Hγβ [H1β H2β]]].
(* Now β is apart from α but still in the desired branch. *)
exists β; repeat split. apply seq_neq; exists n. rewrite <-H1β. easy. lia.
assert(m <= n). { apply not_gt. intros H'. now apply Hm in H'. }
eapply branch_trans. apply Hm. eapply branch_incl. 2: apply H1β. auto. easy.
Qed.

(* A countable union of closed sets is closed. *)
Theorem closed_ωisect X :
  (∀n, Closed (X n)) -> Closed (⋂ X).
Proof.
intros H α Hα n. apply H. intros m.
destruct (Hα m) as [β [H1β [H2β H3β]]]; now exists β.
Qed.

(* An element in the complement of a closed set has a disjoint branch. *)
Theorem closed_complement X α :
  Closed X -> ¬X α -> ∃m, X ∩ Branch m α = ∅.
Proof.
intros HX Hα. apply not_all_not_ex; intros Hn. apply Hα, HX.
intros m; assert(Hm := Hn m). apply not_empty in Hm as [β [H1β H2β]]; exists β.
repeat split. intros H; now subst. all: easy.
Qed.

(* The derived set removes a countable number of isolated points. *)
Theorem countable_diff_D X :
  Countable (X ⧵ D X).
Proof.
(* Under every branch we follow the least element of X, or default to zero. *)
(* We could also use the choice axiom for a shorter proof. *)
pose(F1 m α i b :=
  (Branch m α ∩ X = ∅ /\ b = false) \/
  (Branch m α ∩ X ≠ ∅ /\ ∃β, MinBranch (Branch m α ∩ X) (S i) β /\ b = β i)).
pose(F2 m α i b := (i < m /\ b = α i) \/ (¬(i < m) /\ F1 m α i b)).
pose(F3 n := let (m, α) := pre_decode n in F2 m α).
(* Prove that F3 is a function relation. *)
assert(F3_func : ∀p, ∃!b, F3 (fst p) (snd p) b). {
  intros [n i]; simpl.
  unfold F3; destruct (pre_decode n) as [m α]; unfold F2.
  revert i; apply fn_rel_lem; intros i _. apply fn_rel_fn.
  revert i; apply fn_rel_lem; intros i Hi. apply fn_rel_const.
  (* Obtain the smallest branch at depth S i. *)
  destruct (min_branch_ex (Branch m α ∩ X) (S i)) as [β Hβ]. easy.
  exists (β i); split. now exists β. intros b [γ [Hγ R]]; subst b.
  eapply min_branch_unique. apply Hβ. apply Hγ. lia. }
(* We now turn F3 into a function. *)
apply unique_choice in F3_func as [f3 Hf3]; exists (λ n i, f3 (n, i)).
(* Find m such that α is the only element in Branch m α ∩ X. *)
intros α [H1α H2α]; apply not_all_ex_not in H2α as [m Hm].
destruct (pre_decode_surj m α) as [n [H1n H2n]]; exists n.
assert(Branch m α ∩ X = Singleton α). {
  apply incl_eq; unfold Singleton; intros β Hβ.
  apply NNPP; intros H. apply Hm; now exists β.
  subst β; split. apply branch_refl. easy. }
(* Now f3 follows α. *)
extensionality i; assert(Hi := Hf3 (n, i)); remember (f3 (n, i)) as b.
simpl in Hi; unfold F3 in Hi; destruct (pre_decode n) as [k β]; unfold F2 in Hi.
simpl in H1n, H2n; subst k. destruct Hi as [[H1i H2i]|[_ Hi]].
- (* b coincides with the pre_decode branch. *)
  rewrite H2i; symmetry. now apply H2n.
- (* b must stick to α. *)
  apply branch_sym in H2n.
  unfold F1 in Hi; destruct Hi as [[Hi _]|[_ [γ [Hγ R]]]].
  exfalso; apply eq_incl in Hi as [Hi _]; now apply (Hi α).
  rewrite R. erewrite branch_eq, H in Hγ; try easy.
  destruct Hγ as [Hγ _]. apply not_empty in Hγ as [δ [H1δ H2δ]].
  rewrite H2δ; apply H1δ. lia.
Qed.

(* Now we start building examples of derived sets. *)
Section Examples.

(* Shift α ∈ C to the m-th branch of zeros (prefix 0^m ++ 1). *)
Definition shift_branch m α := m>>(pre 1 ones (1>>α)).

(* Copy X ⊆ C at the given branch of zeros. *)
Definition Shift m X α := ∃β, X β /\ α = shift_branch m β.

(* Copy X ⊆ C at every branch of zeros. *)
Definition Shifts X := ⋃ λ m, Shift m X.

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
- (* α ≠ zeros is not a limit point. *)
  apply NNPP; intros H; apply seq_neq in H as [i Hi].
  unfold zeros in Hi; apply not_eq_sym, not_false_iff_true in Hi.
  (* Find β in (D ↑ n) (Shifts X) s.t. Branch (S i) α β. *)
  simpl in Hα; destruct (Hα (S i)) as [β [H1β [H2β H3β]]].
  (* Note that for some m : nat, β = shift_branch m zeros. *)
  (* We cannot find a γ ≠ β in the branch where β splits from zeros. *)
  admit.
- (* zeros is a limit point. *)
  subst; intros m. exists (shift_branch m zeros); repeat split.
  + apply seq_neq; exists m. unfold shift_branch, shift, pre.
    rewrite ltb_irrefl; replace (m - m <? 1) with true by b_lia.
    now unfold zeros, ones.
  + intros i Hi. unfold shift_branch, shift.
    now replace (i <? m) with true by b_lia.
  + (* [shift_branch m zeros] is in (D ↑ n) (Shifts X). *)
    admit.
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

End Examples.
