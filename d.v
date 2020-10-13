(* The `derived set' containing limit points of a set X : P C *)

From set_theory Require Import lib fn bin set.

(* All non-isolated points: distinct points exist within any branch of α. *)
Definition D (X : P C) α := ∀m, ∃β, α ≠ β /\ X β /\ Branch m α β.

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
intros α Hα m. destruct (Hα m) as [γ [Hαγ [Hγ Hi]]].
(* Find  where γ splits from α, and find β ∈ X in this branch. *)
apply C_neq in Hαγ as [n Hn]. destruct (Hγ (S n)) as [β [Hγβ [Hβ Hj]]].
(* Now β is apart from α but still in the desired branch. *)
exists β; repeat split. apply C_neq; exists n. rewrite <-Hj. easy. lia. easy.
assert(m <= n). { apply not_gt. intros H'. now apply Hi in H'. }
eapply Branch_trans. apply Hi. eapply Branch_restrict. 2: apply Hj. auto.
Qed.

(* A countable union of closed sets is closed. *)
Theorem closed_ωisect X :
  (∀n, Closed (X n)) -> Closed (⋂ X).
Proof.
intros H α Hα n. apply H. intros m.
destruct (Hα m) as [β Hβ]; now exists β.
Qed.

(* An element in the complement of a closed set has a disjoint branch. *)
Theorem closed_complement X α :
  Closed X -> ¬X α -> ∃m, X ∩ Branch m α = ∅.
Proof.
intros HX Hα. apply not_all_not_ex; intros Hn. apply Hα, HX.
intros m. destruct (not_empty _ _ (Hn m)) as [β [H1β H2β]]; exists β.
repeat split. intros H; now subst. all: easy.
Qed.

(* The derived set removes a countable number of isolated points. *)
Theorem countable_diff_D X :
  Countable (X ⧵ D X).
Proof.
(* The easiest approach is to `choose' a point in X under every branch. *)
pose(P s β := X β /\ Branch (fst s) (snd s) β).
assert(∀s, ∃α, (∃β, P s β) -> P s α). {
  intros. destruct (classic (∃β, P s β)) as [[β Hβ]|Hβ].
  now exists β. now exists zeros. }
(* If we choose α ∈ X at every branch, we also reach all isolated points. *)
destruct (choice _ H) as [f Hf]. exists (λ n, f (pre_decode n)).
(* Find m such that α is the only element of Branch m α. *)
intros α [H1α H2α]. apply not_all_ex_not in H2α as [m Hm].
destruct (pre_decode_surj m α) as [n [H1n H2n]]; exists n.
(* This implies P for the image of f. *)
assert(Hfn : ∃β, P (pre_decode n) β). { exists α; split. easy.
  rewrite H1n. apply Branch_sym, H2n. }
apply Hf in Hfn as [H3n H4n]; rewrite H1n in H4n.
(* If f (pre_decode n) ≠ α, then Hm gives a contradiction. *)
apply NNPP; intros H5n; apply Hm. exists (f (pre_decode n)); repeat split.
auto. easy. eapply Branch_trans. apply H2n. easy.
Qed.

(* countable_diff_D can be proved without choice, with some extra trouble. *)
Theorem countable_diff_D_again X :
  Countable (X ⧵ D X).
Proof.
(* Under every branch we follow the least element of X, or default to zero. *)
pose(Stick m α i b :=
  (Branch m α ∩ X = ∅ /\ b = false) \/
  (Branch m α ∩ X ≠ ∅ /\ ∃β, MinBranch (Branch m α) (S i) β /\ b = β i)).
pose(F m α i b := (i < m /\ b = α i) \/ (¬(i < m) /\ Stick m α i b)).
pose(G n := let (m, α) := pre_decode n in F m α).
(* Prove that G is a function relation. *)
assert(G_func : ∀p, ∃!b, G (fst p) (snd p) b). { intros [n i]; simpl.
  unfold G; destruct (pre_decode n) as [m α]; unfold F.
  revert i; apply fn_rel_lem; intros i _. apply fn_rel_fn.
  revert i; apply fn_rel_lem; intros i Hi. apply fn_rel_const.
  (* Obtain the smallest branch at depth S i. *)
  admit. }
(* Now we can turn G into a function. *)
apply unique_choice in G_func as [g Hg]; exists (λ n i, g (n, i)).
(* Find m such that α is the only element of Branch m α. *)
intros α [H1α H2α]; apply not_all_ex_not in H2α as [m Hm].
destruct (pre_decode_surj m α) as [n [H1n H2n]]; exists n.
(* Show that g must follow α since it is the only element in this branch. *)
Abort.

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
  apply NNPP; intros H; apply C_neq in H as [i Hi].
  unfold zeros in Hi; apply not_eq_sym, not_false_iff_true in Hi.
  (* Find β in (D ↑ n) (Shifts X) s.t. Branch (S i) α β. *)
  simpl in Hα; destruct (Hα (S i)) as [β [H1β [H2β H3β]]].
  (* Note that for some m : nat, β = shift_branch m zeros. *)
  (* We cannot find a γ ≠ β in the branch where β splits from zeros. *)
  admit.
- (* zeros is a limit point. *)
  subst; intros m. exists (shift_branch m zeros); repeat split.
  + apply C_neq; exists m. unfold shift_branch, shift, pre.
    rewrite ltb_irrefl; replace (m - m <? 1) with true by b_lia.
    now unfold zeros, ones.
  + (* [shift_branch m zeros] is in (D ↑ n) (Shifts X). *)
    admit.
  + intros i Hi. unfold shift_branch, shift.
    now replace (i <? m) with true by b_lia.
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
