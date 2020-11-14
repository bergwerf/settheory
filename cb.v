(* The set of Cantor-Bendixon derivatives. *)

From set_theory Require Import lib fn pair set seq bin d.

(* We can prove several lemmas about CB(X) when X is a closed set. *)
Section Closed_sets.

Variable X : P C.
Hypothesis closed_X : Closed X.

(* CB(X) ⊆ P(C) *)
Inductive CB : P C -> Prop :=
  | CB_intro : CB X
  | CB_limit : ∀Y, CB Y -> CB (D Y)
  | CB_isect : ∀Y : nat -> P C, (∀n, CB (Y n)) -> CB (⋂ Y).

(*
Induction over CB is called `transfinite' induction because it is not clear how
a direct induction (e.g. on some derivation structure) can be carried out in
such a way that K(X) is also reached. It is noteworthy that CB is always at most
countable, which follows from the fact that X ⧵ K(X) is at most countable.
*)

(* The kernel is the intersection of all Cantor-Bendixon derivatives. *)
Definition K α := ∀Y, CB Y -> Y α.

(* All Y ∈ CB(X) are closed. *)
Theorem CB_closed Y :
  CB Y -> Closed Y.
Proof.
intros H; induction H. easy.
apply closed_D. now apply closed_ωisect.
Qed.

(* All Y ∈ CB(X) are included in X. *)
Theorem CB_incl Y :
  CB Y -> Y ⊆ X.
Proof.
intros H; induction H. easy.
eapply incl_trans. now apply CB_closed. easy.
intros α Hα. eapply H0, (Hα 0).
Qed.

(* All Y ∈ CB(X) differ at most a countable number of elements from X. *)
Theorem CB_countable_diff Y :
  CB Y -> Countable (X ⧵ Y).
Proof.
intros H; induction H.
- exists (λ _, zeros); now intros α [H1α H2α].
- erewrite diff_union. 2: now apply CB_closed. apply countable_union.
  easy. apply countable_diff_D. now apply CB_incl.
- rewrite diff_ωisect_eq_ωunion_diff; apply countable_ωunion; now intros.
Qed.

(* We introduce a short notation for a disjoint branch. *)
Definition CB_Disjoint (s : nat * C) Y :=
  CB Y /\ Y ∩ Eqn (fst s) (snd s) = ∅.

(*
If α ∈ X is not in the kernel, Y ∈ CB(X) exists s.t. α ∉ Y and
there is a branch of α that is entirely disjoint from Y.
*)
Lemma CB_isolated_in_disjoint_branch α :
  (X ⧵ K) α -> ∃Y m, CB_Disjoint (m, α) Y.
Proof.
intros [H1α H2α].
apply not_all_ex_not in H2α as [Y HY]; exists Y.
apply imply_to_and in HY as [H1Y H2Y].
apply closed_complement in H2Y as [n Hn].
now exists n. now apply CB_closed.
Qed.

(*
For every branch s in C as given by pre_decode, there exists a Y ∈ CB(X) such
that; if CB(X) contains a set disjoint from s, then Y is such a set.
*)
Lemma CB_choose_disjoint_at_pre_decode n : ∃Y, CB Y /\
  ((∃Y', CB_Disjoint (pre_decode n) Y') -> CB_Disjoint (pre_decode n) Y).
Proof.
destruct (classic (∃Y', CB_Disjoint (pre_decode n) Y')) as [[Z [H1Z H2Z]]|HZ].
exists Z; split; easy. exists X; split. apply CB_intro.
intros H; exfalso; now apply HZ.
Qed.

(* The kernel is a Cantor-Bendixon derivative. *)
Theorem CB_K :
  CB K.
Proof.
(* Obtain a sequence Y from the previous theorem using AC. We claim K = ⋂ Y. *)
(* We could use unique_choice by exploiting a well-ordening of CB. *)
destruct (choice _ CB_choose_disjoint_at_pre_decode) as [Y HY].
replace K with (⋂ Y). apply CB_isect; intros; apply (proj1 (HY n)).
(* Now we must prove K = ⋂ Y. *)
symmetry; apply incl_eq.
- (* Trivial direction *)
  intros α Hα n; apply Hα. apply (proj1 (HY n)).
- (* Hard direction; exploit pre_decode_surj and HY. *)
  apply diff_incl with (U:=X); intros α Hα.
  (* ⋂ Y is included in X. *)
  apply CB_incl with (Y:=Y 0). apply (proj1 (HY 0)). easy.
  (* Obtain a disjoint branch that contains α. *)
  assert(HXα := proj1 Hα).
  apply CB_isolated_in_disjoint_branch in Hα as [Z [m [HZ]]].
  (* Obtain a number that is mapped to this branch by pre_decode. *)
  destruct (pre_decode_surj m α) as [n [Hm Hn]]; subst; simpl in *.
  (* Point out the Y that does not contain α. *)
  rewrite diff_ωisect_eq_ωunion_diff; exists n. split. easy.
  (* Use HY to show that Y_n is indeed disjoint from α. *)
  assert(Hn' : ∃Y', CB_Disjoint (pre_decode n) Y'). { exists Z; split.
    easy. erewrite eqn_eq. 2: apply eqn_sym, Hn. easy. }
  apply HY in Hn' as [_ HYn]; apply eq_incl in HYn as [HYn _].
  (* We use that α ∈ Y n implies α ∈ ∅. *)
  intros Hα; apply (HYn α); split. easy.
  now apply eqn_sym.
Qed.

(* The kernel contains no isolated points. *)
Corollary CB_K_perfect :
  Perfect K.
Proof.
intros α Hα; apply Hα.
apply CB_limit, CB_K.
Qed.

End Closed_sets.
