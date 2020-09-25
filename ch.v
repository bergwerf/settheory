(* A proof that the Continuum Hypothesis holds for closed sets. *)

From set_theory Require Import lib fn pair bin set d.

(* Cantor-Bendixon derivative *)
Inductive CB (X : P C) : P C -> Prop :=
  | CB_intro : CB X X
  | CB_limit : ∀Y, CB X Y -> CB X (D Y)
  | CB_isect : ∀Y : nat -> P C, (∀n, CB X (Y n)) -> CB X (⋂ Y).

(*
Induction over CB is called `transfinite' induction because it is not clear how
a direct induction (e.g. on some derivation structure) can be carried out in
such a way that K(X) is also reached. It is noteworthy that CB is always at most
countable, which follows from the fact that X ⧵ K(X) is at most countable. We
can also prove that CB is well-ordered by the proper superset relation (but this
proof relies on induction over CB). This could be a future addition in `wot.v'.
*)

(* Kernel of the Cantor-Bendixon derivative *)
(* We need a sigma type; [∀Y, CB X Y -> Y α] does not work with negation! *)
Definition K X α := ∀σ : {Y | CB X Y}, (proj1_sig σ) α.

(*
Finally we prove CH for closed sets. With closed sets we can exploit a
hierarchy of derived sets given by the Cantor-Bendixon derivatives. Open sets
are trickier because a countable open set may contain uncountably many limit
points. (Take for example all finite sequences prepended to zeros. This is
similar to the rational numbers which approach all real numbers.)
*)
Section Continuum_Hypothesis.

Variable X : P C.
Hypothesis closed_X : Closed X.

(* A set Y ⊆ C embeds C if a one-to-one function f : C -> Y exists. *)
Definition EmbedsC (Y : P C) := ∃f : C -> C, Injective f /\ ∀α, Y (f α).

(* Every infinite set X is either countable or embeds C. *)
Definition CH := Infinite X -> Countable X \/ EmbedsC X.

(* All Y ∈ CB(X) are closed. *)
Lemma CB_closed Y :
  CB X Y -> Closed Y.
Proof.
intros H; induction H. easy.
apply closed_D. now apply closed_ωisect.
Qed.

(* All Y ∈ CB(X) are included in X. *)
Lemma CB_incl Y :
  CB X Y -> Y ⊆ X.
Proof.
intros H; induction H. easy.
eapply incl_trans. now apply CB_closed. easy.
intros α Hα. eapply H0, (Hα 0).
Qed.

(* All Y ∈ CB(X) differ at most a countable number of elements from X. *)
Theorem CB_countable_complement Y :
  CB X Y -> Countable (X ⧵ Y).
Proof.
intros H; induction H.
- exists (λ _, zeros); now intros α [H1α H2α].
- erewrite diff_union. 2: apply CB_closed. apply countable_union.
  easy. apply countable_diff_D. easy. now apply CB_incl.
- rewrite diff_ωisect_eq_ωunion_diff; apply countable_ωunion; now intros.
Qed.

(* We introduce a short notation for a disjoint branch. *)
Definition CB_Disjoint (s : nat * C) Y :=
  CB X Y /\ Y ∩ Branch (fst s) (snd s) = ∅.

(*
If α ∈ X is not in the kernel, Y ∈ CB(X) exists s.t. α ∉ Y and
there is a branch of α that is entirely disjoint from Y.
*)
Lemma CB_isolated_in_disjoint_branch α :
  (X ⧵ K X) α -> ∃Y m, CB_Disjoint (m, α) Y.
Proof.
intros [H1α H2α]. apply not_all_ex_not in H2α as [[Y HY] H2α]; simpl in *;
exists Y. apply closed_complement in H2α as [n Hn].
now exists n. now apply CB_closed.
Qed.

(*
For every branch s in C as given by pre_decode, there exists a Y ∈ CB(X) such
that; if CB(X) contains a set disjoint from s, then Y is such a set.
*)
Lemma CB_choose_disjoint_at_pre_decode n :
  ∃Y, CB X Y /\
  ((∃Y', CB_Disjoint (pre_decode n) Y') -> CB_Disjoint (pre_decode n) Y).
Proof.
destruct (classic (∃Y', CB_Disjoint (pre_decode n) Y')) as [[Z [H1Z H2Z]]|HZ].
exists Z; split; easy. exists X; split. apply CB_intro.
intros H; exfalso; now apply HZ.
Qed.

(* The kernel is a Cantor-Bendixon derivative. *)
Theorem CB_K :
  CB X (K X).
Proof.
(* Obtain a sequence Y from the previous theorem using AC. We claim K = ⋂ Y. *)
destruct (choice _ CB_choose_disjoint_at_pre_decode) as [Y HY].
replace (K X) with (⋂ Y). apply CB_isect; intros; apply (proj1 (HY n)).
(* Now we must prove K = ⋂ Y. *)
symmetry; apply incl_eq.
- (* Trivial direction *)
  intros α Hα n; assert(HYn := proj1 (HY n)).
  now assert(σYn := Hα (exist _ (Y n) HYn)).
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
    easy. erewrite Branch_eq. 2: apply Branch_sym, Hn. easy. }
  apply HY in Hn' as [_ HYn]; apply eq_incl in HYn as [HYn _].
  (* We use that α ∈ Y n implies α ∈ ∅. *)
  intros Hα; apply (HYn α); split. easy.
  now apply Branch_sym.
Qed.

(* The kernel contains no isolated points. *)
Corollary CB_K_perfect :
  Perfect (K X).
Proof.
intros α Hα. assert(CB X (D (K X))) by (apply CB_limit, CB_K).
apply (Hα (exist _ _ H)).
Qed.

(* C embeds into any non-empty, perfect set. *)
Lemma nonempty_perfect_embeds_C (Y : P C) :
  Y ≠ ∅ -> Perfect Y -> EmbedsC Y.
Proof.
intros ex H; apply not_empty in ex as [α Hα].
Admitted.

(* Either X is countable or C embeds into X. *)
Theorem Closed_Continuum_Hypothesis : CH.
Proof.
destruct (classic (K X = ∅)).
- left. rewrite <-diff_empty, <-H. apply CB_countable_complement, CB_K.
- right. apply nonempty_perfect_embeds_C in H as [f [H1f H2f]].
  exists f; split. easy. intros; eapply CB_incl.
  apply CB_K. apply H2f. apply CB_K_perfect.
Qed.

End Continuum_Hypothesis.
