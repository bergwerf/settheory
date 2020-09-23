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

Definition CH X := Infinite X ->
  Countable X \/ ∃f : C -> C, Injective f /\ ∀α, X (f α).

Variable X : P C.
Hypothesis X_Closed : Closed X.

(* All Y ∈ CB(X) are closed. *)
Lemma CB_Closed Y :
  CB X Y -> Closed Y.
Proof.
intros H; induction H. easy.
apply D_Closed. now apply ωIsect_Closed.
Qed.

(* All Y ∈ CB(X) are included in X. *)
Lemma CB_incl Y :
  CB X Y -> Y ⊆ X.
Proof.
intros H; induction H. easy.
eapply incl_trans. now apply CB_Closed. easy.
intros α Hα. eapply H0, (Hα 0).
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
exists Y. apply Closed_complement in H2α as [n Hn].
now exists n. now apply CB_Closed.
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
Theorem CB_kernel :
  CB X (K X).
Proof.
(* Obtain a sequence Y from the previous theorem using AC. We claim K = ⋂ Y. *)
destruct (choice _ CB_choose_disjoint_at_pre_decode) as [Y HY].
replace (K X) with (⋂ Y). apply CB_isect; intros; apply (proj1 (HY n)).
(* Now we must prove K = ⋂ Y. *)
apply incl_eq.
- intros α Hα n; assert(HYn := proj1 (HY n)).
  now assert(σYn := Hα (exist _ (Y n) HYn)).
- apply diff_incl with (U:=X); intros α Hα.
  (* ⋂ Y is included in X. *)
  apply CB_incl with (Y:=Y 0). apply (proj1 (HY 0)). easy.
  (* Obtain a disjoint branch that contains α. *)
  assert(HXα := proj1 Hα).
  apply CB_isolated_in_disjoint_branch in Hα as [Z [m [HZ]]].
  (* Obtain a number that pre_decode maps to this branch. *)
  destruct (pre_decode_surj m α) as [n [Hm Hn]]; subst; simpl in *.
  (* Point out the Y that does not contain α. *)
  rewrite diff_ωisect_eq_ωunion_diff; exists n. split. easy.
  (* Use HY to show that Y_n is indeed disjoint from α. *)
  assert(Hn' : ∃Y', CB_Disjoint (pre_decode n) Y'). { exists Z; split.
    easy. erewrite Branch_eq. 2: apply Branch_sym, Hn. easy. }
  apply HY in Hn' as [_ HYn]; apply eq_incl in HYn as [HYn _].
  (* We use that α ∈ Y n -> α ∈ ∅. *)
  intros Hα; apply (HYn α); split. easy.
  now apply Branch_sym.
Qed.

(* The kernel is `perfect': it contains no isolated points. *)
Theorem K_perfect :
  K X ⊆ D (K X).
Proof.
Abort.

(* Either X embeds into nat, or C embeds into X. *)
Theorem Closed_Continuum_Hypothesis :
  CH X.
Proof.
Abort.

End Continuum_Hypothesis.
