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
intros H. induction H. easy.
apply D_Closed. now apply ωIsect_Closed.
Qed.

(* We introduce a short notation for a disjoint branch. *)
Definition CB_disjoint Y α m := CB X Y /\ Y ∩ Branch m α = ∅.

(*
If α ∈ X is not in the kernel, Y ∈ CB(X) exists s.t. α ∉ Y and
there is a branch of α that is entirely disjoint from Y.
*)
Theorem CB_isolated_in_disjoint_branch α :
  (X ⧵ K X) α -> ∃Y m, ¬Y α /\ CB_disjoint Y α m.
Proof.
intros [H1α H2α]. apply not_all_ex_not in H2α as [[Y HY] H2α]; simpl in *.
exists Y. assert(Hα := H2α). apply Closed_complement in H2α as [m Hm].
exists m; easy. now apply CB_Closed.
Qed.

(*
Choose a sequence Y_n from CB(X) that contains a Y_n that is disjoint with every
branch of the Cantor space, if one exists (otherwise we pick X).
*)
Theorem CB_disjoint_at_every_possible_branch :
  ∃Y, (∀n : nat, CB X (Y n)) /\
  ∀α m, (∃Z, CB_disjoint Z α m) -> ∃n, CB_disjoint (Y n) α m.
Proof.
Abort.

(* The kernel is a Cantor-Bendixon derivative. *)
Theorem CB_kernel :
  CB X (K X).
Proof.
Abort.

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
