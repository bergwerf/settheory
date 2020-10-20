(* Basic notions from set theory *)

From set_theory Require Import lib fn pair.

Section Definitions.

Variable X : Type.

(* The power set *)
Definition P := X -> Prop.

Variable V : P.
Variable W : P.
Variable Y : nat -> P.

(* A function range. *)
Definition Rng {D} (f : D -> X) x := ∃d, f d = x.

(* The empty set. *)
Definition EmptySet (x : X) := False.

(* An infinite set *)
Definition Infinite := ∃f : nat -> X, Injective f /\ ∀n, V (f n).

(* A countable set *)
Definition Countable := ∃f : nat -> X, ∀x, V x -> ∃n, f n = x.

(* Singleton set *)
Definition Singleton (x y : X) := x = y.

(* V is a subset of W. *)
Definition Inclusion := ∀x, V x -> W x.

(* The difference of V relative to W is equal to V - W. *)
Definition Difference x := V x /\ ¬W x.

(* V is a proper superset of W. *)
Definition ProperSuperset := Inclusion /\ Difference ≠ EmptySet.

(* Binary union *)
Definition Union x := V x \/ W x.

(* Binary intersection *)
Definition Isect x := V x /\ W x.

(* Countable union *)
Definition ωUnion x := ∃n, Y n x.

(* Countable intersection *)
Definition ωIsect x := ∀n, Y n x.

End Definitions.

Arguments Rng {_ _}.
Arguments EmptySet {_}.
Arguments Infinite {_}.
Arguments Countable {_}.
Arguments Singleton {_}.
Arguments Inclusion {_}.
Arguments Difference {_}.
Arguments ProperSuperset {_}.
Arguments Union {_}.
Arguments Isect {_}.
Arguments ωUnion {_}.
Arguments ωIsect {_}.

Notation "'∅'" := (EmptySet).
Notation "V ⊆ W" := (Inclusion V W) (at level 50).
Notation "V ⊃ W" := (ProperSuperset V W) (at level 50).
Notation "V ⧵ W" := (Difference V W) (at level 40, left associativity).
Notation "V ∪ W" := (Union V W) (at level 40, left associativity).
Notation "V ∩ W" := (Isect V W) (at level 40, left associativity).
Notation "⋃ V" := (ωUnion V) (at level 30).
Notation "⋂ V" := (ωIsect V) (at level 30).

(* This is quite useful. *)
Lemma prop_ext {X} (V W : P X) :
  V = W <-> ∀x, V x <-> W x.
Proof.
split; intros. now subst.
extensionality x; now apply propositional_extensionality.
Qed.

Section Basic_lemmas.

Variable X : Type.
Variable V : P X.
Variable W : P X.
Variable U : P X.

(* Set inclusion is transitive *)
Lemma incl_trans : U ⊆ V -> V ⊆ W -> U ⊆ W.
Proof. intros HU HV x; auto. Qed.

(* Equal sets are included in each other. *)
Lemma eq_incl : V = W -> V ⊆ W /\ W ⊆ V.
Proof. intros; now subst. Qed.

(* Sets that are included in each other are equal. *)
Lemma incl_eq : V ⊆ W -> W ⊆ V -> V = W.
Proof. intros; apply prop_ext; split; auto. Qed.

(*
If V is included in U, and W removes at least as much from U as V,
then V is included in W.
*)
Lemma diff_incl :
  V ⊆ U -> U ⧵ W ⊆ U ⧵ V -> V ⊆ W.
Proof.
intros HVU H x HV. apply HVU in HV as HU.
assert(Hx := H x). eapply contra in Hx; unfold Difference in *.
apply not_and_or in Hx as [Hx|Hx]. easy. now apply NNPP.
now intros [_ HVx].
Qed.

End Basic_lemmas.

(* Re-use basic lemmas in a non-trivial way. *)
Section Other_lemmas.

Variable X : Type.
Variable V : P X.
Variable W : P X.
Variable U : P X.
Variable Y : nat -> P X.

(* A set is non-empty iff it contains an element. *)
Lemma not_empty :
  V ≠ ∅ <-> ∃x, V x.
Proof.
split.
- intros H; apply not_all_not_ex; intros H'; apply H.
  apply prop_ext; intros; split; unfold EmptySet; intros.
  now apply (H' x). easy.
- intros [x Hx] H; apply eq_incl in H as [H _].
  now apply (H x).
Qed.

(* The difference of V relative to ∅ is all of V. *)
Lemma diff_empty : V ⧵ ∅ = V.
Proof. apply incl_eq. now intros x [H _]. easy. Qed.

(* The empty set does not add any elements. *)
Lemma union_empty : V ∪ ∅ = V.
Proof. apply incl_eq. now intros x [H|H]. intros x H; now left. Qed.

(* If V is included in W, and W is empty, then V is empty. *)
Lemma incl_empty : V ⊆ W -> W = ∅ -> V = ∅.
Proof. intros HV HW; apply incl_eq. now rewrite <-HW. easy. Qed.

(* Intersection distributes over union. *)
Lemma isect_distr_union :
  (V ∪ W) ∩ U = (V ∩ U) ∪ (W ∩ U).
Proof.
apply incl_eq; intros x.
- intros [[HV|HW] HU]. now left. now right.
- intros [[HV HU]|[HW HU]]; split; try easy. now left. now right.
Qed.

(*
If V is included in W, then the intersection between
V and U is included in the intersection between W and U.
*)
Lemma incl_isect_incl : V ⊆ W -> V ∩ U ⊆ W ∩ U.
Proof. intros HV x [H1x H2x]. split; auto. Qed.

(*
Removing only shared elements is equal to
re-adding elements not removed by others.
*)
Lemma diff_ωisect_eq_ωunion_diff :
  V ⧵ ⋂ Y = ⋃ (λ n, V ⧵ Y n).
Proof.
apply incl_eq.
- intros x [H1x H2x]. apply not_all_ex_not in H2x as [n Hn]; now exists n.
- intros x [n [H1n H2n]]; split. easy. apply ex_not_not_all; now exists n.
Qed.

(*
Suppose V is included in W is included in U. Removing all elements in V from U
is equal to removing all elements in W and adding the elements not in V back.
*)
Lemma diff_union :
  V ⊆ W -> W ⊆ U -> U ⧵ V = (U ⧵ W) ∪ (W ⧵ V).
Proof.
intros HV HW; apply incl_eq; intros x.
- intros [H1x H2x]. destruct (classic (W x)). now right. now left.
- intros [[H1x H2x]|[H1x H2x]]; split; try easy.
  eapply contra. apply HV. easy. now apply HW.
Qed.

(* A union of countable sets is countable. *)
Lemma countable_union :
  Countable V -> Countable W -> Countable (V ∪ W).
Proof.
intros [v Hv] [w Hw].
pose(f c m := if c =? 0 then v m else w m).
pose(g n := let (c, m) := π_inv n in f c m).
exists g; intros x [Hx|Hx].
1: destruct (Hv x Hx) as [m Hm]; exists (π (0, m)).
2: destruct (Hw x Hx) as [m Hm]; exists (π (1, m)).
all: unfold g, f; now rewrite π_inv_π_id.
Qed.

(* A countable union of countable sets is countable. *)
Lemma countable_ωunion :
  (∀n, Countable (Y n)) -> Countable (⋃ Y).
Proof.
intros; apply choice in H as [F HY].
pose(f n := let (i, m) := π_inv n in F i m).
exists f; intros x [i Hx]. apply HY in Hx as [m Hm].
exists (π (i, m)); unfold f; now rewrite π_inv_π_id.
Qed.

End Other_lemmas.

(*
We used the choice axiom to prove countable_ωunion. There seems to be no way to
avoid this, except by changing the definition of Countable. This is possible
while preserving the use of classical logic; by using function relations that
can be effectively obtained.

Unfortunately this also means proofs that involve Countable must be within Type,
which would require induction on CB to be within Type. Hence proofs about CB can
then no longer use classical logic.
*)
Section Countable_ωunion_without_choice.

Definition CountableRel {X} (V : P X) := {F : nat -> X -> Prop |
  (∀n, ∃!x, F n x) /\ ∀x, V x -> ∃n, F n x}.

(* A countable union of countable sets is countable. *)
Lemma countable_rel_ωunion {X} (Y : nat -> P X) :
  (∀n, CountableRel (Y n)) -> CountableRel (⋃ Y).
Proof.
intros H;
pose(F n := sig1 (H n));
pose(HF n := sig2 (H n));
pose(G x y := let (n, i) := π_inv x in F n i y).
exists G; split; intros x; unfold G.
- destruct (π_inv x) as [n i]. apply (proj1 (HF n)).
- intros [n Hn]. apply (proj2 (HF n)) in Hn as [i Hi].
  exists (π ((n, i))). now rewrite π_inv_π_id.
Qed.

End Countable_ωunion_without_choice.
