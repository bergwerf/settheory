(* Basic notions from set theory *)

From set_theory Require Import lib fn bin.

Section Definitions.

Variable X : Type.

(* The power set *)
Definition P := X -> Prop.

Variable V : P.
Variable W : P.

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

(* Difference between V and W. *)
Definition Difference x := V x /\ ¬W x.

(* V is a proper superset of W. *)
Definition ProperSuperset := Inclusion /\ Difference ≠ EmptySet.

(* Binary union *)
Definition Union x := V x \/ W x.

(* Binary intersection *)
Definition Isect x := V x /\ W x.

(* Countable union *)
Definition ωUnion (Y : nat -> P) x := ∃n, Y n x.

(* Countable intersection *)
Definition ωIsect (Y : nat -> P) x := ∀n, Y n x.

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
Notation "'{0}'" := (Singleton zeros).
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

Section Lemmas.

Variable X : Type.
Variable V : P X.
Variable W : P X.
Variable U : P X.

Lemma incl_refl : V ⊆ V.
Proof. easy. Qed.

(* Equal sets are included in each other. *)
Lemma eq_incl : W = V -> V ⊆ W /\ W ⊆ V.
Proof. intros; subst. split; apply incl_refl. Qed.

(* Sets that are included in each other are equal. *)
Lemma incl_eq : V ⊆ W -> W ⊆ V -> W = V.
Proof. intros; apply prop_ext; split; auto. Qed.

(* A non-empty set contains an element. *)
Lemma not_empty :
  V ≠ ∅ -> ∃x, V x.
Proof.
intros. apply not_all_not_ex; intros H'; apply H.
apply prop_ext; intros; split; unfold EmptySet; intros.
now apply (H' x). easy.
Qed.

(*
If V and W are both included in the same set U, and W removes at least as much
from U as V, then V is included in W.
*)
Lemma diff_incl :
  V ⊆ U -> W ⊆ U -> U ⧵ W ⊆ U ⧵ V -> V ⊆ W.
Proof.
intros HV HW H α Hα. apply HV in Hα as HU.
apply contra with (x:=α) in H; unfold Difference in *.
apply not_and_or in H as [H|H]. easy. now apply NNPP.
now intros [_ HVα].
Qed.

End Lemmas.
