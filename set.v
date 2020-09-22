(* Basic notions from set theory *)

From set_theory Require Import lib fn bin.

(* The power set *)
Definition P X := X -> Prop.

(* V is included in W. *)
Definition Incl {X} (V W : P X) := ∀x, V x -> W x.

(* V is empty. *)
Definition Empty {X} (V : P X) := ∀x, ~V x.

(* An infinite set *)
Definition Infinite {X} (V : P X) := ∃f : nat -> X, Injective f /\ ∀n, V (f n).

(* A countable set *)
Definition Countable {X} (V : P X) := ∃f : nat -> X, ∀x, V x -> ∃n, f n = x.

(* Singleton set *)
Definition singleton {X} (x y : X) := x = y.

(* Binary union *)
Definition union {X} (V W : P X) x := V x \/ W x.

(* Binary intersection *)
Definition isect {X} (V W : P X) x := V x /\ W x.

(* Countable union *)
Definition ωunion {X} (Y : nat -> P X) x := ∃n, Y n x.

(* Countable intersection *)
Definition ωisect {X} (Y : nat -> P X) x := ∀n, Y n x.

(* Exclude W from V. *)
Definition exclude {X} (V W : P X) x := V x /\ ~W x.

Notation "V ⊆ W" := (Incl V W) (at level 50).
Notation "V ∪ W" := (union V W) (at level 20, left associativity).
Notation "V ∩ W" := (isect V W) (at level 20, left associativity).
Notation "⋃ V" := (ωunion V) (at level 30).
Notation "⋂ V" := (ωisect V) (at level 30).
Notation "V ⧵ W" := (exclude V W) (at level 40).
Notation "'{0}'" := (singleton zeros).

Lemma Incl_refl {X} (V : P X) : V ⊆ V.
Proof. easy. Qed.

Lemma not_Empty {X} (V : P X) : ~Empty V -> ∃x, V x.
Proof. intros H. apply not_all_not_ex. intros H'; apply H. exact H'. Qed.

Lemma eq_set {X} (V W : P X) : W = V -> V ⊆ W /\ W ⊆ V.
Proof. intros. subst. split; apply Incl_refl. Qed.

Lemma set_eq {X} (V W : P X) :
  V ⊆ W -> W ⊆ V -> W = V.
Proof.
intros H1 H2. extensionality x.
apply propositional_extensionality; split.
apply H2. apply H1.
Qed.
