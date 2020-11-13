(* Introducing the axiomatic approach to set theory. *)

Require Import lib bin.

Module Basic_language_of_set_theory.

(* Set value in a sequenc. *)
Definition set {T} n v (α : nat -> T) i := if i =? n then v else α i.

(* Formulae in the basic language of set-theory. *)
Inductive formula :=
  | IsEqual (x y : nat)
  | ElementOf (x y : nat)
  | Negation (φ : formula)
  | Conjunction (φ ϕ : formula)
  | Exists (x : nat) (φ : formula).

Notation "i == j" := (IsEqual i j) (at level 50).
Notation "i ∈ j" := (ElementOf i j) (at level 50).
Notation "¬` φ" := (Negation φ) (at level 60, φ at next level, format "¬` φ").
Notation "i != j" := (¬`(i = j)) (at level 50).
Notation "i ∉ j" := (¬`(i ∈ j)) (at level 50).
Notation "φ ∧` ϕ" := (Conjunction φ ϕ) (at level 70).
Notation "φ ∨` ϕ" := (¬`(¬`ϕ ∧` ¬`φ)) (at level 70).
Notation "φ ==> ϕ" := (¬`(φ ∧` ¬`ϕ)) (at level 80).
Notation "φ <=> ϕ" := ((φ ==> ϕ) ∧` (ϕ ==> φ)) (at level 80).
Notation "∃` x [ φ ]" := (Exists x φ) (format "∃` x [ φ ]").
Notation "∀` x [ φ ]" := (¬`∃`x[¬`φ]) (format "∀` x [ φ ]").

(* Universal quantification of n variables. *)
Fixpoint closure n φ :=
  match n with
  | 0 => φ
  | S m => closure m (∀`m[φ])
  end.

(* Map formula variables. *)
Definition subst (i j v : nat) := if v =? i then j else v.
Fixpoint mapf f φ :=
  match φ with
  | i == j => f i == f j
  | i ∈ j => f i ∈ f j
  | ¬`ϕ => ¬`mapf f ϕ
  | ϕ ∧` ψ => mapf f ϕ ∧` mapf f ψ
  | ∃`x[ϕ] => ∃`x[mapf f ϕ]
  end.

(* Compute number of free variables. *)
Definition fv (Γ : C) i := if Γ i then 0 else S i.
Fixpoint max_fv (Γ : nat -> bool) φ :=
  match φ with
  | i == j => max (fv Γ i) (fv Γ j)
  | i ∈ j => max (fv Γ i) (fv Γ j)
  | ¬`ϕ => max_fv Γ ϕ
  | ϕ ∧` ψ => max (max_fv Γ ϕ) (max_fv Γ ψ)
  | ∃`x[ϕ] => max_fv (set x true Γ) ϕ
  end.

Definition FV φ := max_fv (const false) φ.
Definition fresh φ := FV φ.

Notation "∀^( n )[ φ ]" := (closure n φ) (format "∀^( n )[ φ ]").
Notation "φ '\[' i := j ]" := (mapf (subst i j) φ)
  (at level 55, format "φ '\[' i  :=  j ]").

(* Unique existential quantifiction of x for φ = φ(x). *)
Definition Exists_unique x φ :=
  let z := fresh φ in
  ∃`x[φ ∧` ∀`z[φ\[x := z] ==> x == z]].

Notation "∃! x [ φ ]" := (Exists_unique x φ) (format "∃! x [ φ ]").

End Basic_language_of_set_theory.
Import Basic_language_of_set_theory.

Section Zermelo_Fraenkel_axioms.

(* 1. Standard model theoretic conventions. *)

Definition Not_empty := ∃`0[0 == 0].
Definition Eq_refl := ∀`0[0 == 0].
Definition Eq_sym := ∀`0[∀`1[0 == 1 ==> 1 == 0]].
Definition Eq_trans := ∀`0[∀`1[∀`2[0 == 1 ∧` 1 == 2 ==> 0 == 2]]].
Definition Eq_equiv := Eq_refl ∧` Eq_sym ∧` Eq_trans.

(* 2. Frege's comprehension scheme. *)

Definition Schema_of_comprehension φ :=
  let n := FV φ - 1 in
  let x := n in
  let z := S x in
  ∀^(n)[∃`z[∀`x[x ∈ z <=> φ]]].

(* 3. Zermelo's axioms. *)

Definition Axiom_of_extensionality :=
  ∀`0[∀`1[∀`2[2 ∈ 0 <=> 2 ∈ 1] ==> 0 == 1]].

Definition Axiom_of_pairing :=
  ∀`0[∀`1[∃`2[∀`3[3 ∈ 2 <=> 3 == 0 ∨` 3 == 1]]]].

Definition Axiom_of_union :=
  ∀`0[∃`1[∀`2[2 ∈ 1 <=> ∃`3[2 ∈ 3 ∧` 3 ∈ 0]]]].

Definition Axiom_of_powersets :=
  ∀`0[∃`1[∀`2[2 ∈ 1 <=> ∀`3[3 ∈ 2 ==> 3 ∈ 0]]]].

  (* Axiom of infinity: ∃I[∅ ∈ I ∧ ∀n ∈ I[{n, {n}} ∈ I]]. *)

Definition Schema_of_regularity φ :=
  let n := FV φ - 1 in
  let x := n in
  let y := S x in
  ∀^(n)[∃`x[φ] ==> ∃`x[φ ∧` ∀`y[y ∈ x ==> ¬`φ\[x := y]]]].

Definition Schema_of_specification φ :=
  let n := FV φ - 1 in
  let x := n in
  let a := S x in
  let b := S a in
  ∀^(n)[∀`a[∃`b[∀`x[x ∈ b <=> x ∈ a ∧` φ]]]].

(* Fraenkels missing schema of replacement. *)
Definition Schema_of_replacement φ :=
  let n := FV φ - 2 in
  let x := n in
  let y := S x in
  let a := S y in
  let b := S a in
  ∀^(n)[∀`a[
    ∀`x[x ∈ a ==> ∃!y[φ]] ==>
    ∃`b[∀`x[x ∈ a ==> ∃`y[y ∈ b ∧` φ]]]
  ]].

End Zermelo_Fraenkel_axioms.

Module Model_definition.

(*
A set-theoretic model can be specified by giving a universe type,
an equality predicate, and an inclusion predicate.
*)
Definition model U : Type := (U -> U -> Prop) * (U -> U -> Prop).

Section Tarski_truth.

Variable U : Type.
Variable A : model U.

(* Evaluate relation given two optionally bound values. *)
Definition holds (R : U -> U -> Prop) x y :=
  match x, y with
  | Some u, Some v => R u v
  | _, _ => False
  end.

(* Tarski-truth definition. *)
Fixpoint models (Γ : nat -> option U) φ : Prop :=
  match φ with
  | i == j => holds (fst A) (Γ i) (Γ j)
  | i ∈ j => holds (snd A) (Γ i) (Γ j)
  | ¬`ϕ => ¬models Γ ϕ
  | ϕ ∧` ψ => models Γ ϕ /\ models Γ ψ
  | ∃`x[ϕ] => ∃u, models (set x (Some u) Γ) ϕ
  end.

Definition empty_context (i : nat) : option U := None.

End Tarski_truth.

Arguments models {_}.

Notation "A |= φ [ Γ ]" := (models A φ Γ) (at level 100).
Notation "A |= φ" := (A |= φ [ empty_context ]) (at level 100).

End Model_definition.
Import Model_definition.
