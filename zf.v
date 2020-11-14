(* Introducing the axiomatic approach to set theory. *)

Require Import lib seq.

Module Basic_language_of_set_theory.

(* Formulae in the basic language of set-theory. *)
Inductive formula :=
  | IsEqual (x y : nat)
  | ElementOf (x y : nat)
  | Negation (φ : formula)
  | Conjunction (φ ϕ : formula)
  | Exists (x : nat) (φ : formula).

Notation "i == j" := (IsEqual i j) (at level 40).
Notation "i ∈ j" := (ElementOf i j) (at level 40).
Notation "¬` φ" := (Negation φ) (at level 50, φ at next level, format "¬` φ").
Notation "i != j" := (¬`(i = j)) (at level 40).
Notation "i ∉ j" := (¬`(i ∈ j)) (at level 40).
Notation "φ ∧` ϕ" := (Conjunction φ ϕ) (at level 60).
Notation "φ ∨` ϕ" := (¬`(¬`ϕ ∧` ¬`φ)) (at level 60).
Notation "φ ==> ϕ" := (¬`(φ ∧` ¬`ϕ)) (at level 70).
Notation "φ <=> ϕ" := ((φ ==> ϕ) ∧` (ϕ ==> φ)) (at level 70).
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

(* Compute if a variable occurs freely. *)
Fixpoint free y φ : bool :=
  match φ with
  | i == j => (i =? y) || (j =? y)
  | i ∈ j => (i =? y) || (j =? y)
  | ¬`ϕ => free y ϕ
  | ϕ ∧` ψ => free y ϕ || free y ψ
  | ∃`x[ϕ] => if x =? y then false else free y ϕ
  end.

(* Compute upper bound on free variables. *)
Definition fv (Γ : nat -> bool) i := if Γ i then 0 else S i.
Fixpoint max_fv (Γ : nat -> bool) φ :=
  match φ with
  | i == j => max (fv Γ i) (fv Γ j)
  | i ∈ j => max (fv Γ i) (fv Γ j)
  | ¬`ϕ => max_fv Γ ϕ
  | ϕ ∧` ψ => max (max_fv Γ ϕ) (max_fv Γ ψ)
  | ∃`x[ϕ] => max_fv (Γ;x:=true) ϕ
  end.

Definition FV φ := max_fv (const false) φ.
Definition fresh φ := FV φ.

Notation "∀^( n )[ φ ]" := (closure n φ) (format "∀^( n )[ φ ]").
Notation "φ '\[' i := j ]" := (mapf (subst i j) φ)
  (at level 45, format "φ '\[' i := j ]").

(* Unique existential quantifiction of x for φ = φ(x). *)
Definition Exists_unique x φ :=
  let z := fresh φ in
  ∃`x[φ ∧` ∀`z[φ\[x:=z] ==> x == z]].

Notation "∃! x [ φ ]" := (Exists_unique x φ) (format "∃! x [ φ ]").

End Basic_language_of_set_theory.
Import Basic_language_of_set_theory.

Module Model_definition.

(*
A set-theoretic model can be specified by giving a universe type,
an equality predicate, and an inclusion predicate.
*)
Definition model U : Type := (U -> U -> Prop) * (U -> U -> Prop).

Definition ctx U := nat -> option U.
Definition Γ0 {U} : ctx U := const None.

Section Tarski_truth.

Variable U : Type.
Variable A : model U.

(* Evaluate relation given two optionally bound values. *)
Definition Holds (R : U -> U -> Prop) x y :=
  match x, y with
  | Some u, Some v => R u v
  | _, _ => False
  end.

(* Tarski-truth definition. *)
Fixpoint Realizes (Γ : ctx U) φ : Prop :=
  match φ with
  | i == j => Holds (fst A) (Γ i) (Γ j)
  | i ∈ j => Holds (snd A) (Γ i) (Γ j)
  | ¬`ϕ => ¬Realizes Γ ϕ
  | ϕ ∧` ψ => Realizes Γ ϕ /\ Realizes Γ ψ
  | ∃`x[ϕ] => ∃u, Realizes (set x (Some u) Γ) ϕ
  end.

End Tarski_truth.

Arguments Realizes {_}.
Arguments Γ0 {_}.

Notation "↓ x" := (Some x) (at level 20, format "↓ x").
Notation "A |= ( φ )[ Γ ]" := (Realizes A Γ φ)
  (at level 75, format "A  |=  ( φ )[ Γ ]").
Notation "A |= φ" := (A |= (φ)[Γ0])
  (at level 75).

End Model_definition.
Import Model_definition.

Section General_proofs.

Variable U : Type.
Variable A : model U.

Section Part_1.

Variable Γ : ctx U.
Variable φ ϕ : formula.

Theorem disj_elim :
  A |= (φ ∨` ϕ)[Γ] -> A |= (φ)[Γ] \/ A |= (ϕ)[Γ].
Proof.
simpl; intros; apply not_and_or in H as [H|H]; apply NNPP in H; auto.
Qed.

Theorem disj_intro :
  A |= (φ)[Γ] \/ A |= (ϕ)[Γ] -> A |= (φ ∨` ϕ)[Γ].
Proof.
simpl; intros H [H1 H2]. destruct H; auto.
Qed.

Theorem implies_intro :
  (A |= (φ)[Γ] -> A |= (ϕ)[Γ]) -> A |= (φ ==> ϕ)[Γ].
Proof.
simpl; intros H [H1 H2]; apply H2, H, H1.
Qed.

Theorem implies_elim :
  A |= (φ ==> ϕ)[Γ] -> A |= (φ)[Γ] -> A |= (ϕ)[Γ].
Proof.
simpl; intros; apply not_and_or in H as [H|H]. easy. now apply NNPP.
Qed.

Theorem forall_intro x :
  (∀u, A |= (φ)[Γ;x:=↓u]) -> A |= (∀`x[φ])[Γ].
Proof.
simpl; intros H [u Hu]; apply Hu, H.
Qed.

Theorem forall_elim x :
  A |= (∀`x[φ])[Γ] -> ∀u, A |= (φ)[Γ;x:=↓u].
Proof.
simpl; intros. eapply not_ex_all_not in H. apply NNPP, H.
Qed.

End Part_1.

Section Part_2.

Variable Γ : ctx U.
Variable φ ϕ : formula.

Theorem iff_intro :
  (A |= (φ)[Γ] <-> A |= (ϕ)[Γ]) -> A |= (φ <=> ϕ)[Γ].
Proof.
intros; split; apply implies_intro; intros; now apply H.
Qed.

Theorem iff_elim :
  A |= (φ <=> ϕ)[Γ] -> (A |= (φ)[Γ] <-> A |= (ϕ)[Γ]).
Proof.
intros [H1 H2]; split; intros; eapply implies_elim.
apply H1. easy. apply H2. easy.
Qed.

Theorem closure_intro n :
  (∀Δ : ctx U, A |= (φ)[pre n Δ Γ]) -> A |= (∀^(n)[φ])[Γ].
Proof.
revert φ; induction n; simpl; intros.
assert(H' := H Γ0); now rewrite pre_0 in H'.
apply IHn; intros. apply forall_intro; intros.
rewrite set_eq_pre_pre_const, pre_pre1, pre_pre2.
apply H. lia.
Qed.

End Part_2.

Section Part_3.

Variable Γ : ctx U.
Variable φ : formula.

Theorem change_context (Δ : ctx U) :
  (∀i, free i φ = true -> Γ i = Δ i) -> A |= (φ)[Γ] -> A |= (φ)[Δ].
Proof.
unfold FV; revert Γ Δ; induction φ; simpl; intros.
1,2: erewrite <-H, <-H; try easy; now rewrite Nat.eqb_refl, ?orb_true_r.
- intros H'; apply H0.
  eapply IHf. 2: apply H'.
  intros. symmetry; now apply H.
- split. apply IHf1 with (Γ:=Γ); try easy. 2: eapply IHf2 with (Γ:=Γ); try easy.
  all: intros i Hi; apply H; now rewrite Hi, ?orb_true_r.
- destruct H0 as [u Hu]; exists u.
  eapply IHf. 2: apply Hu. intros i Hi.
  destruct (eq_dec x i). subst; now rewrite ?set_get1.
  rewrite ?set_get2; try lia. apply H.
  now replace (x =? i) with false by b_lia.
Qed.

Lemma free_max_fv bound x :
  free x φ = true -> bound x = false -> x < max_fv bound φ.
Proof.
revert bound; unfold FV; induction φ; simpl; intros.
1,2: unfold fv; destruct (x0 =? x) eqn:H1, (y =? x) eqn:H2;
b_Prop; subst; try easy; rewrite H0; lia.
- auto.
- apply orb_true_elim in H as [H|H].
  apply IHf1 in H0; try easy; lia. apply IHf2 in H0; try easy; lia.
- destruct (x0 =? x) eqn:E; try easy; b_Prop.
  apply IHf. easy. rewrite set_get2. easy. lia.
Qed.

Theorem subst_elim x y u :
  Γ y = Some u ->
  A |= (φ\[x:=y])[Γ] ->
  A |= (φ)[Γ;x:=↓u].
Proof.
Admitted.

End Part_3.

End General_proofs.

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
  ∀^(n)[∃`x[φ] ==> ∃`x[φ ∧` ∀`y[y ∈ x ==> ¬`φ\[x:=y]]]].

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

(* Some axioms also hold in the ordering of the natural numbers. *)
Section Ordering_of_the_natural_numbers.

Definition NatLt := (@Logic.eq nat, Peano.lt).

Theorem nat_realizes_extensionality :
  NatLt |= Axiom_of_extensionality.
Proof.
repeat (apply forall_intro; intros).
apply implies_intro; intros.
cut(∀i, i < u <-> i < u0).
- simpl. clear H; revert u0; induction u; intros.
  destruct u0. easy. exfalso; assert(H0 := H 0); lia.
  destruct u0. exfalso; assert(H0 := H 0); lia.
  apply eq_S, IHu. intros; split; intros; assert(Hi := H (S i)); lia.
- intros. apply forall_elim with (u:=i) in H. now apply iff_elim in H.
Qed.

Theorem nat_realizes_union :
  NatLt |= Axiom_of_union.
Proof.
repeat (apply forall_intro; intros).
exists (pred u). apply forall_intro; intros m.
apply iff_intro; split; simpl.
- exists (pred u); split; simpl; lia.
- intros [n Hn]; lia.
Qed.

Lemma classical_bounded_search (P : nat -> Prop) n :
  P n -> ∃m, m <= n /\ P m /\ ∀k, k < m -> ¬P k.
Proof.
revert P; induction n; intros. now exists 0.
apply IHn in H as [l Hl]. destruct (classic (P 0)).
exists 0; repeat split; try easy. lia.
exists (S l); repeat split. lia. easy.
intros; destruct k. easy. apply Hl; lia.
Qed.

Theorem nat_realizes_regularity φ :
  FV φ >= 1 -> NatLt |= Schema_of_regularity φ.
Proof.
intros Hφ; unfold Schema_of_regularity.
remember (FV φ - 1) as x; remember (S x) as y.
apply closure_intro; intros. remember (pre x Δ Γ0) as Γ.
apply implies_intro; intros [w Hw].
apply classical_bounded_search with (n:=w) in Hw as [m [_ [H1m H2m]]].
exists m; split. easy.
apply forall_intro; intros; apply implies_intro; intros H H'.
revert H; simpl; rewrite set_get1, set_get2, set_get1. 2: lia.
simpl; intros. apply H2m in H; apply H; clear H.
eapply subst_elim in H'. 2: apply set_get1.
rewrite set_comm, set_override in H'. 2: lia.
eapply change_context; intros. 2: apply H'.
apply free_max_fv with (bound:=const false) in H.
rewrite set_get2. easy. unfold FV in Heqx; lia. easy.
Qed.

End Ordering_of_the_natural_numbers.
