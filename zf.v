(* Introducing the axiomatic approach to set theory. *)

Require Import lib set seq.

Module Basic_language_of_set_theory.

(* Formulae in the language of set-theory. *)
Inductive formula :=
  | IsEqual (x y : nat)
  | ElementOf (x y : nat)
  | Not (φ : formula)
  | And (φ ϕ : formula)
  | Ex (x : nat) (φ : formula).

Notation "x == y" := (IsEqual x y) (at level 40).
Notation "x ∈ y" := (ElementOf x y) (at level 40).
Notation "¬` φ" := (Not φ) (at level 50, φ at next level, format "¬` φ").
Notation "x != y" := (¬`(x == y)) (at level 40).
Notation "x ∉ y" := (¬`(x ∈ y)) (at level 40).
Notation "φ ∧` ϕ" := (And φ ϕ) (at level 60).
Notation "φ ∨` ϕ" := (¬`(¬`ϕ ∧` ¬`φ)) (at level 60).
Notation "φ ==> ϕ" := (¬`(φ ∧` ¬`ϕ)) (at level 70).
Notation "φ <=> ϕ" := ((φ ==> ϕ) ∧` (ϕ ==> φ)) (at level 70).
Notation "∃` x [ φ ]" := (Ex x φ) (format "∃` x [ φ ]").
Notation "∀` x [ φ ]" := (¬`∃`x[¬`φ]) (format "∀` x [ φ ]").
Notation "⊤" := (∀`0[0 == 0]).

(* Universal quantification of n variables. *)
Fixpoint closure n φ :=
  match n with
  | 0 => φ
  | S m => closure m (∀`m[φ])
  end.

(* Compute if there is a free occurence of i in φ. *)
Fixpoint free i φ :=
  match φ with
  | x == y => (x =? i) || (y =? i)
  | x ∈ y => (x =? i) || (y =? i)
  | ¬`ϕ => free i ϕ
  | ϕ ∧` ψ => free i ϕ || free i ψ
  | ∃`x[ϕ] => if x =? i then false else free i ϕ
  end.

(* Compute if j is free in all free occurences of i. *)
Fixpoint free_at i j φ :=
  match φ with
  | x == y => true
  | x ∈ y => true
  | ¬`ϕ => free_at i j ϕ
  | ϕ ∧` ψ => free_at i j ϕ && free_at i j ψ
  | ∃`x[ϕ] =>
      if x =? i then true
      else if x =? j then negb (free i φ)
      else free_at i j ϕ
  end.

(* Compute largest variable occuring in φ. *)
Fixpoint max_var φ :=
  match φ with
  | x == y => max x y
  | x ∈ y => max x y
  | ¬`ϕ => max_var ϕ
  | ϕ ∧` ψ => max (max_var ϕ) (max_var ψ)
  | ∃`x[ϕ] => max x (max_var ϕ)
  end.

(* Compute upper bound on the number of free variables. *)
Fixpoint count_fvar (fr : nat -> bool) φ :=
  let f := λ i, if fr i then S i else 0 in
  match φ with
  | x == y => max (f x) (f y)
  | x ∈ y => max (f x) (f y)
  | ¬`ϕ => count_fvar fr ϕ
  | ϕ ∧` ψ => max (count_fvar fr ϕ) (count_fvar fr ψ)
  | ∃`x[ϕ] => count_fvar (fr;x:=false) ϕ
  end.

Notation fvar φ := (count_fvar (const true) φ).
Notation fresh φ := (S (max_var φ)).

(* Replace free occurrences of i with j. *)
Fixpoint subst i j φ :=
  let s := id;i:=j in
  match φ with
  | x == y => s x == s y
  | x ∈ y => s x ∈ s y
  | ¬`ϕ => ¬`subst i j ϕ
  | ϕ ∧` ψ => subst i j ϕ ∧` subst i j ψ
  | ∃`x[ϕ] => ∃`x[if x =? i then ϕ else subst i j ϕ]
  end.

Notation "∀^( n )[ φ ]" := (closure n φ) (format "∀^( n )[ φ ]").
Notation "φ '\[' i := j ]" := (subst i j φ)
  (at level 30, format "φ '\[' i := j ]").

(* Unique existential quantifiction of x for φ = φ(x). *)
Definition Exists_unique x φ :=
  let z := fresh φ in
  ∃`x[φ ∧` ∀`z[φ\[x:=z] ==> x == z]].

Notation "∃!` x [ φ ]" := (Exists_unique x φ) (format "∃!` x [ φ ]").

End Basic_language_of_set_theory.
Export Basic_language_of_set_theory.

Module Model_definition.

(*
A set-theoretic model can be specified by giving a universe type,
an equality predicate, and an inclusion predicate.
*)
Definition model U : Type := (U -> U -> Prop) * (U -> U -> Prop).

Notation ctx U := (nat -> option U).
Notation "↓ x" := (Some x) (at level 20, format "↓ x").
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
  | x == y => Holds (fst A) (Γ x) (Γ y)
  | x ∈ y => Holds (snd A) (Γ x) (Γ y)
  | ¬`ϕ => ¬Realizes Γ ϕ
  | ϕ ∧` ψ => Realizes Γ ϕ /\ Realizes Γ ψ
  | ∃`x[ϕ] => ∃u, Realizes (Γ;x:=↓u) ϕ
  end.

End Tarski_truth.

Arguments Realizes {_}.
Arguments Γ0 {_}.

Notation "A |= ( φ )[ Γ ]" := (Realizes A Γ φ)
  (at level 75, format "A  |=  ( φ )[ Γ ]").
Notation "A |= φ" := (A |= (φ)[Γ0]) (at level 75).

Definition Logical_consequence (Γ Δ : P formula) :=
  ∀U, ∀A : model U, (∀φ, Γ φ -> A |= φ) -> ∀φ, Δ φ -> A |= φ.

Notation "Γ ∴ Δ" := (Logical_consequence Γ Δ) (at level 80).

End Model_definition.
Export Model_definition.

Module Model_tools.

Section Part_1.

Variable U : Type.
Variable A : model U.
Variable Γ : ctx U.
Variable φ ϕ : formula.

Theorem neg_elim : A |= (¬`φ)[Γ] -> ¬ A |= (φ)[Γ].
Proof. easy. Qed.

Theorem neg_intro : ¬ A |= (φ)[Γ] -> A |= (¬`φ)[Γ].
Proof. easy. Qed.

Theorem conj_elim : A |= (φ ∧` ϕ)[Γ] -> A |= (φ)[Γ] /\ A |= (ϕ)[Γ].
Proof. easy. Qed.

Theorem conj_intro : A |= (φ)[Γ] /\ A |= (ϕ)[Γ] -> A |= (φ ∧` ϕ)[Γ].
Proof. easy. Qed.

Theorem ex_elim k : A |= (∃`k[φ])[Γ] -> ∃u, A |= (φ)[Γ;k:=↓u].
Proof. easy. Qed.

Theorem ex_intro k : (∃u, A |= (φ)[Γ;k:=↓u]) -> A |= (∃`k[φ])[Γ].
Proof. easy. Qed.

Theorem disj_elim : A |= (φ ∨` ϕ)[Γ] -> A |= (φ)[Γ] \/ A |= (ϕ)[Γ].
Proof. cbn; intros; apply not_and_or in H as [H|H]; apply NNPP in H; auto. Qed.

Theorem disj_intro : A |= (φ)[Γ] \/ A |= (ϕ)[Γ] -> A |= (φ ∨` ϕ)[Γ].
Proof. cbn; intros H [H1 H2]. destruct H; auto. Qed.

Theorem implies_intro : (A |= (φ)[Γ] -> A |= (ϕ)[Γ]) -> A |= (φ ==> ϕ)[Γ].
Proof. cbn; intros H [H1 H2]; apply H2, H, H1. Qed.

Theorem implies_elim : A |= (φ ==> ϕ)[Γ] -> A |= (φ)[Γ] -> A |= (ϕ)[Γ].
Proof. cbn; intros; apply not_and_or in H as [H|H]. easy. now apply NNPP. Qed.

Theorem forall_intro x : (∀u, A |= (φ)[Γ;x:=↓u]) -> A |= (∀`x[φ])[Γ].
Proof. cbn; intros H [u Hu]; apply Hu, H. Qed.

Theorem forall_elim x : A |= (∀`x[φ])[Γ] -> ∀u, A |= (φ)[Γ;x:=↓u].
Proof. cbn; intros. eapply not_ex_all_not in H. apply NNPP, H. Qed.

End Part_1.

Ltac fsplit := try (apply conj_intro; split).
Ltac fsplit_in H H1 H2 := try (apply conj_elim in H; destruct H as [H1 H2]).
Ltac fapply H := try (eapply implies_elim; [apply H|]).
Ltac fintro x := try (apply forall_intro; intro x).
Ltac fsuppose H := try (apply neg_intro; intro H).
Ltac fsuppose_ex x H := let H' := fresh in
  try (apply neg_intro; intro H'; apply ex_elim in H' as [x H]).
Ltac ftake x H := try (apply ex_intro; intros [x H]).
Ltac fhyp H := try (apply implies_intro; intro H).
Ltac fhyp_split H1 H2 := let H := fresh in try (fhyp H; fsplit_in H H1 H2).

Section Part_2.

Variable U : Type.
Variable A : model U.
Variable Γ : ctx U.
Variable φ ϕ : formula.

Theorem iff_intro :
  (A |= (φ)[Γ] <-> A |= (ϕ)[Γ]) -> A |= (φ <=> ϕ)[Γ].
Proof.
intros; fsplit; fhyp H'; now apply H.
Qed.

Theorem iff_elim :
  A |= (φ <=> ϕ)[Γ] -> (A |= (φ)[Γ] <-> A |= (ϕ)[Γ]).
Proof.
intro H; fsplit_in H H1 H2. split; intros.
now fapply H1. now fapply H2.
Qed.

Theorem closure_intro n :
  (∀Δ : ctx U, A |= (φ)[pre n Δ Γ]) -> A |= (∀^(n)[φ])[Γ].
Proof.
revert φ; induction n; simpl; intros.
assert(H' := H Γ0); now rewrite pre_0 in H'.
apply IHn; intros. fintro x.
rewrite set_eq_pre_pre_const, pre_pre1, pre_pre2.
apply H. lia.
Qed.

End Part_2.

Section Part_3.

Variable U : Type.
Variable A : model U.
Variable Γ : ctx U.
Variable φ : formula.

Theorem free_lt_count_fvar fr i :
  fr i = true -> free i φ = true -> i < count_fvar fr φ.
Proof.
revert fr; induction φ; simpl; intros.
1,2: destruct (x =? i) eqn:X, (y =? i) eqn:Y;
b_Prop; subst; try easy; rewrite H; lia.
- auto.
- b_Prop. apply IHf1 in H; try easy; lia. apply IHf2 in H; try easy; lia.
- destruct (x =? i) eqn:E; try easy; b_Prop.
  apply IHf. rewrite set_get2. easy. lia. easy.
Qed.

Corollary free_lt_fvar x : free x φ = true -> x < fvar φ.
Proof. intros; now apply free_lt_count_fvar. Qed.

Theorem count_fvar_le_fresh fr :
  count_fvar fr φ <= fresh φ.
Proof.
revert fr; induction φ; simpl; intros.
1,2: destruct (fr x), (fr y); lia.
- assert(IH := IHf fr); lia.
- assert(IH1 := IHf1 fr); assert(IH2 := IHf2 fr); lia.
- assert(IH := IHf (fr;x:=false)); lia.
Qed.

Corollary fvar_le_fresh : fvar φ <= fresh φ.
Proof. apply count_fvar_le_fresh. Qed.

Theorem fresh_free_at i j :
  j >= fresh φ -> free_at i j φ = true.
Proof.
induction φ; simpl; intros; auto.
b_Prop. apply IHf1. lia. apply IHf2. lia.
destruct (x =? i) eqn:I; b_Prop. easy.
destruct (x =? j) eqn:J; b_Prop.
subst; lia. apply IHf; lia.
Qed.

Theorem subst_eq i :
  φ\[i:=i] = φ.
Proof.
induction φ; simpl. 1,2: unfold set.
1,2: destruct (x =? i) eqn:X, (y =? i) eqn:Y; b_Prop; now subst.
now rewrite IHf. now rewrite IHf1, IHf2. rewrite IHf; now destruct (x =? i).
Qed.

Theorem subst_not_free_eq i j :
  free i φ = false -> φ\[i:=j] = φ.
Proof.
induction φ; simpl; intros; b_Prop.
1,2: now rewrite ?set_get2.
now rewrite IHf. now rewrite IHf1, IHf2.
destruct (x =? i). easy. now rewrite IHf.
Qed.

Theorem change_context (Δ : ctx U) :
  (∀i, free i φ = true -> Γ i = Δ i) -> A |= (φ)[Γ] -> A |= (φ)[Δ].
Proof.
revert Γ Δ; induction φ; simpl; intros.
1,2: erewrite <-H, <-H; try easy; now rewrite eqb_refl, ?orb_true_r.
- intros H'; apply H0.
  eapply IHf. 2: apply H'.
  intros. symmetry; now apply H.
- split. apply IHf1 with (Γ:=Γ); try easy. 2: eapply IHf2 with (Γ:=Γ); try easy.
  all: intros i Hi; apply H; now rewrite Hi, ?orb_true_r.
- destruct H0 as [u Hu]; exists u.
  eapply IHf. 2: apply Hu. intros i Hi.
  destruct (eq_dec i x). subst; now rewrite ?set_get1.
  rewrite ?set_get2; try lia. apply H.
  now replace (x =? i) with false by b_lia.
Qed.

End Part_3.

Section Part_4.

Variable U : Type.
Variable A : model U.
Variable Γ : ctx U.
Variable φ : formula.

Theorem subst_set_ctx i j :
  free_at i j φ = true ->
  A |= (φ\[i:=j])[Γ] <->
  A |= (φ)[Γ;i:=Γ j].
Proof.
revert Γ; induction φ; simpl; intros; split; intros.
1-4: unfold set in *; destruct (x =? i) eqn:X, (y =? i) eqn:Y; b_Prop;
subst; try rewrite ?set_get1, ?set_get2 in *; now try rewrite H in *.
1-2: intros H1; now apply H0, IHf.
1-2: b_Prop; split; try apply IHf1; try apply IHf2; easy.
all: destruct (x =? i) eqn:I, H0 as [v Hv]; b_Prop; subst; exists v.
- now rewrite set_override.
- rewrite set_comm; try easy.
  destruct (x =? j) eqn:J; b_Prop.
  + apply negb_true_iff in H.
    rewrite subst_not_free_eq in Hv; try easy.
    eapply change_context. 2: apply Hv. intros k Hk.
    symmetry; apply set_get2. intros H'; subst; now rewrite H in Hk.
  + replace (Γ j) with ((Γ;x:=↓v) j).
    now apply IHf. apply set_get2; lia.
- now rewrite set_override in Hv.
- rewrite set_comm in Hv; try easy.
  destruct (x =? j) eqn:X; b_Prop.
  + apply negb_true_iff in H.
    rewrite subst_not_free_eq; try easy.
    eapply change_context. 2: apply Hv. intros k Hk.
    apply set_get2. intros H'; subst; now rewrite H in Hk.
  + apply IHf. easy. rewrite set_get2. easy. lia.
Qed.

End Part_4.

End Model_tools.
Export Model_tools.

Section Zermelo_Fraenkel_axioms.

(* 1. Standard model theoretic conventions. *)

Definition Not_empty := ∃`0[0 == 0].
Definition Eq_reflexive := ∀`0[0 == 0].
Definition Eq_symmetric := ∀`0[∀`1[0 == 1 ==> 1 == 0]].
Definition Eq_transitive := ∀`0[∀`1[∀`2[0 == 1 ∧` 1 == 2 ==> 0 == 2]]].
Definition Eq_equivalence := Eq_reflexive ∧` Eq_symmetric ∧` Eq_transitive.

(* 2. Frege's comprehension scheme. *)

Definition Axiom_of_comprehension φ :=
  let x := fvar φ - 1 in
  let z := fresh φ in
  ∀^(x)[∃`z[∀`x[x ∈ z <=> φ]]].

Definition Schema_of_comprehension ϕ :=
  ∃φ, fvar φ >= 1 /\ ϕ = Axiom_of_comprehension φ.

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

Definition Axiom_of_regularity φ :=
  let x := fvar φ - 1 in
  let y := fresh φ in
  ∀^(x)[∃`x[φ] ==> ∃`x[φ ∧` ∀`y[y ∈ x ==> ¬`φ\[x:=y]]]].

Definition Schema_of_regularity ϕ :=
  ∃φ, fvar φ >= 1 /\ ϕ = Axiom_of_regularity φ.

Definition Axiom_of_specification φ :=
  let x := fvar φ - 1 in
  let a := fresh φ in
  let b := S a in
  ∀^(x)[∀`a[∃`b[∀`x[x ∈ b <=> x ∈ a ∧` φ]]]].

Definition Schema_of_specification ϕ :=
  ∃φ, fvar φ >= 1 /\ ϕ = Axiom_of_specification φ.

(* Fraenkels missing schema of replacement. *)
Definition Axiom_of_replacement φ :=
  let x := fvar φ - 2 in
  let y := S x in
  let a := fresh φ in
  let b := S a in
  ∀^(x)[∀`a[
    ∀`x[x ∈ a ==> ∃!`y[φ]] ==>
    ∃`b[∀`x[x ∈ a ==> ∃`y[y ∈ b ∧` φ]]]
  ]].

Definition Schema_of_replacement ϕ :=
  ∃φ, fvar φ >= 2 /\ ϕ = Axiom_of_replacement φ.

Definition ZF_finite :=
  ⦃ Not_empty ⦄ ∪
  ⦃ Eq_equivalence ⦄ ∪
  ⦃ Axiom_of_extensionality ⦄ ∪
  ⦃ Axiom_of_pairing ⦄ ∪
  ⦃ Axiom_of_union ⦄ ∪
  ⦃ Axiom_of_powersets ⦄ ∪
  Schema_of_regularity ∪
  Schema_of_specification ∪
  Schema_of_replacement.

End Zermelo_Fraenkel_axioms.

(* Eq_equivalence is realized by any equivalence relation. *)
Theorem realize_equivalence {U} (A : model U) :
  Equivalence (fst A) -> A |= Eq_equivalence.
Proof.
intros [R S T]. fsplit; fsplit.
- fintro x; apply R.
- fintro x; fintro y; fhyp H. now apply S.
- fintro x; fintro y; fintro z; fhyp_split H1 H2.
  eapply T. apply H1. easy.
Qed.

(* Frege's comprehension axiom cannot be realized. *)
Theorem Russells_paradox :
  ∃φ, Schema_of_comprehension φ /\ ∅ ∴ ⦃ ¬`φ ⦄.
Proof.
exists (Axiom_of_comprehension (0 ∉ 0)); split.
exists (0 ∉ 0); split. now lazy. easy.
intros U A _ φ def; rewrite <-def; clear def φ. fsuppose_ex uv H.
replace (fvar (0 ∉ 0) - 1) with 0 in H by now subst.
replace (fresh (0 ∉ 0)) with 1 in H by now subst.
apply forall_elim with (u:=uv), iff_elim in H.
rewrite set_comm in H. 2: easy. remember (Γ0;0:=↓uv) as Γ.
assert(R : (0 ∈ 1)\[1:=0] = 0 ∈ 0) by easy.
assert(absurd : A |= (0 ∈ 0)[Γ] <-> A |= (0 ∉ 0)[Γ]).
- split; intros.
  + apply H. replace (↓uv) with (Γ 0).
    apply subst_set_ctx. easy. now rewrite R.
    now rewrite HeqΓ, set_get1.
  + rewrite <-R. apply subst_set_ctx. easy.
    replace (Γ 0) with (↓uv). apply H, H0.
    now rewrite HeqΓ, set_get1.
- assert(A |= (0 ∉ 0)[Γ]).
  + fsuppose H1; apply absurd in H1 as H2. now apply H2 in H1.
  + apply absurd in H0 as H1. now apply H0 in H1.
Qed.

(* Some axioms also hold in the ordering of the natural numbers. *)
Section Ordering_of_the_natural_numbers.

Definition NatLt := (@Logic.eq nat, Peano.lt).

Theorem nat_realizes_extensionality :
  NatLt |= Axiom_of_extensionality.
Proof.
fintro m; fintro n; fhyp H.
cut(∀i, i < m <-> i < n).
- clear H; intros; lazy. revert H; revert m; induction n; intros.
  destruct m. easy. exfalso; assert(H0 := H 0); lia.
  destruct m. exfalso; assert(H0 := H 0); lia.
  apply eq_S, IHn. intros; split; intros; assert(Hi := H (S i)); lia.
- intros. now apply forall_elim with (u:=i), iff_elim in H.
Qed.

(* Union gives the predecessor of n. *)
Theorem nat_realizes_union :
  NatLt |= Axiom_of_union.
Proof.
fintro n; exists (pred n).
fintro m. apply iff_intro; split; simpl.
- exists (pred n); split; simpl; lia.
- intros [k Hk]; lia.
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

(* Regularity gives a smallest number in every definable set. *)
Theorem nat_realizes_regularity ϕ :
  Schema_of_regularity ϕ -> NatLt |= ϕ.
Proof.
intros [φ [Hφ def]]; subst; unfold Axiom_of_regularity.
remember (fvar φ - 1) as x;
remember (fresh φ) as y.
assert(x_lt_y : x < y). {
  subst. eapply lt_le_trans.
  2: apply fvar_le_fresh. lia. }
(* Introduce hypothesis. *)
apply closure_intro; intros; remember (pre x Δ Γ0) as Γ.
apply implies_intro; intros [n Hn].
(* Find the smallest number m that satisfies φ. *)
apply classical_bounded_search with (n:=n) in Hn as [m [_ [H1m H2m]]].
exists m; split. easy.
(* Introduce candidate k and show that k < m. *)
fintro k; apply implies_intro; intros H H'.
revert H; simpl; rewrite set_get1, set_get2, set_get1.
simpl; intros. 2: lia.
(* Show that we have a contradiction. *)
apply H2m in H; apply H; clear H. eapply subst_set_ctx in H'.
- rewrite set_comm, set_override, set_get1 in H'. 2: lia.
  eapply change_context. 2: apply H'. intros i Hi.
  apply set_get2. apply free_lt_fvar in Hi; lia.
- apply fresh_free_at; lia.
Qed.

End Ordering_of_the_natural_numbers.
