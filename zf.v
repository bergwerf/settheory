(* Introducing the axiomatic approach to set theory. *)

Require Import lib set seq.

Module Basic_language_of_set_theory.

(* Formulae in the basic language of set-theory. *)
Inductive formula :=
  | IsEqual (i j : nat)
  | ElementOf (i j : nat)
  | Negation (φ : formula)
  | Conjunction (φ ϕ : formula)
  | Exists (i : nat) (φ : formula).

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

(* Compute if there is a free occurence of x in φ. *)
Fixpoint free x φ :=
  match φ with
  | i == j => (i =? x) || (j =? x)
  | i ∈ j => (i =? x) || (j =? x)
  | ¬`ϕ => free x ϕ
  | ϕ ∧` ψ => free x ϕ || free x ψ
  | ∃`i[ϕ] => if i =? x then false else free x ϕ
  end.

(* Compute if y is free in all free occurences of x. *)
Fixpoint free_at x y φ :=
  match φ with
  | i == j => true
  | i ∈ j => true
  | ¬`ϕ => free_at x y ϕ
  | ϕ ∧` ψ => free_at x y ϕ && free_at x y ψ
  | ∃`i[ϕ] =>
      if i =? x then true
      else if i =? y then negb (free x φ)
      else free_at x y ϕ
  end.

(* Compute largest variable occuring in φ. *)
Fixpoint max_var φ :=
  match φ with
  | i == j => max i j
  | i ∈ j => max i j
  | ¬`ϕ => max_var ϕ
  | ϕ ∧` ψ => max (max_var ϕ) (max_var ψ)
  | ∃`i[ϕ] => max i (max_var ϕ)
  end.

(* Compute upper bound on the number of free variables. *)
Fixpoint count_fvar (Γ : nat -> bool) φ :=
  let f := λ i, if Γ i then 0 else S i in
  match φ with
  | i == j => max (f i) (f j)
  | i ∈ j => max (f i) (f j)
  | ¬`ϕ => count_fvar Γ ϕ
  | ϕ ∧` ψ => max (count_fvar Γ ϕ) (count_fvar Γ ψ)
  | ∃`x[ϕ] => count_fvar (Γ;x:=true) ϕ
  end.

(* Replace free occurrences of x with y. *)
Fixpoint subst x y φ :=
  match φ with
  | i == j => (id;x:=y) i == (id;x:=y) j
  | i ∈ j => (id;x:=y) i ∈ (id;x:=y) j
  | ¬`ϕ => ¬`subst x y ϕ
  | ϕ ∧` ψ => subst x y ϕ ∧` subst x y ψ
  | ∃`i[ϕ] => ∃`i[if i =? x then ϕ else subst x y ϕ]
  end.

Definition fvar φ := count_fvar (const false) φ.
Definition fresh φ := S (max_var φ).

Notation "∀^( n )[ φ ]" := (closure n φ) (format "∀^( n )[ φ ]").
Notation "φ '\[' i := j ]" := (subst i j φ)
  (at level 30, format "φ '\[' i := j ]").

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
Notation "A |= φ" := (A |= (φ)[Γ0]) (at level 75).

Definition Logical_consequence (Γ Δ : P formula) :=
  ∀U, ∀A : model U, (∀φ, Γ φ -> A |= φ) -> ∀φ, Δ φ -> A |= φ.

Notation "Γ |- Δ" := (Logical_consequence Γ Δ) (at level 80).

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

Theorem free_lt_count_fvar bound x :
  free x φ = true -> bound x = false -> x < count_fvar bound φ.
Proof.
revert bound; induction φ; simpl; intros.
1,2: destruct (i =? x) eqn:I, (j =? x) eqn:J;
b_Prop; subst; try easy; rewrite H0; lia.
- auto.
- b_Prop. apply IHf1 in H0; try easy; lia. apply IHf2 in H0; try easy; lia.
- destruct (i =? x) eqn:E; try easy; b_Prop.
  apply IHf. easy. rewrite set_get2. easy. lia.
Qed.

Corollary free_lt_fvar x : free x φ = true -> x < fvar φ.
Proof. intros; now apply free_lt_count_fvar. Qed.

Theorem count_fvar_le_S_max_var bound :
  count_fvar bound φ <= S (max_var φ).
Proof.
revert bound; induction φ; simpl; intros.
1,2: destruct (bound i), (bound j); lia.
- assert(IH := IHf bound); lia.
- assert(IH1 := IHf1 bound); assert(IH2 := IHf2 bound); lia.
- assert(IH := IHf (bound;i:=true)); lia.
Qed.

Corollary fvar_le_fresh : fvar φ <= fresh φ.
Proof. apply count_fvar_le_S_max_var. Qed.

Theorem fresh_free_at x y :
  y >= fresh φ -> free_at x y φ = true.
Proof.
unfold fresh; induction φ; simpl; intros; auto.
b_Prop. apply IHf1. lia. apply IHf2. lia.
destruct (i =? x) eqn:X; b_Prop. easy.
destruct (i =? y) eqn:Y; b_Prop.
subst; lia. apply IHf; lia.
Qed.

Theorem subst_eq x :
  φ\[x:=x] = φ.
Proof.
induction φ; simpl. 1,2: unfold set.
1,2: destruct (i =? x) eqn:I, (j =? x) eqn:J; b_Prop; now subst.
now rewrite IHf. now rewrite IHf1, IHf2. rewrite IHf; now destruct (i =? x).
Qed.

Theorem subst_not_free_eq x y :
  free x φ = false -> φ\[x:=y] = φ.
Proof.
induction φ; simpl; intros; b_Prop.
1,2: now rewrite ?set_get2.
now rewrite IHf. now rewrite IHf1, IHf2.
destruct (i =? x). easy. now rewrite IHf.
Qed.

Theorem change_context (Δ : ctx U) :
  (∀x, free x φ = true -> Γ x = Δ x) -> A |= (φ)[Γ] -> A |= (φ)[Δ].
Proof.
revert Γ Δ; induction φ; simpl; intros.
1,2: erewrite <-H, <-H; try easy; now rewrite Nat.eqb_refl, ?orb_true_r.
- intros H'; apply H0.
  eapply IHf. 2: apply H'.
  intros. symmetry; now apply H.
- split. apply IHf1 with (Γ:=Γ); try easy. 2: eapply IHf2 with (Γ:=Γ); try easy.
  all: intros i Hi; apply H; now rewrite Hi, ?orb_true_r.
- destruct H0 as [u Hu]; exists u.
  eapply IHf. 2: apply Hu. intros j Hj.
  destruct (eq_dec i j). subst; now rewrite ?set_get1.
  rewrite ?set_get2; try lia. apply H.
  now replace (i =? j) with false by b_lia.
Qed.

End Part_3.

Section Part_4.

Variable Γ : ctx U.
Variable φ : formula.

Theorem subst_set_ctx x y :
  free_at x y φ = true ->
  A |= (φ\[x:=y])[Γ] <->
  A |= (φ)[Γ;x:=Γ y].
Proof.
revert Γ; induction φ; simpl; intros; split; intros.
1-4: unfold set in *; destruct (i =? x) eqn:I, (j =? x) eqn:J; b_Prop;
subst; try rewrite ?set_get1, ?set_get2 in *; now try rewrite H in *.
1-2: intros H1; now apply H0, IHf.
1-2: b_Prop; split; try apply IHf1; try apply IHf2; easy.
all: destruct (i =? x) eqn:I, H0 as [v Hv]; b_Prop; subst; exists v.
- now rewrite set_override.
- rewrite set_comm; try easy.
  destruct (i =? y) eqn:Y; b_Prop.
  + apply negb_true_iff in H.
    rewrite subst_not_free_eq in Hv; try easy.
    eapply change_context. 2: apply Hv. intros j Hj.
    symmetry; apply set_get2. intros H'; subst; now rewrite H in Hj.
  + replace (Γ y) with ((Γ;i:=↓v) y).
    now apply IHf. apply set_get2; lia.
- now rewrite set_override in Hv.
- rewrite set_comm in Hv; try easy.
  destruct (i =? y) eqn:Y; b_Prop.
  + apply negb_true_iff in H.
    rewrite subst_not_free_eq; try easy.
    eapply change_context. 2: apply Hv. intros j Hj.
    apply set_get2. intros H'; subst; now rewrite H in Hj.
  + apply IHf. easy. rewrite set_get2. easy. lia.
Qed.

End Part_4.

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
  let x := fvar φ - 1 in
  let z := fresh φ in
  ∀^(x)[∃`z[∀`x[x ∈ z <=> φ]]].

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
  let x := fvar φ - 1 in
  let y := fresh φ in
  ∀^(x)[∃`x[φ] ==> ∃`x[φ ∧` ∀`y[y ∈ x ==> ¬`φ\[x:=y]]]].

Definition Schema_of_specification φ :=
  let x := fvar φ - 1 in
  let a := fresh φ in
  let b := S a in
  ∀^(x)[∀`a[∃`b[∀`x[x ∈ b <=> x ∈ a ∧` φ]]]].

(* Fraenkels missing schema of replacement. *)
Definition Schema_of_replacement φ :=
  let x := fvar φ - 2 in
  let y := S x in
  let a := fresh φ in
  let b := S a in
  ∀^(x)[∀`a[
    ∀`x[x ∈ a ==> ∃!y[φ]] ==>
    ∃`b[∀`x[x ∈ a ==> ∃`y[y ∈ b ∧` φ]]]
  ]].

End Zermelo_Fraenkel_axioms.

(* Frege's comprehension axiom cannot be realized. *)
Theorem Russells_paradox :
  ∃φ, ∅ |- ⦃ ¬`Schema_of_comprehension φ ⦄.
Proof.
exists (0 ∉ 0).
intros U A _ φ def; rewrite <-def; clear def φ. intros [uv H].
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
  + intros H1; apply absurd in H1 as H2. now apply H2 in H1.
  + apply absurd in H0 as H1. now apply H0 in H1.
Qed.

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

(* Union gives the predecessor of n. *)
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

(* Regularity gives a smallest number in every definable set. *)
Theorem nat_realizes_regularity φ :
  fvar φ >= 1 -> NatLt |= Schema_of_regularity φ.
Proof.
intros Hφ; unfold Schema_of_regularity.
remember (fvar φ - 1) as x;
remember (fresh φ) as y.
assert(x_lt_y : x < y). {
  subst. eapply lt_le_trans.
  2: apply fvar_le_fresh. lia. }
(* Introduce hypothesis. *)
apply closure_intro; intros. remember (pre x Δ Γ0) as Γ.
apply implies_intro; intros [w Hw].
(* Find the smallest number m that satisfies φ. *)
apply classical_bounded_search with (n:=w) in Hw as [m [_ [H1m H2m]]].
exists m; split. easy.
(* Introduce candidate u and show that u < m. *)
apply forall_intro; intros; apply implies_intro; intros H H'.
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
