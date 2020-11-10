(* General propositions and properties of functions. *)

From set_theory Require Import lib.

Section Function_propositions.

Variable A : Type.
Variable B : Type.
Variable f : A -> B.

Definition Injective := ∀x z, f x = f z -> x = z.
Definition Surjective := ∀y, ∃x, f x = y.
Definition Bijective := ∃g, (∀ x, g (f x) = x) /\ ∀y, f (g y) = y.

(* A bijection is certainly injective and surjective. *)
Theorem fn_bi_inj_surj :
  Bijective -> Injective /\ Surjective.
Proof.
intros [g [H2g H1g]]; split.
- intros x z Hxz. now rewrite <-H2g, <-Hxz.
- intros y; now exists (g y).
Qed.

(* An injective and surjective function is bijective. *)
Theorem fn_inj_surj_bi :
  Injective -> Surjective -> Bijective.
Proof.
intros inj surj. assert(∀y, ∃!x, f x = y). {
  intros; destruct (surj y) as [x Hx]; exists x. split; try easy.
  intros; apply inj. now rewrite H, Hx. }
apply unique_choice in H as [g Hg]; exists g.
split; intros. now apply inj. easy.
Qed.

End Function_propositions.

Arguments Injective {_ _} _.
Arguments Surjective {_ _} _.
Arguments Bijective {_ _} _.

(* Knuth's up-arrow notation for iterated composition *)
Notation "f ↑ n" := (iter n f) (at level 60).

(* Helpful lemmas when working with function relations. *)
Section Function_relations.

Variable X : Type.
Variable Y : Type.

(* A function that can be separated into two parts. *)
Lemma fn_rel_lem (P : X -> Prop) Pos Neg :
  (∀x, P x -> ∃!y, Pos x y) ->
  (∀x, ¬P x -> ∃!y, Neg x y) ->
  ∀x, ∃!y : Y, (P x /\ Pos x y) \/ (¬P x /\ Neg x y).
Proof.
intros Hpos Hneg x. destruct (classic (P x)) as [H|H].
- destruct (Hpos _ H) as [y [H1y H2y]]; exists y; split. now left.
  intros x' [Hx'|Hx']. now apply H2y. easy.
- destruct (Hneg _ H) as [y [H1y H2y]]; exists y; split. now right.
  intros x' [Hx'|Hx']. easy. now apply H2y.
Qed.

(* A function relation based on a constant. *)
Lemma fn_rel_const (c : Y) : ∃!y, y = c.
Proof. now exists c. Qed.

(* A function relation based on a function. *)
Lemma fn_rel_fn (f : X -> Y) x : ∃!y, y = f x.
Proof. now exists (f x). Qed.

End Function_relations.
