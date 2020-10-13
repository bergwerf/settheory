(* General propositions and properties of functions *)

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
