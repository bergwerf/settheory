(* General propositions and properties of functions *)

From set_theory Require Import lib. 

Lemma unfold_compose {X Y Z} {f : X -> Y} {g : Y -> Z} {h : X -> Z} :
  g ∘ f = h -> ∀x, g (f x) = h x.
Proof.
intros. eapply equal_f in H; unfold compose in H. apply H.
Qed.

Section Function_propositions.

Variable A : Type.
Variable B : Type.
Variable f : A -> B.

Definition Injective := ∀x z, f x = f z -> x = z.
Definition Surjective := ∀y, ∃x, f x = y.
Definition Bijective := ∃g, g ∘ f = id /\ f ∘ g = id.

(* A bijection is certainly injective and surjective. *)
Theorem fn_bi_inj_surj :
  Bijective -> Injective /\ Surjective.
Proof.
intros [g [H2g H1g]]; split.
- intros x z Hxz. assert(H' := unfold_compose H2g); unfold id in H'.
  now rewrite <-H'; rewrite <-H', Hxz at 1.
- intros y; exists (g y). replace y with (id y) at 2 by easy.
  now apply unfold_compose.
Qed.

(* An injective and surjective function is bijective. *)
Theorem fn_inj_surj_bi :
  Injective -> Surjective -> Bijective.
Proof.
(* We use AC to construct an inverse. *)
intros Inj Surj. apply choice in Surj as [g Hg]. exists g.
split; extensionality x; unfold compose, id.
apply Inj, Hg. apply Hg.
Qed.

End Function_propositions.

Arguments Injective {_ _} _.
Arguments Surjective {_ _} _.
Arguments Bijective {_ _} _.

(* Knuth's up-arrow notation for iterated composition *)
Notation "f ↑ n" := (iter n f) (at level 60).
