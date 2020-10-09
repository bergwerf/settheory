(* General propositions and properties of functions *)

From set_theory Require Import lib.

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
- intros x z Hxz. assert(H' := equal_f H2g); unfold id, compose in H'.
  now rewrite <-H'; rewrite <-H', Hxz at 1.
- intros y; exists (g y). replace y with (id y) at 2 by easy.
  eapply equal_f in H1g; unfold compose in H1g; apply H1g.
Qed.

(* An injective and surjective function is bijective. *)
Theorem fn_inj_surj_bi :
  Injective -> Surjective -> Bijective.
Proof.
intros inj surj. assert(∀y, ∃!x, f x = y). {
  intros; destruct (surj y) as [x Hx]; exists x. split; try easy.
  intros; apply inj. now rewrite H, Hx. }
apply unique_choice in H as [g Hg]; exists g.
split; extensionality x; unfold compose, id.
apply inj, Hg. apply Hg.
Qed.

End Function_propositions.

Arguments Injective {_ _} _.
Arguments Surjective {_ _} _.
Arguments Bijective {_ _} _.

(* Knuth's up-arrow notation for iterated composition *)
Notation "f ↑ n" := (iter n f) (at level 60).

Lemma fold_compose {X Y Z} (f : X -> Y) (g : Y -> Z) x : g (f x) = (g ∘ f) x.
Proof. easy. Qed.

Lemma iter_S_compose {X} (f : X -> X) n : f ↑ (S n) = f ∘ (f ↑ n).
Proof. easy. Qed.
