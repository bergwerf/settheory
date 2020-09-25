(* A proof that the Continuum Hypothesis holds for closed sets. *)

From set_theory Require Import lib fn pair bin set d cb.

(*
We can prove CH for closed sets. With closed sets we can exploit a hierarchy of
derived sets given by the Cantor-Bendixon derivatives. Open sets are trickier
because a countable open set may contain uncountably many limit points. (Take
for example all finite sequences prepended to zeros. This is similar to the
rational numbers which approach all real numbers.)
*)
Section Continuum_Hypothesis.

Variable X : P C.
Hypothesis closed_X : Closed X.

(* A set Y ⊆ C embeds C if a one-to-one function f : C -> Y exists. *)
Definition EmbedsC (Y : P C) := ∃f : C -> C, Injective f /\ ∀α, Y (f α).

(* Every infinite set X is either countable or embeds C. *)
Definition CH := Infinite X -> Countable X \/ EmbedsC X.

(* C embeds into any non-empty, perfect set. *)
Lemma nonempty_perfect_embeds_C (Y : P C) :
  Y ≠ ∅ -> Perfect Y -> EmbedsC Y.
Proof.
intros ex H; apply not_empty in ex as [α Hα].
Admitted.

(* Either X is countable or C embeds into X. *)
Theorem Closed_Continuum_Hypothesis : CH.
Proof.
destruct (classic (K X = ∅)).
- left. rewrite <-diff_empty, <-H. now apply CB_countable_diff, CB_K.
- right. apply nonempty_perfect_embeds_C in H as [f [H1f H2f]].
  exists f; split. easy. intros; eapply CB_incl. easy.
  now apply CB_K. apply H2f. now apply CB_K_perfect.
Qed.

End Continuum_Hypothesis.
