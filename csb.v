(* The Cantor-Schröder-Bernstein theorem *)

From set_theory Require Import lib fn set.

(* I use full types instead of Ensembles to make the proof more elegant. *)
Section Aquivalenzsatz.

Variable X : Type.
Variable Y : Type.
Variable f : X -> Y.
Variable g : Y -> X.
Hypothesis f_inj : Injective f.
Hypothesis g_inj : Injective g.

(* Infinite (ω) reflection of the set Y ⧵ Rng f. *)
Inductive CSB_Y : nat -> Y -> Prop :=
  | CSB_Y_0 : ∀y, ¬Rng f y -> CSB_Y 0 y
  | CSB_Y_S : ∀n x, CSB_X n x -> CSB_Y (S n) (f x)
with CSB_X : nat -> X -> Prop :=
  | CSB_X_n : ∀n y, CSB_Y n y -> CSB_X n (g y).

(* Bijective mapping as a functional relation. *)
Definition CSB_h x y : Prop :=
  (g y = x /\ ∃n, CSB_Y n y) \/ (f x = y /\ ¬∃n, CSB_X n x).

Lemma CSB_h_unique x :
  ∃!y, CSB_h x y.
Proof.
destruct (classic (∃n, CSB_X n x)) as [[n Hn]|H].
- inversion Hn; subst; exists y; split. left; split. easy. now exists n.
  intros y' [[Hy' _]|[_ Hy']]. now apply g_inj.
  exfalso; apply Hy'; now exists n.
- exists (f x); split. now right. intros y' [[Hy' [n Hn]]|[Hy' _]].
  exfalso; apply H; exists n. rewrite <-Hy'; now apply CSB_X_n. easy.
Qed.

Lemma CSB_h_inj x x' y :
  CSB_h x y -> CSB_h x' y -> x = x'.
Proof.
intros [[H1 [n Hn]]|[H1a H1b]] [[H2 [m Hm]]|[H2a H2b]].
- now rewrite <-H1, <-H2.
- exfalso; destruct n; inversion Hn; subst. apply H; now exists x'.
  apply f_inj in H2; subst. apply H2b; now exists n.
- exfalso; destruct m; inversion Hm; subst. apply H; now exists x.
  apply f_inj in H1; subst. apply H1b; now exists m.
- apply f_inj; now rewrite H1a, H2a.
Qed.

Lemma CSB_h_surj y :
  ∃x, CSB_h x y.
Proof.
destruct (classic (∃n, CSB_Y n y)) as [[n Hn]|H].
- exists (g y); left; split. easy. now exists n.
- destruct (classic (Rng f y)) as [[x Hx]|Hy].
  + exists x; right; split. easy. intros [n Hn].
    apply H; exists (S n). rewrite <-Hx; now apply CSB_Y_S.
  + exfalso; apply H; exists 0; now apply CSB_Y_0.
Qed.

Theorem CSB :
  ∃f : X -> Y, Bijective f.
Proof.
destruct (unique_choice _ _ _ CSB_h_unique) as [h Hh];
exists h; apply fn_inj_surj_bi.
- intros x x' H; apply CSB_h_inj with (y:=h x).
  apply Hh. rewrite H; apply Hh.
- intros y; destruct (CSB_h_surj y) as [x Hx]; exists x.
  destruct (CSB_h_unique x) as [y' [_ Hy']].
  now rewrite <-(Hy' y), <-(Hy' (h x)).
Qed.

End Aquivalenzsatz.
