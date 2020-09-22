(* The Cantor-Schröder-Bernstein theorem *)

From set_theory Require Import lib fn.

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
  | CSB_Y_0 : ∀y, (∀x, f x <> y) -> CSB_Y 0 y
  | CSB_Y_S : ∀n x, CSB_X n x -> CSB_Y (S n) (f x)
with CSB_X : nat -> X -> Prop :=
  | CSB_X_n : ∀n y, CSB_Y n y -> CSB_X n (g y).

Lemma CSB_choice x :
  ∃y, (∃m n, x = g y /\ CSB_Y m y /\ CSB_X n x) \/ (f x = y /\ ∀n, ~CSB_X n x).
Proof.
destruct (classic (∃i, CSB_X i x)) as [[i Hi]|H].
- inversion_clear Hi. exists y; left; exists i, i. now repeat split.
- exists (f x); right; intros; split. easy. intros n Hn; apply H; now exists n.
Qed.

Lemma CSB_Y_pred n x :
  CSB_Y n (f x) -> CSB_X (pred n) x.
Proof.
intros. inversion H. exfalso; now apply (H0 x).
apply f_inj in H0; now subst.
Qed.

(*
Y' 0     := Y ⧵ Rng f
X' n     := g (Y' n) 
Y' (n+1) := f (X' n)
h        := { (x, f x) | ∃n, x ∈ X' n } ∪ { (g(y), y) | ∃n, y ∈ Y' n }
*)
Theorem CSB :
  ∃h : X -> Y, Bijective h.
Proof.
destruct (choice _ CSB_choice) as [h Hh]; exists h. apply fn_inj_surj_bi.
- (* Injective *)
  intros x z H. destruct (Hh x) as [[n [_ [H1x [H2x _]]]]|[H1x H2x]].
  + (* x ∈ CSB_X n *)
    rewrite H1x, H. destruct (Hh z) as [[_ [_ [Hz _]]]|[H1z H2z]].
    easy. rewrite H, <-H1z in H2x; apply CSB_Y_pred in H2x.
    exfalso; now apply (H2z (pred n)).
  + (* x ∉ CSB_X *)
    destruct (Hh z) as [[i [_ [_ [Hz _]]]]|[Hz _]].
    rewrite <-H, <-H1x in Hz; apply CSB_Y_pred in Hz.
    exfalso; now apply (H2x (pred i)).
    rewrite <-H1x, <-Hz in H; now apply f_inj in H.
- (* Surjective *)
  intros y. destruct (classic (∃n, CSB_Y n y)) as [[i Hi]|H].
  + (* y ∈ CSB_Y i *)
    exists (g y). destruct (Hh (g y)) as [[_ [_ [Hgy _]]]|[_ Hgy]].
    now apply g_inj in Hgy. exfalso; apply (Hgy i). now apply CSB_X_n. 
  + (* x ∈ (Rng f) ⧵ CSB_Y *)
    assert(H0 : ~CSB_Y 0 y) by (intros H'; apply H; now exists 0).
    assert(H1 : ~∀x, f x <> y) by (intros H'; now apply CSB_Y_0 in H').
    apply not_all_not_ex in H1 as [x Hx]; exists x.
    destruct (Hh x) as [[_ [n [_ [_ Hy]]]]|[Hfx _]].
    apply CSB_Y_S in Hy; rewrite Hx in Hy. exfalso; apply H; now exists (S n).
    now rewrite <-Hfx, Hx.
Qed.

End Aquivalenzsatz.
