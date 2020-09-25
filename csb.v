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

(*
Usually CSB is proved without AC because functions may use the excluded middle.
In set theory functions are not effective procedures, but rather formulae ϕ =
ϕ(x, y) that satisfy the property that ∀x∃!y[ϕ(x,y)]. In Coq the excluded middle
is inconsistent with other elimination rules for functions. As a middle ground
we will see that we could produce an effective procedure if CSB_X were
decidable. This gives a stronger result than using AC (= WOT).
*)
Definition CSB_X_decidable := ∀x,
  (* y ∈ CSB_Y n /\ x = g y. *)
  {n : nat & {y : Y | CSB_Y n y & x = g y}} +
  (* x ∉ CSB_X *)
  {¬∃n, CSB_X n x}.

(*
We cannot actually directly create an inhabitant of this type using AC since
CSB_X_decidable is not in Prop (although we could easily prove CSB using AC).
But we can prove a very similar statement in Prop using only classical logic.
*)
Lemma CSB_X_decidable_AC :
  ∀x, (∃n y, CSB_Y n y /\ x = g y) \/ ¬∃n, CSB_X n x.
Proof.
intros; destruct (classic (∃n, CSB_X n x)) as [[n Hn]|Hx].
inversion_clear Hn. left; now exists n, y. now right.
Qed.

(* Lets postulate this decidability. *)
Hypothesis CSB_X_dec : CSB_X_decidable.

(*
Y' 0     := Y ⧵ Rng f
X' n     := g (Y' n)
Y' (n+1) := f (X' n)
h        := { (x, f x) | ∃n, x ∈ X' n } ∪ { (g(y), y) | ∃n, y ∈ Y' n }
*)
Definition CSB_h x :=
  match CSB_X_dec x with
  | inleft (existT _ _ (exist2 _ _ y _ _)) => y
  | inright _ => f x
  end.

Lemma CSB_X_h_left n x :
  CSB_X n x -> ∃y, g y = x /\ CSB_h x = y.
Proof.
intros; unfold CSB_h. destruct (CSB_X_dec x) as [[m [y _ Hy]]|Hx].
now exists y. exfalso; apply Hx; now exists n.
Qed.

Lemma CSB_X_h_right x :
  (¬∃n, CSB_X n x) -> CSB_h x = f x.
Proof.
intros; unfold CSB_h. destruct (CSB_X_dec x) as [[m [y H1y H2y]]|Hx].
exfalso; apply H; exists m. subst; now apply CSB_X_n. easy.
Qed.

Lemma CSB_X_g_f n x :
  CSB_X n (g (f x)) -> ∃m, CSB_X m x.
Proof.
intros; inversion H; inversion H2; apply g_inj in H0; subst.
exfalso; apply H3; now exists x. apply f_inj in H5; subst; now exists n1.
Qed.

Lemma CSB_h_inj :
  Injective CSB_h.
Proof.
intros x z Hxz.
destruct (classic (∃n, CSB_X n x)) as [[n Hx]|Hx];
destruct (classic (∃n, CSB_X n z)) as [[m Hz]|Hz];
assert(Rx := Hx); assert(Rz := Hz);
try apply CSB_X_h_left in Rx as [y1 [Hy1 Rx]];
try apply CSB_X_h_left in Rz as [y2 [Hy2 Rz]];
try apply CSB_X_h_right in Rx;
try apply CSB_X_h_right in Rz;
rewrite Rx, Rz in Hxz;
clear Rx Rz; subst; try auto.
exfalso; now apply Hz, CSB_X_g_f with (n:=n).
exfalso; now apply Hx, CSB_X_g_f with (n:=m).
Qed.

Lemma CSB_h_surj :
  Surjective CSB_h.
Proof.
intros y.
destruct (classic (∃n, CSB_Y n y)) as [[n Hn]|H].
- (* y ∈ CSB_Y n *)
  exists (g y). apply CSB_X_n, CSB_X_h_left in Hn as [y' [H1y' H2y']].
  rewrite H2y'. now apply g_inj.
- (* y ∈ (Rng f) ⧵ CSB_Y *)
  assert(Hy : Rng f y). { apply not_all_not_ex; intros H'.
    apply all_not_not_ex, CSB_Y_0 in H'. apply H; now exists 0. }
  destruct Hy as [x Hx]; exists x. rewrite CSB_X_h_right. easy.
  intros [n Hn]; apply H; exists (S n). rewrite <-Hx; now apply CSB_Y_S.
Qed.

Theorem CSB :
  ∃h : X -> Y, Injective h /\ Surjective h.
Proof.
exists CSB_h; split.
apply CSB_h_inj.
apply CSB_h_surj.
Qed.

End Aquivalenzsatz.
