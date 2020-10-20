(* Well-ordering *)

From set_theory Require Import lib fn pair set.

(* This is just a trick to get nice notations. *)
Definition Lt {X} (lt : X -> X -> Prop) x y := lt x y.

(* Well-Ordering Structure *)
Record wos (X : Type) (lt : X -> X -> Prop) := Well_order {
  irreflexive  : ∀x, ¬(Lt lt x x);
  transitive   : ∀x y z, Lt lt x y -> Lt lt y z -> Lt lt x z;
  total        : ∀x y, Lt lt x y \/ x = y \/ Lt lt y x;
  wellorder    : ∀W : P X, W ≠ ∅ -> ∃x, W x /\ ∀y, Lt lt y x -> ¬W y;
}.

Arguments exist {_ _}.
Arguments irreflexive {_ _}.
Arguments transitive {_ _}.
Arguments total {_ _}.
Arguments wellorder {_ _}.

Notation "x '<' lt '`' y" := (Lt lt x y)
  (at level 70, lt at next level, format "x  '<' lt '`'  y").

(* A progressive property of a well-order is universal. *)
Theorem wos_ind {V _0} (A : wos V _0) (P : P V) :
  (∀x, (∀y, y <_0` x -> P y) -> P x) -> ∀x, P x.
Proof.
(* This is the contra-position of wellorder on the complement of V. *)
pose(Q x := ¬P x); intros HP.
assert(HQ : ¬(Q ≠ ∅)). {
  apply (contra _ _ (wellorder A Q)).
  apply all_not_not_ex; intros x [H1x H2x].
  apply H1x, HP; intros. now apply NNPP, H2x. }
apply NNPP in HQ; apply eq_incl in HQ as [HQ _].
intros x; apply NNPP; intros H. now apply HQ in H.
Qed.

(* A well-order has no infinite decreasing chains. *)
Theorem wos_no_infinite_descent {V _0} (A : wos V _0) (f : nat -> V) :
  ¬∀n, f (S n) <_0` f n.
Proof.
pose(P x := ∃n, x = f n).
assert(P ≠ ∅) by (apply not_empty; exists (f 0); now exists 0).
apply (wellorder A) in H as [x [[i Hi] Hx]]; subst.
intros H; eapply Hx. apply H. now exists (S i).
Qed.

(* Initial segment of a well-ordering structure. *)
Section WOS_initial_segment.

Variable V : Type.
Variable _0 : V -> V -> Prop.
Variable A : wos V _0.
Variable t : V.

Definition segment_lt (x y : {x : V | x <_0` t}) :=
  proj1_sig x <_0` proj1_sig y.

Definition wos_initial_segment :
  wos {x : V | x <_0` t} segment_lt.
Proof.
apply Well_order; unfold segment_lt; intros.
- destruct x; simpl. apply (irreflexive A).
- destruct x, y, z; simpl. now apply (transitive A) with (y:=x0).
- destruct x, y; simpl; destruct (total A x x0) as [H|[H|H]].
  now left. right; left; subst. now rewrite (proof_irrelevance _ l l0).
  now right; right.
- pose(U x := ∃H : x <_0` t, W (exist x H)).
  assert(HU : U ≠ ∅). {
    apply not_empty in H as [[x H1x] H2x].
    apply not_empty; exists x; now exists H1x. }
  apply (wellorder A) in HU as [x [[H1x H2x] H3x]].
  exists (exist x H1x); split. easy. intros [y H1y] H2y; simpl in H2y.
  apply H3x in H2y. intros Hneg; apply H2y; now exists H1y.
Defined.

End WOS_initial_segment.

Arguments segment_lt {_}.
Arguments wos_initial_segment {_ _}.

(* The well-order A is isomorphic to B. *)
Definition WOSIsomorphism {V W _0 _1} (A : wos V _0) (B : wos W _1) f :=
  Bijective f /\ ∀x y, x <_0` y <-> f x <_1` f y.

Notation "A ↾ x" := (wos_initial_segment A x)(at level 90, format "A ↾ x").
Notation "A ≅ B" := (∃f, WOSIsomorphism A B f)(at level 100).
Notation "A ≺ B" := (∃x, A↾x ≅ B)(at level 100).

Lemma wos_total {V _0} (A : wos V _0) x y :
  x ≠ y -> x <_0` y \/ y <_0` x.
Proof.
intros Hneq; destruct (total A x y) as [H|[H|H]].
now left. easy. now right.
Qed.

(* The only automorphism of a well-order is the identity. *)
Theorem wos_automorphism_id {V _0} (A : wos V _0) f :
  WOSIsomorphism A A f -> f = id.
Proof.
intros [[g [_ Hg]] f_iso]; extensionality x; unfold id; revert x.
apply (wos_ind A); intros x IH. apply NNPP; intros H.
apply (wos_total A) in H as [H|H].
- apply IH in H as H1; apply f_iso in H as H2.
  rewrite H1 in H2; now apply irreflexive in H2.
- rewrite <-Hg in H at 1; apply f_iso in H.
  apply IH in H as H1; rewrite Hg in H1.
  rewrite <-H1 in H; now apply irreflexive in H.
Qed.

(* A well-order is not isomorphic with a prefix of itself. *)
Theorem wos_ncong_pre {V _0} (A : wos V _0) t :
  ¬(A ≅ A↾t).
Proof.
intros [f [[g [_ Hg]] f_iso]].
unfold segment_lt, Lt at 2 in f_iso.
(* This is very similar to wos_automorphism_id. *)
assert(∀x, sig1 (f x) = x). {
  apply (wos_ind A); intros x IH. apply NNPP; intros H.
  apply (wos_total A) in H as [H|H].
  - apply IH in H as H1; apply f_iso in H as H2.
    rewrite H1 in H2; now apply irreflexive in H2.
  - assert(Hx : x <_0` t). {
      eapply (transitive A). apply H. apply (sig2 (f x)). }
    pose(xt := exist x Hx : {x : V | x <_0` t}).
    replace x with (sig1 (f (g xt))) in H at 1 by now rewrite Hg.
    apply f_iso in H. apply IH in H as H1; rewrite Hg in H1.
    rewrite <-H1 in H; now apply irreflexive in H. }
(* Now we find a contradiction. *)
assert(Hft := sig2 (f t)); simpl in Hft.
rewrite H in Hft. now apply irreflexive in Hft.
Qed.

(* Two different prefixes of a well-order are not isomorphic. *)
Theorem wos_pre_ncong {V _0} (A : wos V _0) s t :
  s <_0` t -> ¬(A↾t ≅ A↾s).
Proof.
intros Hst [f [[g [_ Hg]] f_iso]].
unfold segment_lt, Lt at 3, Lt at 6 in f_iso.
(* This is again very similar to wos_automorphism_id. *)
assert(∀x, sig1 (f x) = sig1 x). {
  apply (wos_ind (A↾t)); intros x IH.
  unfold segment_lt, Lt at 2 in IH. apply NNPP; intros H.
  apply (wos_total A) in H as [H|H].
  - assert(Hfx : sig1 (f x) <_0` t). {
      eapply (transitive A). apply (sig2 (f x)). easy. }
    pose(fxt := exist (sig1 (f x)) Hfx : {x : V | x <_0` t}).
    replace (sig1 (f x)) with (sig1 (fxt)) in H by easy.
    apply IH in H as H1; apply f_iso in H as H2.
    rewrite H1 in H2; now apply irreflexive in H2.
  - assert(Hx : sig1 x <_0` s). {
      eapply (transitive A). apply H. apply (sig2 (f x)). }
    pose(xs := exist (sig1 x) Hx : {x : V | x <_0` s}).
    replace (sig1 x) with (sig1 xs) in H by easy.
    rewrite <-Hg in H at 1; apply f_iso in H.
    apply IH in H as H1; rewrite Hg in H1.
    rewrite <-H1 in H; now apply irreflexive in H. }
(* Now we find a contradiction. *)
pose(sx := exist s Hst : {x : V | x <_0` t}).
assert(Hft := sig2 (f sx)); simpl in Hft.
rewrite H in Hft; simpl in Hft.
now apply irreflexive in Hft.
Qed.

(* Creating ever larger well-orderings of the natural numbers. *)
Section Larger_lexicographic_ordenings.

(* Given is a sequence of well-orderings of the natural numbers. *)
Variable lt : nat -> nat -> nat -> Prop.
Variable A : ∀n, wos nat (lt n).

(* We define a lexicographic ordering. *)
Definition lex m n :=
  let (m, x) := π_inv m in
  let (n, y) := π_inv n in
  m < n \/ (m = n /\ x <lt n` y).

(* This well-orders the natural numbers. *)
Definition lex_wos :
  wos nat lex.
Proof.
Admitted.

(* A_n is isomorphic with an initial segment of the lexicographic ordening. *)
Theorem lex_wos_larger n :
  A n ≺ lex_wos.
Proof.
Abort.

End Larger_lexicographic_ordenings.
