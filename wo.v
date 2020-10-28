(* Well-ordering *)

From set_theory Require Import lib fn pair set.

Arguments exist {_ _}.

(* Equivalent properties of well-orderings. *)
Section Well_ordering.

Variable X : Type.
Variable lt : X -> X -> Prop.

(* This is just a trick to get nice notations. *)
Definition Lt := lt.

(* Well-order 1: each non-empty set as a least member. *)
Definition wellorder1 := ∀W : P X, W ≠ ∅ -> ∃x, W x /\ ∀y, Lt y x -> ¬W y.

(* Well-order 2: each progressive property is universal. *)
Definition wellorder2 := ∀P : P X, (∀x, (∀y, Lt y x -> P y) -> P x) -> ∀x, P x.

(* Well-order 3: there is no infinitely decreasing sequence. *)
Definition wellorder3 := ∀f : nat -> X, ∃n, ¬Lt (f (S n)) (f n).

Theorem wellorder1iff2 :
  wellorder1 <-> wellorder2.
Proof.
(* These statements are each others contraposition. *)
unfold wellorder1, wellorder2; split; intros H.
- intros P HP. eapply classic_contra. 2: exact HP. intros HPneg.
  apply not_all_ex_not, not_empty, H in HPneg as [x [H1x H2x]].
  apply ex_not_not_all; exists x; intros Hy.
  apply H1x, Hy. intros; now apply NNPP, H2x.
- intros W HW. apply not_all_not_ex; eapply contra. 2: exact HW.
  intros HWneg. apply empty, H; intros x Hx.
  destruct (not_and_or _ _ (HWneg x)); easy.
Qed.

Theorem wellorder1iff3 :
  wellorder1 <-> wellorder3.
Proof.
unfold wellorder1, wellorder3; split; intros H.
- (* Find lower bound in the range of f. *)
  intros f. assert(Rng f ≠ ∅) by (apply not_empty; now exists (f 0), 0).
  apply H in H0 as [x [[n Hn] Hx]]; exists n; subst.
  intros Hn; apply Hx in Hn; apply Hn. now exists (S n).
- (* Create infinite decreasing sequence using dependent countable choice. *)
  apply NNPP; intros Hneg; apply not_all_ex_not in Hneg as [W HW].
  apply imply_to_and in HW as [H1W H2W].
  apply not_empty in H1W as [v Hv].
  pose(v0 := exist v Hv).
  pose(sigW := {x : X | W x}).
  assert(H3W : ∀x : sigW, ∃y : sigW, Lt (sig1 y) (sig1 x)). {
    intros [x Hx]. apply not_ex_all_not with (n:=x) in H2W.
    apply not_and_or in H2W as [H2W|H2W]. easy.
    apply not_all_ex_not in H2W as [y Hy].
    apply imply_to_and in Hy as [H1y H2y].
    apply NNPP in H2y. now exists (exist y H2y). }
  destruct (DC_fun _ _ H3W v0) as [f [_ Hf]].
  pose(g n := sig1 (f n)). destruct (H g) as [n Hn].
  apply Hn; unfold g; apply Hf.
Qed.

(* Well-Ordering Structure *)
Definition wos :=
  (∀x, ¬(Lt x x)) /\
  (∀x y z, Lt x y -> Lt y z -> Lt x z) /\
  (∀x y, Lt x y \/ x = y \/ Lt y x) /\
  wellorder1.

Definition irreflexive (A : wos) := proj1 A.
Definition transitive (A : wos) := proj1 (proj2 A).
Definition total (A : wos) := proj1 (proj2 (proj2 A)).
Definition wellorder (A : wos) := proj2 (proj2 (proj2 A)).

End Well_ordering.

Arguments Lt {_}.
Arguments irreflexive {_ _}.
Arguments transitive {_ _}.
Arguments total {_ _}.
Arguments wellorder {_ _}.

Notation "x '<' lt '`' y" := (Lt lt x y)
  (at level 70, lt at next level, format "x  '<' lt '`'  y").

(* Re-statement of wellorder2. *)
Theorem wos_ind {V _0} (A : wos V _0) (P : P V) :
  (∀x, (∀y, y <_0` x -> P y) -> P x) -> ∀x, P x.
Proof.
apply wellorder1iff2, A.
Qed.

(* Initial segment of a well-ordering structure. *)
Section WOS_initial_segment.

Variable V : Type.
Variable _0 : V -> V -> Prop.
Variable A : wos V _0.
Variable t : V.

Definition segment_lt (x y : {x : V | x <_0` t}) :=
  proj1_sig x <_0` proj1_sig y.

Theorem wos_initial_segment :
  wos {x : V | x <_0` t} segment_lt.
Proof.
unfold segment_lt; repeat split; intros.
- destruct x; simpl. apply (irreflexive A).
- destruct x, y, z; simpl. now apply (transitive A) with (y:=x0).
- destruct x, y; simpl; destruct (total A x x0) as [H|[H|H]].
  now left. right; left; subst. now rewrite (proof_irrelevance _ l l0).
  now right; right.
- intros W H.
  pose(U x := ∃H : x <_0` t, W (exist x H)).
  assert(HU : U ≠ ∅). {
    apply not_empty in H as [[x H1x] H2x].
    apply not_empty; exists x; now exists H1x. }
  apply (wellorder A) in HU as [x [[H1x H2x] H3x]].
  exists (exist x H1x); split. easy. intros [y H1y] H2y; simpl in H2y.
  apply H3x in H2y. intros Hneg; apply H2y; now exists H1y.
Qed.

End WOS_initial_segment.

Arguments segment_lt {_}.
Arguments wos_initial_segment {_ _}.

(* The well-order A is isomorphic to B. *)
Definition WOSIsomorphism {V W _0 _1} (A : wos V _0) (B : wos W _1) f :=
  Bijective f /\ ∀x y, x <_0` y <-> f x <_1` f y.

Notation "A ↾ x" := (wos_initial_segment A x)(at level 90, format "A ↾ x").
Notation "A ≅ B" := (∃f, WOSIsomorphism A B f)(at level 100).

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

(* Because of the previous theorem we may now define this. *)
Notation "A ≺ B" := (∃x, A ≅ B↾x)(at level 100).

(* Creating ever larger well-orderings of the natural numbers. *)
Require Import Wf_nat.
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
Theorem lex_wos :
  wos nat lex.
Proof.
repeat split; unfold Lt, lex; intros;
try destruct (π_inv x) as [nx x'] eqn:Ex;
try destruct (π_inv y) as [ny y'] eqn:Ey;
try destruct (π_inv z) as [nz z'].
- intros [H|[_ H]]. lia. now apply (irreflexive (A nx)) in H.
- destruct H as [H1|[H1eq H1]], H0 as [H2|[H2eq H2]]. 1,2,3: left; lia.
  subst. right; split. easy. eapply (transitive (A nz)). apply H1. apply H2.
- destruct (lt_eq_lt_dec nx ny) as [[H|H]|H].
  1: now left; left. 2: now right; right; left. subst.
  destruct (total (A ny) x' y') as [H|[H|H]].
  1: now left; right. 2: now right; right; right. subst.
  right; left. destruct (fn_bi_inj_surj _ _ _ π_inv_bijective) as [Hπ _].
  eapply Hπ; now rewrite Ex, Ey.
- (* TBD *)
Admitted.

(* A_n is isomorphic with an initial segment of the lexicographic ordening. *)
Theorem lex_wos_larger n :
  A n ≺ lex_wos.
Proof.
Abort.

End Larger_lexicographic_ordenings.
