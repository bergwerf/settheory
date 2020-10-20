(* Well-ordering *)

From set_theory Require Import lib fn set.

(* Well-Ordering Structure *)
Record wos (X : Type) (lt : X -> X -> Prop) := Well_order {
  irreflexive  : ∀x, ¬(lt x x);
  transitive   : ∀x y z, lt x y -> lt y z -> lt x z;
  total        : ∀x y, lt x y \/ x = y \/ lt y x;
  wellorder    : ∀V : P X, V ≠ ∅ -> ∃x, V x /\ ∀y, lt y x -> ¬V y;
}.

Arguments exist {_ _}.
Arguments irreflexive {_ _}.
Arguments transitive {_ _}.
Arguments total {_ _}.
Arguments wellorder {_ _}.

Definition lt {X lt} (A : wos X lt) := lt.

Notation "x '≺_' A '`' y" := (lt A x y)
  (at level 70, A at next level, format "x  '≺_' A '`'  y").

(* A progressive property of a well-order is universal. *)
Theorem wos_ind {X lt} (A : wos X lt) (V : P X) :
  (∀x, (∀y, y ≺_A` x -> V y) -> V x) -> ∀x, V x.
Proof.
(* This is the contra-position of wellorder on the complement of V. *)
pose(Vneg x := ¬V x); intros HV.
assert(HVneg : ¬(Vneg ≠ ∅)). {
  apply (contra _ _ (wellorder A Vneg)).
  apply all_not_not_ex; intros x [H1x H2x].
  apply H1x, HV; intros. now apply NNPP, H2x. }
apply NNPP in HVneg; apply eq_incl in HVneg as [HVneg _].
intros x; destruct (classic (V x)). easy. now apply HVneg in H.
Qed.

(* A well-order has no infinite decreasing chains. *)
Theorem wos_no_infinite_descent {X lt} (A : wos X lt) (f : nat -> X) :
  ¬∀n, f (S n) ≺_A` f n.
Proof.
pose(V x := ∃n, x = f n).
assert(V ≠ ∅) by (apply not_empty; exists (f 0); now exists 0).
apply (wellorder A) in H as [x [[n Hn] Hx]]; subst.
intros H; eapply Hx. apply H. now exists (S n).
Qed.

(* Prefix of a well-ordering structure. *)
Section WOS_prefix.

Variable X : Type.
Variable lt : X -> X -> Prop.
Variable A : wos X lt.
Variable bound : X.

Definition wos_pre_prec (x y : {x : X | x ≺_A` bound}) :=
  proj1_sig x ≺_A` proj1_sig y.

Definition wos_pre :
  wos {x : X | x ≺_A` bound} wos_pre_prec.
Proof.
apply Well_order; unfold wos_pre_prec; intros.
- destruct x; simpl. apply (irreflexive A).
- destruct x, y, z; simpl. now apply (transitive A) with (y:=x0).
- destruct x, y; simpl; destruct (total A x x0) as [H|[H|H]].
  now left. right; left; subst. now rewrite (proof_irrelevance _ l l0).
  now right; right.
- pose(V' x := ∃H : x ≺_A` bound, V (exist x H)).
  assert(H' : V' ≠ ∅). {
    apply not_empty in H as [[x H1x] H2x].
    apply not_empty; exists x; now exists H1x. }
  apply (wellorder A) in H' as [x [[H1x H2x] H3x]].
  exists (exist x H1x); split. easy. intros [y H1y] H2y; simpl in H2y.
  apply H3x in H2y. intros Hneg; apply H2y; now exists H1y.
Defined.

End WOS_prefix.

Definition WOSIsomorphism {V W lt0 lt1} (A : wos V lt0) (B : wos W lt1) f :=
  Bijective f /\ ∀x y, x ≺_A` y <-> f x ≺_B` f y.

Definition WOSIsomorphic {V W lt0 lt1} (A : wos V lt0) (B : wos W lt1) :=
  ∃f, WOSIsomorphism A B f.

Notation "A ↾ x" := (wos_pre _ _ A x)(at level 90, format "A ↾ x").
Notation "A ≅ B" := (WOSIsomorphic A B)(at level 100).

(* The only automorphism of a well-order is the identity. *)
Theorem wos_automorphism_id {V lt} (A : wos V lt) f :
  WOSIsomorphism A A f -> f = id.
Proof.
Abort.

(* A well-order is not isomorphic with any prefix. *)
Theorem wos_pre_not_isomorphic {V lt} (A : wos V lt) x :
  ¬(A ≅ A↾x).
Proof.
Abort.
