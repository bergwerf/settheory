(* Well-ordering *)

From set_theory Require Import lib set.

(* Well-Ordering Structure *)
Record wos (X : Type) := Well_order {
  prec         : X -> X -> Prop;
  irreflexive  : ∀x, ¬(prec x x);
  transitive   : ∀x y z, prec x y -> prec y z -> prec x z;
  total        : ∀x y, prec x y \/ x = y \/ prec y x;
  wellorder    : ∀V : P X, V ≠ ∅ -> ∃x, V x /\ ∀y, prec y x -> ¬V y;
}.

Arguments prec {_}.
Arguments irreflexive {_}.
Arguments transitive {_}.
Arguments total {_}.
Arguments wellorder {_}.

Notation "x '≺_' A '`' y" := (prec A x y)
  (at level 30, A at next level, format "x  '≺_' A '`'  y").

(* A progressive property of a well-order is universal. *)
Theorem wos_ind X (A : wos X) (V : P X) :
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
Theorem wos_no_infinite_descent X (A : wos X) (f : nat -> X) :
  ¬∀n, f (S n) ≺_A` f n.
Proof.
pose(V x := ∃n, x = f n).
assert(V ≠ ∅) by (apply not_empty; exists (f 0); now exists 0).
apply (wellorder A) in H as [x [[n Hn] Hx]]; subst.
intros H; eapply Hx. apply H. now exists (S n).
Qed.
