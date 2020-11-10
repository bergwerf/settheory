(* Cantor's pairing function. *)

From set_theory Require Import lib fn.

(* Quadratic form of Cantors pairing function *)
Definition π (k : nat * nat) :=
  let k1 := fst k in
  let k2 := snd k in
  div2 ((k1 + k2) * (k1 + k2 + 1)) + k2.

(* Step mapping *)
Definition π_step (k : nat * nat) : nat * nat :=
  match k with
  | (0, y) => (S y, 0)
  | (S x, y) => (x, S y)
  end.

(* Compute stepped inversion of π. *)
Definition π_inv n := (π_step ↑ n) (0, 0).

Example π_47_32 : π (47, 32) = 3192.
Proof. now lazy. Qed.

Example π_inv_3192 : π_inv 3192 = (47, 32).
Proof. now lazy. Qed.

Lemma π_inv_succ n : π_inv (S n) = π_step (π_inv n).
Proof. easy. Qed.

Lemma π_steps_diagonal k1 k2 n :
  π_inv n = (k1, 0) -> k2 <= k1 -> π_inv (n + k2) = (k1 - k2, k2).
Proof.
unfold π_inv. induction k2; intros.
now rewrite add_0_r, sub_0_r.
apply IHk2 in H. rewrite add_succ_r; simpl. rewrite H.
destruct k1. lia. rewrite sub_succ_l; simpl. easy. all: lia.
Qed.

Lemma π_steps_axis k1 :
  ∃n, π_inv n = (k1, 0).
Proof.
induction k1. now exists 0.
destruct IHk1 as [m Hm]. exists (S (m + k1)).
erewrite π_inv_succ, π_steps_diagonal. 2: apply Hm.
rewrite sub_diag. all: easy.
Qed.

(* π_inv ranges over the entire set of pairs. *)
Theorem π_steps_range k :
  ∃n, π_inv n = k.
Proof.
destruct k as [k1 k2]. destruct (π_steps_axis (k1 + k2)) as [n Hn].
exists (n + k2). erewrite π_steps_diagonal. 2: apply Hn.
now rewrite add_sub. lia.
Qed.

Lemma div2_cancel m n :
  div2 (m + n * 2) = div2 m + n.
Proof.
rewrite div2_div, div_add, <-div2_div. all: easy.
Qed.

(* π is the inverse of π_inv. *)
Theorem π_π_inv_id n :
  π (π_inv n) = n.
Proof.
unfold π_inv. induction n. easy. simpl.
remember ((π_step ↑ n) (0, 0)) as k. rewrite <-IHn.
destruct k as [k0 k1], k0, k1; unfold π; simpl; rewrite ?add_0_r. easy.
(* Simplify div2 match. *)
1: replace (k1 + 1 + k1 * S (k1 + 1))
      with (S (k1*k1 + 3*k1)) by lia.
2: replace (k0 + 1 + k0 * S (k0 + 1))
      with (S (k0*k0 + 3*k0)) by lia.
3: replace (k0 + S k1 + 1 + (k0 + S k1) * S (k0 + S k1 + 1))
      with (S (k0*k0 + k1*k1 + 2*k0*k1 + 5*k0 + 5*k1 + 2*2)) by lia.
(* Simplify other side *)
1: replace (k1 + 1 + S (S (k1 + 1 + k1 * S (S (k1 + 1)))))
      with (k1 * k1 + 3 * k1 + (k1 + 2)*2) by lia.
2: replace ((k0 + 1) * (k0 + 1 + 1))
      with (k0*k0 + 3*k0 + 1*2) by lia.
3: replace ((k0 + S (S k1)) * (k0 + S (S k1) + 1))
      with (k0*k0 + k1*k1 + 2*k0*k1 + 5*k0 + 5*k1 + 3*2) by lia.
(* Simplify div2 and finish. *)
all: rewrite ?div2_cancel; lia.
Qed.

(* π_inv is the inverse of π. *)
Corollary π_inv_π_id k :
  π_inv (π k) = k.
Proof.
destruct (π_steps_range k).
now rewrite <-H, π_π_inv_id.
Qed.

Corollary π_bijective : Bijective π.
Proof. exists π_inv; split. apply π_inv_π_id. apply π_π_inv_id. Qed.

Corollary π_inv_bijective : Bijective π_inv.
Proof. exists π; split. apply π_π_inv_id. apply π_inv_π_id. Qed.
