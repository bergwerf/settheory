(* Lemmas about binary sequences (the Cantor space). *)

From set_theory Require Import lib fn set seq.

Definition zeros := const false.
Definition ones := const true.

Notation "'C'" := (nat -> bool).
Notation "n >> α" := (shift n false α) (at level 20, format "n >> α").

Lemma cantor_eqn_union_S m α :
  Eqn m α = Eqn (S m) (pre m α zeros) ∪ Eqn (S m) (pre m α ones).
Proof.
apply incl_eq; intros β.
- intros Hβ. destruct (β m) eqn:B. 1: right. 2: left.
  1,2: apply eqn_S. 1,3: eapply eqn_trans.
  1,3: apply eqn_sym, eqn_pre. 1,2: easy.
  1,2: unfold pre, zeros, ones, const; now rewrite ltb_irrefl.
- intros [Hβ|Hβ]; apply eqn_incl with (m:=m) in Hβ.
  1,3: eapply eqn_trans. 1,3: apply eqn_pre. 1,2: apply Hβ. all: lia.
Qed.

(* A surjective enumeration of all prefixes in C using BinPos. *)
Require Import BinPos Pnat.
Section Enumerate_prefixes.

(* Convert prefix to positive number. *)
Fixpoint pre_encode n α :=
  match n with
  | 0 => xH
  | S m =>
    match α 0 with
    | false => xO (pre_encode m (1<<α))
    | true => xI (pre_encode m (1<<α))
    end
  end.

(* Ignore the last bit (xH). *)
Definition pre_size p := pred (Pos.size_nat p).
Definition pre_bit p i := if i <? pre_size p
  then Pos.testbit_nat p i else false.

(* Decode a natural number as a prefix in the Cantor space. *)
Definition pre_decode (n : nat) : nat * C :=
  let p := Pos.of_nat (S n) in (pre_size p, pre_bit p).

Lemma pre_size_xO p : pre_size (xO p) = S (pre_size p).
Proof. unfold pre_size; now destruct p. Qed.

Lemma pre_size_xI p : pre_size (xI p) = S (pre_size p).
Proof. unfold pre_size; now destruct p. Qed.

Lemma ltb_S m n : (S m <? S n) = (m <? n).
Proof. intros; destruct (m <? n) eqn:E; b_lia. Qed.

Lemma pre_size_S p n :
  Pos.size_nat p = S n -> pre_size p = n.
Proof.
unfold pre_size; destruct p; simpl; intros.
1-2: now apply eq_add_S. lia.
Qed.

Lemma pre_size_encode n α :
  pre_size (pre_encode n α) = n.
Proof.
apply pre_size_S.
revert α; induction n; simpl; intros. easy.
destruct (α 0); simpl. all: apply eq_S, IHn.
Qed.

Lemma eqn_pre_bit_encode m α :
  Eqn m α (pre_bit (pre_encode m α)).
Proof.
revert α; induction m; intros. easy. intros i Hi. destruct i.
- simpl; destruct (α 0); unfold pre_bit.
  now rewrite pre_size_xI. now rewrite pre_size_xO.
- apply succ_lt_mono in Hi; apply IHm with (α:=1<<α) in Hi.
  clear IHm. unfold del in Hi at 1; simpl in Hi.
  unfold pre_bit in *; simpl. destruct (α 0); simpl.
  now rewrite pre_size_xI, ltb_S. now rewrite pre_size_xO, ltb_S.
Qed.

Lemma pre_decode_to_nat p :
  pre_decode (pred (Pos.to_nat p)) = (pre_size p, pre_bit p).
Proof.
assert(H := Pos2Nat.is_pos p). destruct (Pos.to_nat p) eqn:E. easy.
unfold pre_decode; now rewrite ?pred_succ, <-E, Pos2Nat.id.
Qed.

Theorem pre_decode_surj m α :
  ∃n, fst (pre_decode n) = m /\ Eqn m α (snd (pre_decode n)).
Proof.
exists (pred (Pos.to_nat (pre_encode m α))).
rewrite pre_decode_to_nat; simpl; split.
apply pre_size_encode. apply eqn_pre_bit_encode.
Qed.

End Enumerate_prefixes.

(* We can order prefixes of the same length. *)
Section Prefix_order.

(* The prefix (m, α) comes before (m, β). *)
Definition PreLt m α β :=
  ∃i, i < m /\ Eqn i α β /\ α i = false /\ β i = true.

Variable X : P C.

(* (m, α) is the smallest non-empty prefix in X at depth m. *)
Definition MinPre m α := Eqn m α ∩ X ≠ ∅ /\
  ∀β, PreLt m β α -> Eqn m β ∩ X = ∅.

(* We can retract the property MinPre. *)
Lemma min_pre_incl m :
  MinPre (S m) ⊆ MinPre m.
Proof.
intros α [H1 H2]; split.
- apply not_empty in H1 as [β [H1β H2β]]; apply not_empty; exists β; split.
  eapply eqn_incl. 2: apply H1β. lia. easy.
- intros β [i [H1i [H2i H3i]]]; apply NNPP; intros Hneg.
  apply not_empty in Hneg as [γ [H1γ H2γ]].
  eapply PNNP. apply H2 with (β:=γ); exists i; repeat split. lia.
  eapply eqn_trans. apply eqn_sym, eqn_incl with (n:=m). lia.
  apply H1γ. easy. now rewrite <-H1γ. easy. apply not_empty; now exists γ.
Qed.

(* A minimal prefix is unique. *)
Lemma min_pre_unique m α β :
  MinPre m α -> MinPre m β -> Eqn m α β.
Proof.
intros Hα Hβ; apply NNPP; intros H.
apply not_all_ex_not in H as [i Hi]; apply imply_to_and in Hi as [H1i H2i].
apply find_first_split in H2i as [n [H1n [H2n H3n]]]. 2: apply bool_dec.
destruct (α n) eqn:A, (β n) eqn:B; try easy; clear H3n; exfalso.
- apply Hβ, Hα. exists n; repeat split; try easy. lia. now apply eqn_sym.
- apply Hα, Hβ. exists n; repeat split; try easy. lia.
Qed.

(* PreLt successor cases. *)
Lemma pre_lt_S m α β :
  PreLt (S m) α β -> PreLt m α β \/
  (Eqn m α β /\ α m = false /\ β m = true).
Proof.
intros [i [H1i [H2i H3i]]]; apply lt_S in H1i as [H|H].
left; now exists i. subst; now right.
Qed.

(* PreLt on a prefix. *)
Lemma pre_lt_pre m α β γ :
  PreLt m α (pre m β γ) -> PreLt m α β.
Proof.
intros [i [H1i [H2i H3i]]]; unfold pre in H3i.
replace (i <? m) with true in H3i by b_lia.
exists i; repeat split; try easy. eapply eqn_trans. apply H2i.
intros j Hj; unfold pre; now replace (j <? m) with true by b_lia.
Qed.

(* A non-empty set has a smallest prefix at every depth. *)
Lemma min_pre_ex m :
  X ≠ ∅ -> ∃α, MinPre m α.
Proof.
intros HX; induction m.
- exists zeros. apply not_empty in HX as [α Hα]; split.
  apply not_empty; now exists α. now intros β [i [Hi _]].
- destruct IHm as [α [H1α H2α]].
  destruct (classic (MinPre (S m) (pre m α ones))).
  now exists (pre m α ones). exists (pre m α zeros); split.
  + apply not_and_or in H as [H|H]. apply NNPP in H. intros Hneg; apply H1α.
    now rewrite cantor_eqn_union_S, isect_distr_union, H, Hneg, union_empty.
    apply not_all_ex_not in H as [β Hβ];
    apply imply_to_and in Hβ as [H1β H2β];
    apply pre_lt_S in H1β as [H1β|H1β].
    * apply pre_lt_pre in H1β; apply H2α in H1β.
      exfalso; apply H2β. eapply incl_empty. 2: apply H1β.
      apply incl_isect_incl, eqn_incl; lia.
    * assert(Eqn (S m) β (pre m α zeros)). {
        apply eqn_S. eapply eqn_trans. apply H1β.
        intros i Hi; unfold pre; now replace (i <? m) with true by b_lia.
        unfold pre; rewrite ltb_irrefl. easy. }
      apply eqn_eq in H; now rewrite <-H.
  + intros β Hβ; apply pre_lt_S in Hβ as [Hβ|Hβ].
    * apply pre_lt_pre in Hβ; apply H2α in Hβ.
      eapply incl_empty. 2: apply Hβ. apply incl_isect_incl, eqn_incl; lia.
    * unfold pre in Hβ; now rewrite ltb_irrefl in Hβ.
Qed.

End Prefix_order.
