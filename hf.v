(* ZF model of Hereditarily Finite sets. *)

Require Import lib seq zf.

Unset Elimination Schemes.
Inductive hf : Type := HFSet : list hf -> hf.
Set Elimination Schemes.

(* From: https://stackoverflow.com/questions/46838928/#46840045 *)
Section Induction_in_hf.

Variable P : hf -> Prop.
Hypothesis IH : ∀el, Forall P el -> P (HFSet el).

Fixpoint hf_ind (x : hf) : P x :=
  match x with
  | HFSet el =>
    let fix loop el :=
      match el return Forall P el with
      | nil => @Forall_nil hf P
      | e :: etl => @Forall_cons hf P e etl (hf_ind e) (loop etl)
      end in
    IH el (loop el)
  end.

End Induction_in_hf.

Arguments forallb {_}.
Arguments existsb {_}.

Definition elements (x : hf) :=
  match x with
  | HFSet el => el
  end.

Fixpoint hf_eqb (x y : hf) {struct x} :=
  match x, y with
  | HFSet xe, HFSet ye =>
    let xincl := forallb (λ x', existsb (λ y', hf_eqb x' y') ye) xe in
    let yincl := forallb (λ y', existsb (λ x', hf_eqb x' y') xe) ye in
    xincl && yincl
  end.

Definition hf_inb (x y : hf) := existsb (hf_eqb x) (elements y).
Definition hf_eq x y := hf_eqb x y = true.
Definition hf_in x y := hf_inb x y = true.
Definition HF : model hf := (hf_eq, hf_in).

Instance hf_eq_equivalence :
  Equivalence hf_eq.
Proof.
unfold hf_eq; repeat split.
- intros x; induction x; simpl; b_Prop.
  all: apply forallb_forall; intros; apply existsb_exists.
  all: exists x; split; try easy.
  all: now apply Forall_forall with (x:=x) in H.
- intros x; induction x; intros [l].
  simpl; intros; b_Prop; intros.
  all: apply forallb_forall; intros; apply existsb_exists.
  all: eapply forallb_forall in H2 as H3. 2: apply H1. 3: apply H0.
  all: apply existsb_exists in H3 as [y [H4 H5]].
  all: exists y; split; try easy.
  1: eapply Forall_forall in H4 as IH.
  3: eapply Forall_forall in H2 as IH.
  2,4: apply H. all: now apply IH.
- intros x; induction x; intros [el1] [el2]; simpl; intros; b_Prop.
  all: apply forallb_forall; intros; apply existsb_exists.
  all: eapply forallb_forall in H4 as H5. 2: apply H0. 3: apply H2.
  all: apply existsb_exists in H5 as [y [H6 H7]].
  all: eapply forallb_forall in H6. 2: apply H1. 3: apply H3.
  all: apply existsb_exists in H6 as [z [H8 H9]].
  all: exists z; split; try easy.
  1: eapply Forall_forall in H4 as IH.
  3: eapply Forall_forall in H8 as IH.
  2,4: apply H. all: now apply IH with (y:=y).
Qed.

Theorem hf_realizes_pairing :
  HF |= Axiom_of_pairing.
Proof.
fintro x; fintro y.
pose(p := HFSet (x :: y :: nil)); exists p.
fintro z; apply iff_intro; split; intros.
- apply disj_intro; simpl in H.
  unfold hf_in, hf_inb in H; simpl in H.
  b_Prop; try easy; simpl; auto.
- simpl; unfold hf_in, hf_inb; simpl.
  apply disj_elim in H as [H|H]; simpl in H;
  unfold hf_eq in H; rewrite H; simpl.
  easy. now rewrite orb_true_r.
Qed.

Theorem list_specification {T} (l : list T) P :
  ∃l', ∀x, In x l' <-> In x l /\ P x.
Proof.
induction l. now exists nil.
destruct IHl as [l' IH], (classic (P a)).
- exists (a :: l'); split.
  + intros [Ha|Ha]; subst. split. apply in_eq. easy.
    apply IH in Ha; split. now apply in_cons. easy.
  + intros [[Ha|Ha] Hx]; subst.
    apply in_eq. now apply in_cons, IH.
- exists l'; split.
  intros Hx; apply IH in Hx. split. now apply in_cons. easy.
  intros [[Ha|Ha] Hx]; subst. easy. now apply IH.
Qed.

Theorem hf_realizes_specification ϕ :
  Schema_of_specification ϕ -> HF |= ϕ.
Proof.
intros [φ [Hϕ def]]; subst; unfold Axiom_of_specification.
remember (fvar φ - 1) as x; remember (fresh φ) as a; remember (S a) as b.
apply closure_intro; intros; remember (pre x Δ Γ0) as Γ.
fintro a'; destruct a' as [a'].
pose(spec e := HF |= (φ)[Γ;x:=↓e]).
destruct (list_specification a' spec) as [b' Hb'].
exists (HFSet b'); fintro e; apply iff_intro; split; intros.
Abort.

Theorem hf_realizes_zf_finite φ :
  ZF_finite φ -> HF |= φ.
Proof.
Abort.
