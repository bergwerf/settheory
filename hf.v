(* ZF model of Hereditarily Finite sets. *)

Require Import lib seq zf.
Require Import List.

Unset Elimination Schemes.
Inductive hf : Type := Create : list hf -> hf.
Set Elimination Schemes.

Notation "⟨ l ⟩" := (Create l) (format "⟨ l ⟩").

(* From: https://stackoverflow.com/questions/46838928/#46840045 *)
Section Induction_in_hf.

Variable P : hf -> Prop.
Definition list_and := fold_right (λ x, and (P x)) True.
Hypothesis IH : ∀el, list_and el -> P ⟨el⟩.

Fixpoint hf_ind (x : hf) : P x :=
  match x with
  | ⟨el⟩ =>
    let fix loop el :=
      match el return list_and el with
      | nil => I
      | y :: el' => conj (hf_ind y) (loop el')
      end in
    IH el (loop el)
  end.

End Induction_in_hf.

Arguments forallb {_}.
Arguments existsb {_}.

Definition elements (x : hf) :=
  match x with
  | ⟨el⟩ => el
  end.

Fixpoint hf_eq (x y : hf) {struct x} :=
  match x, y with
  | ⟨xe⟩, ⟨ye⟩ =>
    let xincl := forallb (λ x', existsb (λ y', hf_eq x' y') ye) xe in
    let yincl := forallb (λ y', existsb (λ x', hf_eq x' y') xe) ye in
    xincl && yincl
  end.

Definition hf_in (x y : hf) := existsb (hf_eq x) (elements y).

Definition HF : model hf :=
  (λ x y, hf_eq x y = true,
   λ x y, hf_in x y = true).

Theorem hf_realizes_pairing :
  HF |= Axiom_of_pairing.
Proof.
intro_var x; intro_var y.
pose(p := ⟨x :: y :: nil⟩); exists p.
intro_var z; apply iff_intro; split; intros.
- apply disj_intro; simpl in H.
  unfold hf_in in H; simpl in H; b_Prop; try easy.
  now left. now right.
- simpl; unfold hf_in; simpl.
  apply disj_elim in H as [H|H]; simpl in H; rewrite H; simpl.
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
intro_var a'; destruct a' as [a'].
pose(spec e := HF |= (φ)[Γ;x:=↓e]).
destruct (list_specification a' spec) as [b' Hb'].
exists ⟨b'⟩; intro_var e; apply iff_intro; split; intros.
Abort.
