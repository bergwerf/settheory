(* ZF model of Hereditarily Finite sets. *)

Require Import lib seq zf.
Require Import List.

Unset Elimination Schemes.
Inductive hf : Type := Create : list hf -> hf.
Set Elimination Schemes.

(* From: https://stackoverflow.com/questions/46838928/#46840045 *)
Section Induction_in_hf.

Variable P : hf -> Prop.
Definition list_and := fold_right (λ x, and (P x)) True.
Hypothesis IH : ∀elm, list_and elm -> P (Create elm).

Fixpoint hf_ind (x : hf) : P x :=
  match x with
  | Create elm =>
    let fix loop elm :=
      match elm return list_and elm with
      | nil => I
      | y :: elm' => conj (hf_ind y) (loop elm')
      end in
    IH elm (loop elm)
  end.

End Induction_in_hf.

Arguments forallb {_}.
Arguments existsb {_}.

Definition elements (x : hf) :=
  match x with
  | Create elm => elm
  end.

Fixpoint hf_eq (x y : hf) {struct x} :=
  match x, y with
  | Create xe, Create ye =>
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
pose(p := Create (x :: y :: nil)); exists p.
intro_var z; apply iff_intro; split; intros.
- apply disj_intro; simpl in H.
  unfold hf_in in H; simpl in H; b_Prop; try easy.
  now left. now right.
- simpl; unfold hf_in; simpl.
  apply disj_elim in H as [H|H]; simpl in H; rewrite H; simpl.
  easy. now rewrite orb_true_r.
Qed.
