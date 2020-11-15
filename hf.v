(* ZF model of Hereditarily Finite sets. *)

Require Import lib seq zf.
Require Import List.
Import ListNotations.

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
      | [] => I
      | y :: elm' => conj (hf_ind y) (loop elm')
      end in
    IH elm (loop elm)
  end.

End Induction_in_hf.

Arguments forallb {_}.
Arguments existsb {_}.

Fixpoint hf_eq (x y : hf) {struct x} :=
  match x, y with
  | Create xe, Create ye =>
    let xincl := forallb (λ x', existsb (λ y', hf_eq x' y') ye) xe in
    let yincl := forallb (λ y', existsb (λ x', hf_eq x' y') xe) ye in
    xincl && yincl
  end.

Definition hf_in (x y : hf) :=
  match y with
  | Create elm => existsb (hf_eq x) elm
  end.

Definition HF : model hf :=
  (λ x y, Is_true (hf_eq x y),
   λ x y, Is_true (hf_in x y)).
