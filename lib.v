(* All external imports and some generic tools *)

(* Convenience *)
Require Export Lia.          (* Linear Integer Arithmetic tactic *)
Require Export Utf8.         (* Unicode notations *)
Require Export Compare_dec.  (* Decidable relations *)

(* Definitions *)
Require Export Basics.       (* Some basic combinators *)
Require Export Combinators.  (* Proofs about combinators *)
Require Export PeanoNat.     (* Peano arithmetic *)

(* Logic *)
Require Export Classical.
Require Export ClassicalChoice.
Require Export PropExtensionality.
Require Export FunctionalExtensionality.

(* Import some theorems into the global namespace. *)
Export Nat.
Export Bool.

(*
To denote indices I prefer using: n, m, i, j, k (in that order). One exception
is sequences of the type nat -> T where T : Set because I use n and m to denote
prefixes of such sequences.
*)

(* Convert boolean arithmetic relations to Prop. *)
Ltac bool_to_Prop :=
  match goal with
  | [H : _ && _ = true |- _] =>
    let P := fresh H in (apply andb_prop in H as [P H])
  | [H : _ =? _ = true |- _]   => apply eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply leb_le in H
  | [H : _ <=? _ = false |- _] => apply leb_gt in H
  | [H : _ <? _ = true |- _]   => apply ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply ltb_ge in H
  | |- (_ && _ = true)   => apply andb_true_intro; split
  | |- (_ =? _ = true)   => apply eqb_eq
  | |- (_ =? _ = false)  => apply eqb_neq
  | |- (_ <=? _ = true)  => apply leb_le
  | |- (_ <=? _ = false) => apply leb_gt
  | |- (_ <? _ = true)   => apply ltb_lt
  | |- (_ <? _ = false)  => apply ltb_ge
  | _ => idtac
  end.

Ltac b_Prop := repeat bool_to_Prop.
Ltac b_lia := b_Prop; try (symmetry; b_Prop); lia.
