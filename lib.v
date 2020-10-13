(* All external imports and some generic tools *)

(* Convenience *)
Require Export Lia.          (* Linear Integer Arithmetic tactic *)
Require Export Utf8.         (* Unicode notations *)
Require Export Compare_dec.  (* Decidable relations *)

(* Definitions *)
Require Export PeanoNat.     (* Peano arithmetic *)

(* Logic *)
Require Export Classical.
Require Export ClassicalChoice.
Require Export PropExtensionality.
Require Export FunctionalExtensionality.

(* Import some theorems into the global namespace. *)
Export Nat.
Export Bool.

(* Some global notations. *)
Notation "'∃!' x .. y , P" := (exists! x, .. (exists! y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' '∃!' x .. y ']' , '/'  P ']'") : type_scope.

(* Basic laws of logic that are absent in Coq's library. *)
Section Logic.

Variable P : Prop.
Variable Q : Prop.

Theorem contra : (P -> Q) -> ¬Q -> ¬P.
Proof. auto. Qed.

Theorem classic_contra : (¬Q -> ¬P) -> P -> Q.
Proof. intros; destruct (classic Q). easy. now apply H in H1. Qed.

End Logic.

(*
Naming conventions
------------------
To denote indices I prefer using: n, m, i, j, k (in that order). One exception
is sequences of the type nat -> T where T : Set because I use n and m to denote
prefixes of such sequences. I prefer writing function and theorem labels fully
in small caps, and to start propositions with an uppercase letter.

The names of theorems do not follow a consistent convention (although I try to
stick to logical patterns). If a theorem states a fundamental property of one
specific definition, then the name of that definition is usually written first
(for example `f_inj` for the injective property of f). If a theorem states a
property of a combination of definitions, then the names of those definitions
are usually written in the same order as in the theorem statement (for example
`countable_union` to denote that a union of countable sets is also countable).
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
