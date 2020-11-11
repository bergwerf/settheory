(* The Well-Ordering Theorem of E. Zermelo. *)

From set_theory Require Import lib fn set wo.

Section Well_ordering_theorem.

Variable X : Type.
Variable f : P X -> X.

(* f is a choice function for X. *)
Hypothesis f_choice : ∀V, V (f V).

(* Define a notation for sigma sub-sets of X. *)
Notation "& U" := ({x : X | U x}) (at level 5, format "& U").

(* Define the notion 'X without the initial segment A↾x' *)
Definition after {U : P X} {_0} (A : wos &U _0) x y :=
  ¬∃y', y = sig1 y' /\ y' <_0` x.

(* Define the notion 'f well-ordening'. *)
Definition f_wo {U : P X} {_0} (A : wos &U _0) :=
  ∀x : &U, sig1 x = f (after A x).

(* Define all subsets of X with an f well-ordering. *)
Definition W V := ∃R, ∃A : wos &V R, f_wo A.

Lemma f_wo_iso U V {_0 _1} (A : wos &U _0) (B : wos &V _1) g :
  f_wo A -> f_wo B -> WOSIsomorphism A B g -> ∀x, sig1 (g x) = sig1 x.
Proof.
intros fA fB [[g_inv [_ g_bi]] g_iso]; apply (wos_ind A); intros x IH.
rewrite fA, fB. replace (after A x) with (after B (g x)). easy.
extensionality y; apply propositional_extensionality.
split; apply contra; intros [z [H1z H2z]].
- apply g_iso in H2z as H3z; apply IH in H2z.
  destruct (g z) as [z' Hz']; simpl in *; subst.
  now exists (exist (sig1 z) Hz').
- rewrite <-g_bi in H2z at 1; apply g_iso in H2z.
  apply IH in H2z as H3z; rewrite g_bi in H3z.
  destruct (g_inv z) as [z' Hz']; simpl in *; subst.
  now exists (exist (sig1 z) Hz').
Qed.

Lemma f_wo_incl U V {_0 _1} (A : wos &U _0) (B : wos &V _1) :
  f_wo A -> f_wo B -> U ⊆ V \/ V ⊆ U.
Proof.
Abort.

Theorem WOT :
  ∃R, wos X R.
Proof.
Abort.

End Well_ordering_theorem.
