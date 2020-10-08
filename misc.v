(* Miscellaneous theorems *)

From set_theory Require Import lib.

(* Prove a property of a function that emulates a transition system. *)
Section Self_extending_state_transition_system.

(* A state transition system *)
Variable State : Type.
Variable Trans : Type.
Variable Value : Type.
Variable step : Trans -> State -> State.
Variable output : State -> Value.

(* The state output value tracks transition symbols. *)
Variable Symbol : Type.
Variable symb : Trans -> Symbol.
Variable push : Symbol -> Value -> Value.
Variable peek : Value -> Symbol.

(* The step function encodes the transition into the state output. *)
Hypothesis step_push : ∀s t, output (step t s) = push (symb t) (output s).
Hypothesis peek_push : ∀a v, peek (push a v) = a.

(* A function which takes a number of steps and outputs a value. *)
Variable f : State -> nat -> Value.

(* State transition used by f. *)
Variable trans : State -> Trans.

(* f computes transitions. *)
Hypothesis f_step : ∀s n, f s (S n) = f (step (trans s) s) n.
Hypothesis f_output : ∀s, f s 0 = output s.

(* f pushes one transition symbol at each successor. *)
Theorem self_extending s n :
  f s (S n) = push (peek (f s (S n))) (f s n).
Proof.
revert s; induction n; intros.
- now rewrite f_step, ?f_output, step_push, peek_push.
- now rewrite f_step, IHn, peek_push, (f_step s).
Qed.

End Self_extending_state_transition_system.
