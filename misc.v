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

(* The output value for a state tracks transition symbols. *)
Variable Symbol : Type.
Variable symb : Trans -> Symbol.
Variable push : Symbol -> Value -> Value.
Variable pop : Value -> Symbol.

(* The step function encodes the transition into the state output. *)
Hypothesis step_push : ∀s t, output (step t s) = push (symb t) (output s).
Hypothesis push_pop : ∀a v, pop (push a v) = a.

(* A function which takes a number of steps and outputs a value. *)
Variable f : State -> nat -> Value.

(* The function follows state transitions. *)
Hypothesis f_step : ∀s n, ∃t, f s (S n) = f (step t s) n.
Hypothesis f_output : ∀s, f s 0 = output s.

Theorem self_extending s n :
  f s (S n) = push (pop (f s (S n))) (f s n).
Proof.
Admitted.

End Self_extending_state_transition_system.
