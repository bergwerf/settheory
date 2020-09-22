(* The Cantor-Schröder-Bernstein theorem *)

From set_theory Require Import lib fn.

Theorem CSB {A B} (f : A -> B) (g : B -> A) :
  Injective f -> Injective g -> ∃h : A -> B, Bijective h.
Proof.
(*
B 0     := B ⧵ Rng f
A n     := g (B n)
B (n+1) := f (A n)
h       := { (a, f a) | ∃n, a ∈ A n } ∪ { (g(b), b) | ∃n, b ∈ B n }
*)
Abort.
