(* A proof that the continuum hypothesis holds for closed sets. *)

From set_theory Require Import lib fn pair bin set d cb.

(*
First we will see that it is possible to embed the Cantor space into any
non-empty, perfect subset of the Cantor space (this generalizes to other
topologies such as the real numbers).
*)
Section Perfect_embedding.

Variable X : P C.
Hypothesis nonempty_X : X ≠ ∅.
Hypothesis closed_X : Closed X.
Hypothesis perfect_X : Perfect X.

(* The set X ⊆ C embeds C if a one-to-one function f : C -> X exists. *)
Definition EmbedsC := ∃f : C -> C, (∀α, X (f α)) /\ Injective f.

(*
The first approach I thought of is using an inductive predicate to represent
prefix embeddings. But it turned out a much easier and more intuitive approach
is possible. The main problem with the prefix embedding predicate presented
below is that it is not canonical. One possible solution is to exploit the fact
that a closed and perfect set X always contains its own infimum and supremum,
this yields a canonical split under every branch.
*)
Section Embedding_predicate.

(*
We define an inductive predicate which determines a valid prefix in X to map any
given prefix in C to. A construction of [prefix_embedding (m, α) (n, β)] means
that the prefix (m, α) embeds into X using the prefix (n, β). The constrution
still allows many different prefix embeddings, so additional requirements are
needed to obtain a canonical embedding.
*)
Inductive prefix_embedding : nat * C -> nat * C -> Prop :=
  (* We inductively search for divisions, so β must be an element of X. *)
  | prefix_embedding_0 : ∀α β, X β -> prefix_embedding (0, α) (0, β)
  (* To add one boolean to the prefix, we have to look for a division in X. *)
  | prefix_embedding_S : ∀m α n β k γ γ',
    (* γ, γ' ∈ X *)
    X γ -> X γ' ->
    (* γ and γ' belong to the (n + k)-th branch of β. *)
    Branch (n + k) β γ -> Branch (n + k) β γ' ->
    (* γ and γ' part at n + k, and γ goes in the direction of α at m. *)
    γ (n + k) ≠ γ' (n + k) -> γ (n + k) = α m ->
    (* (n, β) is a prefix embedding of (m, α). *)
    prefix_embedding (m, α) (n, β) ->
    (* Then (n + k, γ) is a prefix embedding of (1 + m, α). *)
    prefix_embedding (S m, α) (n + k, γ).

(* Every embedding is in X. *)
Lemma prefix_embedding_in_X m α n β : prefix_embedding (m, α) (n, β) -> X β.
Proof. intros H; now inversion H. Qed.

(* Every prefix can be embedded. *)
Lemma prefix_embedding_ex :
  ∀s_dom, ∃s_img, prefix_embedding s_dom s_img.
Proof.
intros [m α]; induction m.
- apply not_empty in nonempty_X as [β Hβ]; exists (0, β).
  now apply prefix_embedding_0.
- destruct IHm as [[n β] H1β]. apply prefix_embedding_in_X in H1β as H2β.
  (* Find a second element in Branch n β, and find where it splits from β. *)
  apply perfect_X in H2β as H3β. destruct (H3β n) as [γ [H1γ [H2γ H3γ]]].
  apply neq_least_shared_branch in H1γ as [k [H1k H2k]].
  assert(H1n : n <= k). { apply not_gt; intros H. now apply H3γ in H. }
  assert(H2n : n + (k - n) = k) by lia.
  (* Choose between β and γ based on α(m). *)
  destruct (bool_dec (α m) (β k)).
  + exists ((n + (k - n)), β); apply prefix_embedding_S
    with (β:=β)(γ:=β)(γ':=γ); rewrite ?H2n; try easy.
  + exists ((n + (k - n)), γ); apply prefix_embedding_S
    with (β:=β)(γ:=γ)(γ':=β); rewrite ?H2n; try easy.
    now apply not_eq_sym. now destruct (α m), (β k), (γ k).
Qed.

End Embedding_predicate.

(* Materialize the postulated function using AC. *)
Theorem nonempty_closed_perfect_embeds_C :
  EmbedsC.
Proof.
Admitted.

End Perfect_embedding.

(*
We can now prove the continuum hypothesis (CH) for closed sets. With closed sets
we can exploit a hierarchy of derived sets given by the Cantor-Bendixon
derivatives. Open sets are trickier because a countable open set may contain
uncountably many limit points. (Take for example all finite sequences prepended
to zeros. This is similar to the rational numbers which approach all real
numbers.)
*)
Section Continuum_hypothesis.

(* Every infinite set X is either countable or embeds C. *)
Definition CH X := Infinite X -> Countable X \/ EmbedsC X.

(* CH holds for closed sets. *)
Theorem closed_continuum_hypothesis X :
  Closed X -> CH X.
Proof.
destruct (classic (K X = ∅)).
- left. rewrite <-diff_empty, <-H. now apply CB_countable_diff, CB_K.
- right. apply nonempty_closed_perfect_embeds_C in H as [f [H1f H2f]].
  exists f; split. intros; eapply CB_incl. easy. now apply CB_K.
  easy. easy. apply CB_closed with (X:=X). easy. now apply CB_K.
  now apply CB_K_perfect.
Qed.

End Continuum_hypothesis.
