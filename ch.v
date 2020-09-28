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

(*
An idea from intuitionism that is quite useful here is to consider X as a law σ
that accepts or rejects prefixes (a finitary spread). Given such a law we can
construct another law that represents the embedding of C in X, and then prove
its correctness constructively. We prove this for any set defined by a law that
satisfies the split hypothesis (any prefix splits at some point).
*)
Section Finitary_spread.

(* We use nat * C instead of list bool to simplify proofs. *)
Variable σ : nat * C -> bool.

(* σ is only determined by the prefix (well-defined). *)
Hypothesis σ_wd : ∀m α β, Branch m α β -> σ (m, α) = σ (m, β).

(* X is inhabited. *)
Hypothesis σ_law0 : ∀α, σ (0, α) = true.

(* A prefix is accepted iff a continuation is accepted. *)
Hypothesis σ_law1 : ∀m α, σ (m, α) = true <->
  ∃β, Branch m α β /\ σ (S m, β) = true.

(* Every prefix has two different continuations (eventually splits). *)
Hypothesis σ_split : ∀m α, σ (m, α) = true -> ∃n β,
  m <= n /\ Branch m α β /\
  σ (S n, pre n β zeros) = true /\
  σ (S n, pre n β ones) = true.

(*
(m, β) := current prefix in X
α := input sequence in C
i := index in the image of α
*)
Fixpoint embedding m β α i :=
  (* Check which directions are free. *)
  let β0 := pre m β zeros in
  let β1 := pre m β ones in
  let b0 := σ (S m, β0) in
  let b1 := σ (S m, β1) in
  (* Check if we have reached the image index. *)
  match i with
  | 0 => if b0 && b1 then (α 0) else b1
  | S j =>
    (* If two continuations are possible, then follow α. *)
    match b0, b1 with
    | true, true =>
      match α 0 with
      | false      => embedding (S m) β0 (del 1 α) j
      | true       => embedding (S m) β1 (del 1 α) j
      end
    | true, false  => embedding (S m) β0 α j
    | false, true  => embedding (S m) β1 α j
    | _, _         => false (* (m, β) cannot be continued *)
    end
  end.

Definition embedding' := embedding 0 zeros.

(* σ accepts any prefix of an embedding. *)
Theorem embedding_σ m α :
  σ (m, embedding' α) = true.
Proof.
induction m. apply σ_law0.
apply σ_law1 in IHm as [β [H1β H2β]].
assert(∀γ, embedding' α m = γ m -> Branch (S m) (embedding' α) (pre m β γ)). {
  intros; apply Branch_S. eapply Branch_trans. apply H1β.
  apply Branch_pre. unfold pre; now rewrite ltb_irrefl. }
pose(β0 := pre m β zeros); pose(β1 := pre m β ones);
destruct (σ (S m, β0)) eqn:b0, (σ (S m, β1)) eqn:b1.
- destruct (α 0) eqn:E.
+ rewrite σ_wd with (β:=β1). easy. apply H. admit.
+ rewrite σ_wd with (β:=β0). easy. apply H. admit.
- rewrite σ_wd with (β:=β0). easy. apply H. admit.
- rewrite σ_wd with (β:=β1). easy. apply H. admit.
- exfalso; destruct (β m) eqn:b.
  + rewrite σ_wd with (β:=β1) in H2β.
    now rewrite b1 in H2β. apply Branch_S. apply Branch_pre.
    now unfold β1, pre; rewrite ltb_irrefl.
  + rewrite σ_wd with (β:=β0) in H2β.
    now rewrite b0 in H2β. apply Branch_S. apply Branch_pre.
    now unfold β0, pre; rewrite ltb_irrefl.
Admitted.

(* The embedding is injective. *)
Theorem embedding_inj α1 α2 i n β :
  α1 i ≠ α2 i -> ∃j, embedding n β α1 j ≠ embedding n β α2 j.
Proof.
Admitted.

End Finitary_spread.

(* Obtain a law for X using AC, and use the above construction. *)
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
