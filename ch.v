(* A proof that the continuum hypothesis holds for closed sets. *)

From set_theory Require Import lib ts fn pair set seq bin d cb.

(* We use lists exclusively for the embedding proof. *)
Require Import List.
Import ListNotations.

(*
First we will see that it is possible to embed the Cantor space into any
non-empty, perfect subset of the Cantor space (this generalizes to other
topologies such as the real numbers). The intuitive idea behind this proof is
easy, but it turns out to be one of the most difficult parts to formalize. The
main difficulty is constructing an embedding for every prefix that follows some
rules (self-extending, contained in the image set, injective).
*)
Section Perfect_embedding.

Variable X : P C.
Hypothesis nonempty_X : X ≠ ∅.
Hypothesis closed_X : Closed X.
Hypothesis perfect_X : Perfect X.

(* The set X ⊆ C embeds C if a one-to-one function f : C -> X exists. *)
Definition EmbedsC := ∃f : C -> C, (∀α, X (f α)) /\ Injective f.

(*
An idea from intuitionism that is quite useful here is to consider X as a law σ
that accepts or rejects prefixes. Given such a law we can construct prefixes in
σ for any α : C, and then prove their correctness constructively. Later we use
AC to obtain such a 'spread law' σ for X.
Note that the embedding function Cσ is actually a state transition system
wrapped into one function (we need this insight to prove Cσ_self_extending). It
could be more elegant/efficient to generalize parts of the proof by looking at
state transition systems.
*)
Section Finitary_spread.

Notation "b ⊕ c" := (xorb b c) (at level 20).

(* Spread law. *)
Variable σ : list bool -> bool.

Definition σ_1way s := σ (false :: s) ⊕ σ (true :: s).
Definition σ_2way s := σ (false :: s) && σ (true :: s).

(* A prefix is accepted iff a continuation is accepted. *)
Hypothesis σ_cont : ∀s, σ s = true <-> ∃b, σ (b :: s) = true.

(* Every prefix has two different continuations (eventually splits). *)
Hypothesis σ_split : ∀s, σ s = true -> ∃t, σ_2way (t ++ s) = true.

(*
Prefix embedding of C generated by σ.
s := starting prefix in σ
α := input sequence in C
n := length of output prefix in σ
*)
Fixpoint Cσ s α n :=
  match n with
  | 0 => s
  | S m =>
  if σ_2way s
  then Cσ (α 0 :: s) (1<<α) m
  else Cσ (σ (true :: s) :: s) α m
  end.

(* There are n 1-way points after s. *)
Definition Cσ_1way s α n := ∀m, m < n -> σ_1way (Cσ s α m) = true.

(* Get the nth value of Cσ s α. *)
Definition nth_Cσ s α n := hd false (Cσ s α (S n)).

(* Get nth item of reversed list (so the head is at length s). *)
Definition nth_rev s i := nth i (rev s) false.

(* PART I: nth_Cσ is similar to nth_rev. *)
Section Part_I.

(* Stepping function beloning to Cσ. *)
Definition Cσ_step (b : bool) n s (α : C) := (b :: s, n<<α).

(* State transition function belonging to Cσ. *)
Definition Cσ_trans s α := if σ_2way s then (α 0, 1) else (σ (true :: s), 0).

Theorem Cσ_self_extending d s α n :
  Cσ s α (S n) = hd d (Cσ s α (S n)) :: Cσ s α n.
Proof.
pose(c st i := Cσ (fst st) (snd st) i).
pose(step t st := Cσ_step (fst t) (snd t) (fst st) (snd st)).
pose(trans st := Cσ_trans (fst st) (snd st)).
assert(Hc : ∀s α i, Cσ s α i = c (s, α) i) by (now unfold c); rewrite ?Hc.
apply self_extending with (output:=fst)(symb:=fst)(step:=step)(trans:=trans);
clear s α n; unfold step, Cσ_step, trans, Cσ_trans; simpl; intros; try easy.
destruct s as [s α]; unfold c; simpl. now destruct (σ_2way s).
Qed.

Lemma Cσ_length s α n :
  length (Cσ s α n) = length s + n.
Proof.
revert s α; induction n; intros; simpl. now rewrite add_0_r.
destruct (σ_2way s); rewrite IHn; simpl; lia.
Qed.

Lemma nth_rev_cases b s i :
  i < S (length s) ->
  i < length s /\ nth_rev (b :: s) i = nth_rev s i \/
  i = length s /\ nth_rev (b :: s) i = b.
Proof.
intros; unfold nth_rev; simpl. destruct (eq_dec i (length s)).
- right; split. easy. rewrite app_nth2, rev_length, <-e, sub_diag. easy.
  rewrite rev_length; lia.
- left; split. lia. rewrite app_nth1. easy.
  rewrite rev_length; lia.
Qed.

(* nth_Cσ is the same as nth_rev of a prefix given by Cσ. *)
Theorem nth_Cσ_eq_nth_rev m α :
  Branch m (nth_Cσ [] α) (nth_rev (Cσ [] α m)).
Proof.
induction m; intros. easy.
rewrite Cσ_self_extending with (d:=false). intros i Hi.
assert(Hm : m = length (Cσ [] α m)) by (now rewrite Cσ_length).
rewrite Hm in Hi; eapply nth_rev_cases in Hi as [[H1 H2]|[H1 H2]]; rewrite H2.
apply IHm; now rewrite Hm. rewrite <-Hm in H1; now subst.
Qed.

End Part_I.

(* Part II: σ accepts prefixes of Cσ and Cσ is injective. *)
Section Part_II.

Lemma xorb_split b c : b ⊕ c = true -> b = true \/ c = true.
Proof. destruct b, c; auto. Qed.

Lemma xorb_l b c : b ⊕ c = true -> b = true <-> c = false.
Proof. now destruct b, c. Qed.

Lemma σ_cons b s : σ (b :: s) = true -> σ s = true.
Proof. intros; apply σ_cont; now exists b. Qed.

Lemma σ_app s t : σ (s ++ t) = true -> σ t = true.
Proof. induction s; simpl; intros. easy. eapply IHs, σ_cons, H. Qed.

Lemma σ_1way_inv s : σ_1way s = true -> σ s = true.
Proof. intros H; apply xorb_split in H as [H|H]; eapply σ_cons, H. Qed.

Lemma σ_2way_cons s b : σ_2way s = true -> σ (b :: s) = true.
Proof. unfold σ_2way; intros; b_Prop; now destruct b. Qed.

Lemma σ_2way_inv s : σ_2way s = true -> σ s = true.
Proof. intros; eapply σ_cons with (b:=false), σ_2way_cons, H. Qed.

Lemma σ_1way_cons a s :
  σ_1way s = true -> σ (a :: s) = true -> σ (true :: s) = a.
Proof.
intros; destruct a. easy.
eapply xorb_l. apply H. easy.
Qed.

Lemma σ_12way s :
  σ s = true -> σ_1way s ⊕ σ_2way s = true.
Proof.
unfold σ_1way, σ_2way.
destruct (σ (false :: s)) eqn:F, (σ (true :: s)) eqn:T; try easy.
intros H; exfalso. apply σ_cont in H as [b Hb]; destruct b.
now rewrite T in Hb. now rewrite F in Hb.
Qed.

Lemma σ_cons_true s :
  σ s = true -> σ (σ (true :: s) :: s) = true.
Proof.
intros; destruct (σ (true :: s)) eqn:E. easy.
eapply xorb_l. eapply xorb_l. apply σ_12way.
easy. unfold σ_2way; now rewrite E, andb_false_r. easy.
Qed.

Lemma Cσ_S s α n :
  σ_1way s = true -> Cσ s α (S n) = Cσ (σ (true :: s) :: s) α n.
Proof.
intros; simpl. replace (σ_2way s) with false. easy.
symmetry; eapply xorb_l. apply σ_12way. apply σ_1way_inv, H. easy.
Qed.

(* σ accepts every prefix computed by Cσ. *)
Theorem Cσ_accepted s α n :
  σ s = true -> σ (Cσ s α n) = true.
Proof.
revert s α; induction n; simpl; intros. easy.
destruct (σ_2way s) eqn:T; simpl; apply IHn.
now apply σ_2way_cons. now apply σ_cons_true.
Qed.

(* Every prefix in σ encounters a next 2-way point. *)
Lemma Cσ_split s α :
  σ s = true -> ∃n, Cσ_1way s α n /\ σ_2way (Cσ s α n) = true.
Proof.
intros H; assert(Hs := H); apply σ_split in H as [t Ht].
(* By doing induction over [rev t] we essentially do a linear search. *)
rewrite <-(rev_involutive t) in Ht; remember (rev t) as s'; clear Heqs' t.
revert Ht Hs; revert s; induction s'; simpl; intros. now exists 0.
(* General observations *)
rewrite <-app_assoc in Ht.
assert(σ (a :: s) = true) by (eapply σ_app, σ_2way_inv, Ht).
(* Either σ splits at a :: s, or we can use the induction hypothesis. *)
destruct (σ_2way s) eqn:E. now exists 0.
destruct (IHs' _ Ht) as [n [H1n H2n]]. easy. simpl in H1n, H2n.
assert(H0 : σ_1way s = true). { eapply xorb_l. apply σ_12way; easy. easy. }
exists (S n); split.
- intros m Hm; destruct m. simpl. easy.
  apply succ_lt_mono in Hm; apply H1n in Hm.
  erewrite Cσ_S. erewrite σ_1way_cons. apply Hm. all: easy.
- erewrite Cσ_S. erewrite σ_1way_cons. apply H2n. all: easy.
Qed.

(* Cσ distributes over addition with the same α' on a 1-way segment. *)
Lemma Cσ_add s α α' m n :
  Cσ_1way s α m -> Cσ s α' (m + n) = Cσ (Cσ s α' m) α' n.
Proof.
revert s; induction m; intros. easy.
assert(σ_1way s = true) by (apply (H 0); lia).
rewrite add_succ_l, Cσ_S. rewrite IHm, <-Cσ_S. easy.
easy. intros i Hi; rewrite <-Cσ_S. apply H; lia. all: easy.
Qed.

(* The input sequence does not matter on a 1-way segment. *)
Lemma Cσ_change_seq s α α1 α2 n :
  Cσ_1way s α n -> Cσ s α1 n = Cσ s α2 n.
Proof.
revert s α α1 α2; induction n; intros. easy.
assert(σ_1way s = true). { replace s with (Cσ s α 0) by easy. apply H. lia. }
erewrite ?Cσ_S; try easy. eapply IHn; intros m Hm.
rewrite <-Cσ_S. apply H. lia. easy.
Qed.

(* We can determine where the image splits if the input splits. *)
Theorem nth_Cσ_inj s α1 α2 i :
  σ s = true -> α1 i ≠ α2 i -> ∃n, nth_Cσ s α1 n ≠ nth_Cσ s α2 n.
Proof.
intros Hs Hi; apply find_first_split in Hi as [j [_ [H1j H2j]]].
2: apply bool_dec. clear i; revert Hs H1j H2j; revert s α1 α2.
induction j; intros.
- (* α1 and α2 are apart at the next split. *)
  apply Cσ_split with (α:=α1) in Hs as [n [H1n H2n]]; exists n.
  unfold nth_Cσ; erewrite <-add_1_r, ?Cσ_add.
  erewrite Cσ_change_seq with (n:=n)(α1:=α2)(α2:=α1).
  simpl; rewrite ?H2n. intros H0; apply H2j. easy. all: apply H1n.
- (* go to the next split and apply induction hypothesis. *)
  apply Cσ_split with (α:=α1) in Hs as [m [H1m H2m]].
  assert((1<<α1) j ≠ (1<<α2) j) by easy.
  eapply IHj in H as [n Hn]. exists (m + (n + 1)); unfold nth_Cσ in *.
  erewrite <-add_succ_r, ?Cσ_add, Cσ_change_seq with (n:=m)(α1:=α2)(α2:=α1).
  simpl; rewrite ?H2m. rewrite <-H1j, add_comm. apply Hn. lia.
  1-3: apply H1m. unfold σ_2way in H2m; b_Prop.
  now destruct (α1 0). now apply branch_del.
Qed.

End Part_II.

End Finitary_spread.

(* Every prefix is either in X or is not in X (Law of Excluded Middle). *)
Definition prefix_LEM s b :=
  b = true <-> ∃α, X α /\ Branch (length s) (nth_rev s) α.

(* Classical logic shows that prefix_LEM holds. *)
Lemma prefix_LEM_classic s :
  ∃!b, prefix_LEM s b.
Proof.
unfold unique; destruct (classic (∃α, X α /\ Branch (length s) (nth_rev s) α)).
- exists true; split; try easy. intros b; destruct b; try easy.
  now intros H'; symmetry; apply H'.
- exists false; split; try easy. intros b; destruct b; try easy.
  now intros H'; exfalso; apply H, H'.
Qed.

(* Assert the existence of a prefix decider for X. *)
Section X_prefix_decider.

Variable σ : list bool -> bool.
Variable Hσ : ∀s, prefix_LEM s (σ s).

(* X is inhabited. *)
Theorem σ_nil :
  σ [] = true.
Proof.
apply not_empty in nonempty_X as [α Hα].
apply Hσ; now exists α.
Qed.

Lemma branch_S_nth_rev s b α :
  Branch (length s) (nth_rev s) α -> α (length s) = b ->
  Branch (S (length s)) (nth_rev (b :: s)) α.
Proof.
intros Hm Hb i Hi. eapply nth_rev_cases in Hi
as [[H R]|[H R]]; rewrite R. now apply Hm. now subst.
Qed.

(* A prefix is accepted iff a continuation is accepted. *)
Theorem σ_cont s :
  σ s = true <-> ∃b, σ (b :: s) = true.
Proof.
split.
- (* Continuation *)
  intros H; apply Hσ in H as [α [H1α H2α]]. exists (α (length s)).
  apply Hσ; exists α; split. easy. simpl. now apply branch_S_nth_rev.
- (* Pre-continuation *)
  intros [b Hb]. apply Hσ in Hb as [α [H1α H2α]]; apply Hσ; exists α.
  split. easy. intros i Hi. rewrite <-H2α; unfold nth_rev.
  replace (b :: s) with ([b] ++ s) by easy; rewrite rev_app_distr, app_nth1.
  easy. now rewrite rev_length. simpl; lia.
Qed.

Lemma andb_forall_true f : (∀b, f b = true) -> f false && f true = true.
Proof. intros H; now rewrite ?H. Qed.

Lemma bool_triangle (a b c : bool) : a ≠ b -> a ≠ c -> b = c.
Proof. now destruct a, b, c. Qed.

(* Every prefix in X eventually splits. *)
Theorem σ_split s :
  σ s = true -> ∃t, σ_2way σ (t ++ s) = true.
Proof.
intros H; apply Hσ in H as [α [H1α H2α]]. assert(H3α := perfect_X _ H1α).
destruct (H3α (length s)) as [β [H1β [H2β H3β]]].
apply seq_neq in H1β as [i' Hi'];
apply find_first_split in Hi' as [i [_ [H1i H2i]]]. 2: apply bool_dec.
(* Construct a continuation using induction on i - length s. *)
assert(i >= length s). { apply not_lt; intros H. now apply H2β in H. }
remember (i - length s) as n; assert(i = length s + n) by lia.
rewrite H0 in H1i, H2i; clear H3α H2β H Heqn H0 i i'.
revert H1α H2α H1i H2i H3β; revert s. induction n; intros.
- (* We are at the 2-way point. *)
  exists []; rewrite app_nil_l; rewrite add_0_r in *.
  apply andb_forall_true with (f:=λ b, σ (b :: s)).
  intros; apply Hσ; simpl. destruct (bool_dec (α (length s)) b).
  + exists α; split. easy. now apply branch_S_nth_rev.
  + exists β; split. easy. apply branch_S_nth_rev.
    eapply branch_trans. apply H2α. easy.
    eapply bool_triangle. apply H2i. easy.
- (* We take a 1-way step. *)
  pose(b := α (length s)); pose(t := b :: s).
  assert(length s + S n = length t + n) by (simpl; now rewrite <-add_succ_r).
  rewrite H in H1i, H2i. apply IHn in H2i as [t' Ht']; try easy.
  exists (t' ++ [b]); now rewrite <-app_assoc.
  unfold t; simpl. now apply branch_S_nth_rev.
Qed.

End X_prefix_decider.

(* Obtain a law for X using AC, and use the above construction. *)
Theorem nonempty_closed_perfect_embeds_C :
  EmbedsC.
Proof.
destruct (unique_choice _ _ _ prefix_LEM_classic) as [σ Hσ].
assert(σ_nil := σ_nil σ Hσ);
assert(σ_cont := σ_cont σ Hσ);
assert(σ_split := σ_split σ Hσ).
exists (nth_Cσ σ []); split.
- (* Dom ⊆ X *)
  intros; apply closed_X; intros m.
  apply Cσ_accepted with (α:=α)(n:=m) in σ_nil as Hm. 2: easy.
  (* Obtain β from Hσ and γ from perfect_X, by classical logic one is apart. *)
  apply Hσ in Hm as [β [H1β H2β]]. apply perfect_X in H1β as H3β.
  rewrite Cσ_length in H2β; simpl in H2β.
  destruct (H3β m) as [γ [H1γ [H2γ H3γ]]].
  destruct (classic (nth_Cσ σ [] α = β)).
  + exists γ; repeat split. now rewrite H.
    eapply branch_trans. now apply nth_Cσ_eq_nth_rev.
    eapply branch_trans. apply H2β.
    easy. easy.
  + exists β; repeat split. easy.
    eapply branch_trans. now apply nth_Cσ_eq_nth_rev.
    easy. easy.
- (* Injective *)
  intros α1 α2; apply classic_contra; intros. apply seq_neq in H as [i Hi].
  apply nth_Cσ_inj with (σ:=σ)(s:=[]) in Hi as [n Hn].
  apply seq_neq; now exists n. all: easy.
Qed.

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
