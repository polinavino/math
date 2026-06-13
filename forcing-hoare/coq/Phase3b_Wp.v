(** * Phase 3b: Step-indexed wp for the λ-calculus, with safety

    We define a step-indexed weakest precondition for the language of
    Phase 3a and lift it to an [iProp].  Unlike the Phase 2b wp for
    IMP, this one carries an explicit *safety* conjunct: every
    intermediate configuration must either already be a value or be
    able to take a step.  The reason is that the λ-calculus has stuck
    terms — applying an integer as a function, taking [if0] of a
    lambda, etc. — and we want to rule them out as failures rather
    than counting them as vacuously good.

    We keep this file deliberately minimal: just the wp definition,
    monotonicity, the value rule, and a "pure step" rule for
    deterministic head reduction.  The specific structural rules for
    [plus], [if0], and [app] either require an evaluation-context
    framework or unfold via the pure-step rule on a case-by-case
    basis; we defer them until Phase 3c, where they appear together
    with the [fix] rule that is the actual point of the chapter. *)

From Coq Require Import Arith Lia ZArith.
From ForcingHoare Require Import Phase1_Forcing Phase3a_Lambda.

(** ** Step-indexed weakest precondition

    [wp_at n e Q] holds when evaluating [e] for at most [n] small
    steps is *safe* (no stuck intermediate configuration) and, if it
    reaches a value, the value satisfies [Q]. *)

Fixpoint wp_at (n : nat) (e : expr) (Q : expr -> Prop) : Prop :=
  match n with
  | O => True
  | S k =>
      (value e -> Q e) /\
      (value e \/ exists e', step e e') /\
      (forall e', step e e' -> wp_at k e' Q)
  end.

(** Monotonicity in the step index. *)
Lemma wp_at_mono :
  forall n m e Q, m <= n -> wp_at n e Q -> wp_at m e Q.
Proof.
  intros n m. revert n.
  induction m as [|m IH]; intros n e Q Hle Hwp.
  - simpl. trivial.
  - destruct n as [|n']; [lia|]. simpl in *.
    destruct Hwp as [Hval [Hsafe Hstep]]. split; [|split].
    + exact Hval.
    + exact Hsafe.
    + intros e' Hs. apply (IH n'); [lia | apply Hstep; exact Hs].
Qed.

(** Monotonicity in the postcondition. *)
Lemma wp_at_post_mono :
  forall n e Q1 Q2,
    (forall v, Q1 v -> Q2 v) ->
    wp_at n e Q1 -> wp_at n e Q2.
Proof.
  induction n as [|n IH]; intros e Q1 Q2 Himp Hwp; simpl in *; auto.
  destruct Hwp as [Hval [Hsafe Hstep]]. split; [|split].
  - intros Hv. apply Himp, Hval, Hv.
  - exact Hsafe.
  - intros e' Hs. eapply IH; [exact Himp | apply Hstep; exact Hs].
Qed.

(** Selectively unfolding lemma, paralleling Phase 2b. *)
Lemma wp_at_S n e Q :
  wp_at (S n) e Q =
  ((value e -> Q e) /\
   (value e \/ exists e', step e e') /\
   (forall e', step e e' -> wp_at n e' Q)).
Proof. reflexivity. Qed.

(** Lifted to [iProp]. *)
Definition wp (e : expr) (Q : expr -> Prop) : iProp :=
  MkProp (fun n => wp_at n e Q)
         (fun n m Hmn Hn => wp_at_mono n m e Q Hmn Hn).

(** Validity. *)
Definition wp_valid (e : expr) (Q : expr -> Prop) : Prop :=
  ⊤ ⊢ wp e Q.

Lemma wp_valid_alt e Q :
  wp_valid e Q <-> forall n, wp_at n e Q.
Proof.
  unfold wp_valid, ientails. split.
  - intros H n. apply (H n I).
  - intros H n _. apply H.
Qed.

(** ** Helper: values do not step

    Useful for closing impossible step-from-value subgoals. *)
Lemma value_no_step v e' : value v -> ~ step v e'.
Proof. intros Hv Hs. inversion Hv; subst; inversion Hs. Qed.

(** ** Soundness rules *)

(** *** Values: a value satisfies a postcondition iff the
    postcondition is satisfied at it. *)
Lemma wp_value v Q : value v -> Q v -> wp_valid v Q.
Proof.
  intros Hv HQ. apply wp_valid_alt. intros n.
  destruct n as [|n']; simpl; auto. split; [|split].
  - intros _. exact HQ.
  - left. exact Hv.
  - intros e' Hs. exfalso. eapply value_no_step; eauto.
Qed.

(** *** Pure deterministic step

    If [e] is not a value, every step from [e] lands at the same
    target [e'], and [e'] satisfies the wp at one less step, then [e]
    satisfies the wp.  This is the canonical "pure step" rule and is
    what carries us through any β- or fix-unfolding reduction. *)
Lemma wp_pure_step_at n e e' Q :
  ~ value e ->
  (exists e'', step e e'') ->
  (forall e'', step e e'' -> e'' = e') ->
  wp_at n e' Q ->
  wp_at (S n) e Q.
Proof.
  intros Hnv Hprog Hdet Hwp.
  simpl. split; [|split].
  - intros Hv. contradiction.
  - right. exact Hprog.
  - intros e'' Hs. specialize (Hdet _ Hs). subst. exact Hwp.
Qed.

(** A convenience form: derive [wp_valid] for [e] from [wp_valid] for
    its (deterministic) head-reduct [e']. *)
Lemma wp_pure_step e e' Q :
  ~ value e ->
  (exists e'', step e e'') ->
  (forall e'', step e e'' -> e'' = e') ->
  wp_valid e' Q ->
  wp_valid e Q.
Proof.
  intros Hnv Hprog Hdet Hwp.
  rewrite wp_valid_alt in Hwp.
  apply wp_valid_alt. intros n.
  destruct n as [|n']; simpl; auto.
  apply (wp_pure_step_at n' e e' Q); auto.
Qed.
