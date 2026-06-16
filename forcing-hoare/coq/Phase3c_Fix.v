(** * Phase 3c: Soundness of [fix] via Löb's rule

    The payoff phase.  We define a notion of "recursive spec" for a
    function — a function that takes arguments satisfying some
    predicate [S] and returns values also satisfying [S].  This is the
    simplest spec shape that exhibits genuine self-reference (the
    function's spec mentions the function itself).

    We then prove that to establish the recursive spec for [EFix body],
    it suffices to know that [body], applied with any self-reference
    [e_self] that already has the spec, again has the spec.  The
    proof goes through [iLob] from Phase 1 *directly* — not via a
    meta-level induction on the step index that happens to enact the
    same argument.  This file is therefore the first place in the
    development where the propositional Löb rule does load-bearing
    work.
*)

From Coq Require Import Arith Lia ZArith.
From ForcingHoare Require Import Phase1_Forcing Phase3a_Lambda Phase3b_Wp.

(** ** The recursive-spec iProp

    [recursive_spec e S] says: for every value [v] satisfying [S],
    applying [e] to [v] is safe and produces a value satisfying [S].
    The same predicate [S] appears as pre- and post-condition; this is
    the case where the spec is genuinely self-referential and Löb is
    the natural tool. *)

Lemma recursive_spec_mono (e : expr) (S : expr -> Prop) :
  forall n m, m <= n ->
    (forall v, value v -> S v -> wp_at n (EApp e v) S) ->
    (forall v, value v -> S v -> wp_at m (EApp e v) S).
Proof.
  intros n m Hle H v Hval HS. eapply wp_at_mono; eauto.
Qed.

Definition recursive_spec (e : expr) (S : expr -> Prop) : iProp :=
  MkProp (fun n => forall v, value v -> S v -> wp_at n (EApp e v) S)
         (recursive_spec_mono e S).

(** ** Determinism and progress of fix-application

    Showing that applying [EFix body] to a value [v] has exactly one
    reduct — namely [EApp (subst (EFix body) body) v] — and is never
    stuck.  Both are needed to invoke [wp_pure_step_at] inside the
    Löb argument. *)

Lemma step_fix_det body v e' :
  value v ->
  step (EApp (EFix body) v) e' ->
  e' = EApp (subst (EFix body) body) v.
Proof.
  intros Hv Hs.
  inversion Hs; subst.
  - (* StepAppL: would need EFix body to step, but values do not step *)
    match goal with H : step (EFix _) _ |- _ => inversion H end.
  - (* StepAppR: would need v to step, but v is a value *)
    exfalso. eapply value_no_step; [exact Hv|].
    match goal with H : step v _ |- _ => exact H end.
  - (* StepFix: the only matching case *)
    reflexivity.
Qed.

Lemma step_fix_progress body v :
  value v -> exists e', step (EApp (EFix body) v) e'.
Proof. intros Hv. eexists. apply StepFix. exact Hv. Qed.

Lemma not_value_app_fix body v : ~ value (EApp (EFix body) v).
Proof. intros H. inversion H. Qed.

(** ** The soundness rule for [fix], via internal Löb

    The premise is the "Lipschitz" condition on the body: assuming the
    self-reference [e_self] satisfies the recursive spec, the
    substituted body again satisfies the recursive spec.  Note that
    this premise is an iProp entailment — it is the body's *internal*
    behaviour we constrain, not its behaviour at a particular index.

    The conclusion is that [EFix body] satisfies the recursive spec
    outright, forced at every condition. *)

Theorem wp_fix (body : expr) (S : expr -> Prop) :
  (forall e_self,
     value e_self ->
     recursive_spec e_self S ⊢ recursive_spec (subst e_self body) S) ->
  ⊤ ⊢ recursive_spec (EFix body) S.
Proof.
  intros Hbody.
  (* Strategy: by [iLob], it suffices to show [⊤ ⊢ ▷ φ → φ] for
     [φ := recursive_spec (EFix body) S].  The internal Löb rule then
     closes the proof. *)
  apply ientails_trans with
    (iLater (recursive_spec (EFix body) S) → recursive_spec (EFix body) S).
  - (* ⊤ ⊢ ▷ φ → φ *)
    intros n _.
    intros m Hmn Hlater.
    destruct m as [|m'].
    + (* m = 0: the spec is trivially forced because [wp_at 0 = True]. *)
      intros v Hvalue HS. simpl. trivial.
    + (* m = S m': the load-bearing case.
         [Hlater] now is ▷ φ at S m', which by definition of ▷ is
         [φ] at [m']: every well-typed argument [v] satisfies
         [wp_at m' (EApp (EFix body) v) S]. *)
      simpl in Hlater.
      intros v Hvalue HS.
      (* [EApp (EFix body) v] reduces in one step to
         [EApp (subst (EFix body) body) v], so by [wp_pure_step_at] it
         suffices to verify the reduct at index [m']. *)
      apply (wp_pure_step_at m' (EApp (EFix body) v)
                                (EApp (subst (EFix body) body) v) S).
      * apply not_value_app_fix.
      * apply step_fix_progress; exact Hvalue.
      * intros e' Hs. apply step_fix_det; auto.
      * (* The reduct's wp at [m'] follows from the body's Lipschitz
           assumption [Hbody], instantiated at [e_self := EFix body]
           and supplied with [Hlater] as evidence that this self-
           reference already has the spec at the previous level. *)
        apply (Hbody (EFix body) (VFix body) m' Hlater v Hvalue HS).
  - (* The internal Löb rule closes the gap. *)
    apply iLob.
Qed.

(** ** Generalised soundness rule: distinct pre- and postconditions

    The [recursive_spec] above is the specialisation of a more general
    recursive-spec shape to the case where the precondition on the
    argument and the postcondition on the result coincide.  In a
    standard Hoare-triple setting, one wants a precondition [P] on the
    argument and a postcondition [Q] on the result, with the two
    distinct.  We give that generalisation here and prove the
    corresponding fix-point soundness rule by exactly the same
    Löb-based argument as [wp_fix]. *)

Lemma recursive_spec_pp_mono (e : expr) (P Q : expr -> Prop) :
  forall n m, m <= n ->
    (forall v, value v -> P v -> wp_at n (EApp e v) Q) ->
    (forall v, value v -> P v -> wp_at m (EApp e v) Q).
Proof.
  intros n m Hle H v Hval HP. eapply wp_at_mono; eauto.
Qed.

Definition recursive_spec_pp (e : expr) (P Q : expr -> Prop) : iProp :=
  MkProp (fun n => forall v, value v -> P v -> wp_at n (EApp e v) Q)
         (recursive_spec_pp_mono e P Q).

Theorem wp_fix_pp (body : expr) (P Q : expr -> Prop) :
  (forall e_self,
     value e_self ->
     recursive_spec_pp e_self P Q
       ⊢ recursive_spec_pp (subst e_self body) P Q) ->
  ⊤ ⊢ recursive_spec_pp (EFix body) P Q.
Proof.
  intros Hbody.
  apply ientails_trans with
    (iLater (recursive_spec_pp (EFix body) P Q)
       → recursive_spec_pp (EFix body) P Q).
  - intros n _ m Hmn Hlater.
    destruct m as [|m'].
    + intros v Hvalue HP. simpl. trivial.
    + simpl in Hlater. intros v Hvalue HP.
      apply (wp_pure_step_at m' (EApp (EFix body) v)
                                (EApp (subst (EFix body) body) v) Q).
      * apply not_value_app_fix.
      * apply step_fix_progress; exact Hvalue.
      * intros e' Hs. apply step_fix_det; auto.
      * apply (Hbody (EFix body) (VFix body) m' Hlater v Hvalue HP).
  - apply iLob.
Qed.

(** The original [wp_fix] is a corollary of [wp_fix_pp] specialised
    to [P = Q = S].  We keep the dedicated proof of [wp_fix] above
    for its pedagogical clarity (the more focused statement is what
    we use in the worked examples of Phase 3d). *)
