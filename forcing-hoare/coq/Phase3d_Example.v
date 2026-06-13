(** * Phase 3d: A worked example using [wp_fix]

    Two recursive functions verified using the [wp_fix] rule from
    Phase 3c.  Their purpose is to make the framework concrete: to
    show that the soundness rule is not only sound but actually
    *usable* for verifying programs.

    - [recursive_id] is a fix-point that ignores its self-reference
      and returns its argument unchanged.  It is observably equivalent
      to the plain identity [ELam (EVar 0)], but the [fix] wrapper
      forces a fix-unfolding step at every application.  We verify
      that for any predicate [S], applied to a value satisfying [S],
      it returns a value satisfying [S].

    - [bottom] is the canonical divergent fix-point: applied to any
      value, its single step is to itself.  We verify it satisfies
      *every* recursive spec, vacuously — the textbook observation
      that partial-correctness specifications are trivially satisfied
      by non-terminating programs.  This is included partly as a
      reality check and partly because in the forcing framework the
      proof becomes a one-liner. *)

From Coq Require Import Arith Lia ZArith.
From ForcingHoare Require Import Phase1_Forcing Phase3a_Lambda Phase3b_Wp Phase3c_Fix.

(** A small helper: a value satisfies the wp at any index iff it
    satisfies the postcondition. *)
Lemma wp_at_value n v Q : value v -> Q v -> wp_at n v Q.
Proof.
  intros Hv HQ. destruct n as [|n']; simpl; auto. split; [|split].
  - auto.
  - left; assumption.
  - intros e' Hs. exfalso; eapply value_no_step; eauto.
Qed.

(** Determinism helper: applying [ELam (EVar 0)] to a value [v]
    reduces only to [v]. *)
Lemma step_app_lam_var0_det v e' :
  value v ->
  step (EApp (ELam (EVar 0)) v) e' ->
  e' = v.
Proof.
  intros Hv Hs.
  inversion Hs as [ | | | | |
                  | e1 e1' e2 Hinner
                  | v0 e2 e2' Hv0 Hinner
                  | bd va Hva
                  |
                  ]; subst.
  - (* StepAppL: would need [ELam] to step *)
    exfalso. inversion Hinner.
  - (* StepAppR: would need [v] to step, but [v] is a value *)
    exfalso. apply (value_no_step _ _ Hv Hinner).
  - (* StepBeta: substitutes [v] for index 0 *)
    simpl. reflexivity.
Qed.

(** ** Example 1: a recursive identity *)

Definition recursive_id : expr := EFix (ELam (EVar 0)).

(** Smoke test: [recursive_id 5 ~>[2] 5].  Two small steps: a
    fix-unfolding, then a β-reduction. *)
Example recursive_id_runs :
  steps 2 (EApp recursive_id (EInt 5)) (EInt 5).
Proof.
  unfold recursive_id.
  eapply StepsS; [apply StepFix; constructor|]. simpl.
  eapply StepsS; [apply StepBeta; constructor|]. simpl.
  apply StepsO.
Qed.

(** Soundness: [recursive_id] preserves any postcondition [S].  The
    key observation is that the body [ELam (EVar 0)] does not refer
    to the self-reference (it uses index 0, the lambda's argument, not
    index 1 which would be the fix-self), so the [wp_fix] premise
    reduces to a non-recursive obligation about a plain lambda. *)
Theorem recursive_id_spec (S : expr -> Prop) :
  ⊤ ⊢ recursive_spec recursive_id S.
Proof.
  apply wp_fix. intros e_self Hself n _.
  (* Goal: n ⊩ recursive_spec (subst e_self (ELam (EVar 0))) S
     The body doesn't reference the self, so substitution is the
     identity: [subst e_self (ELam (EVar 0)) = ELam (EVar 0)]. *)
  intros v Hvalue HS.
  destruct n as [|n']; [simpl; trivial|].
  apply (wp_pure_step_at n' (EApp (ELam (EVar 0)) v) v S).
  - intros H; inversion H.
  - eexists. apply StepBeta; exact Hvalue.
  - intros e' Hs. apply step_app_lam_var0_det; assumption.
  - apply wp_at_value; assumption.
Qed.

(** ** Example 2: a divergent fix-point *)

Definition bottom : expr := EFix (EVar 0).

(** Smoke test: [bottom 5] takes one step — to itself. *)
Example bottom_loops :
  steps 1 (EApp bottom (EInt 5)) (EApp bottom (EInt 5)).
Proof.
  unfold bottom.
  eapply StepsS; [apply StepFix; constructor|]. simpl.
  apply StepsO.
Qed.

(** [bottom] satisfies every recursive spec, vacuously, because it
    never reaches a value.  In the forcing framework the [wp_fix]
    proof obligation reduces to reflexivity: the body of [bottom] is
    the bare self-reference, so the substituted body just *is* the
    self-reference, and the Lipschitz premise becomes trivial. *)
Theorem bottom_spec (S : expr -> Prop) :
  ⊤ ⊢ recursive_spec bottom S.
Proof.
  apply wp_fix. intros e_self Hself.
  apply ientails_refl.
Qed.
