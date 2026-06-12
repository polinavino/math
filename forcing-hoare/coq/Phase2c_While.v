(** * Phase 2c: The Hoare rule for [while], via Löb's rule

    The remaining structural rule of partial-correctness Hoare logic is
    the rule for [while]:

       {P ∧ b} c {P}
       -----------------------------
       {P} while b do c {P ∧ ¬b}

    This rule is the one that distinguishes Hoare logic from a purely
    structural language: the conclusion talks about a *recursively
    defined* program, and the soundness proof has to recurse with it.

    In the step-indexed / forcing setup, this recursion is the
    canonical use case for Löb's rule.  We prove the rule directly by
    induction on the step index; the induction step is precisely the
    elimination form of Löb at the meta level (the propositional Löb
    rule we proved in Phase 1 is the internalisation of this same
    argument). *)

From Coq Require Import Arith Lia ZArith.
From ForcingHoare Require Import Phase1_Forcing Phase2a_IMP Phase2b_Hoare.
Close Scope Z_scope.

Lemma hoare_while P b c :
  hoare_valid (fun s => P s /\ beval s b = true) c P ->
  hoare_valid P (CWhile b c) (fun s => P s /\ beval s b = false).
Proof.
  intros HC.
  rewrite hoare_valid_alt in HC.
  apply hoare_valid_alt.
  (* Induction on the step index [n].  The induction step is the
     content of Löb's rule: knowing the result for indices [< n], we
     get it at [n]. *)
  intros n. induction n as [|n IH]; intros s HP.
  - simpl. trivial.
  - rewrite wp_at_S. split.
    + discriminate.
    + intros c' s' Hstep. inversion Hstep; subst.
      * (* StepWhileTrue: the loop unfolds to [c ; while b do c]. *)
        apply wp_seq.
        eapply wp_at_post_mono.
        2: { apply HC; split; [exact HP | assumption]. }
        intros s'' HP'. apply IH. exact HP'.
      * (* StepWhileFalse: the loop terminates with [P ∧ ¬b]. *)
        destruct n as [|n'].
        -- simpl. trivial.
        -- rewrite wp_at_S. split.
           ++ intros _. split; assumption.
           ++ intros c'' s'' Hstep'. inversion Hstep'.
Qed.

(** ** Demonstration: a trivially terminating loop

    [{ True } while (false) do skip { True ∧ false = false }]
*)

Example demo_while_false :
  hoare_valid (fun _ => True) (CWhile BFalse CSkip)
              (fun s => True /\ beval s BFalse = false).
Proof.
  apply hoare_while. apply hoare_valid_alt.
  intros n s [_ Hb]. discriminate Hb.
Qed.

(** ** Putting it together: the "all rules" theorem

    Every soundness rule we have proved is now packaged. Together they
    form a sound proof system for partial correctness over IMP,
    interpreted via the forcing semantics of Phase 1. *)

Theorem imp_hoare_rules :
  (forall P, hoare_valid P CSkip P) /\
  (forall Q x a, hoare_valid (asgn_pre Q x a) (CAssign x a) Q) /\
  (forall P c1 R c2 Q,
     hoare_valid P c1 R ->
     hoare_valid R c2 Q ->
     hoare_valid P (CSeq c1 c2) Q) /\
  (forall P b c1 c2 Q,
     hoare_valid (fun s => P s /\ beval s b = true) c1 Q ->
     hoare_valid (fun s => P s /\ beval s b = false) c2 Q ->
     hoare_valid P (CIf b c1 c2) Q) /\
  (forall P b c,
     hoare_valid (fun s => P s /\ beval s b = true) c P ->
     hoare_valid P (CWhile b c) (fun s => P s /\ beval s b = false)) /\
  (forall P P' c Q Q',
     (forall s, P s -> P' s) ->
     hoare_valid P' c Q' ->
     (forall s, Q' s -> Q s) ->
     hoare_valid P c Q).
Proof.
  repeat split.
  - apply hoare_skip.
  - apply hoare_assign.
  - apply hoare_seq.
  - apply hoare_if.
  - apply hoare_while.
  - apply hoare_consequence.
Qed.
