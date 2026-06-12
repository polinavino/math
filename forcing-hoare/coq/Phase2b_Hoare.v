(** * Phase 2b: Step-indexed Hoare triples for IMP via the forcing semantics

    Step-indexed weakest preconditions and Hoare triples for IMP,
    interpreted as iProps over the forcing semantics from Phase 1.
    We prove soundness of the standard structural rules: [skip],
    assignment, sequencing, conditionals, and the rule of consequence.

    The while rule, which is where the forcing / step-indexed framework
    earns its keep via Löb's rule, is deferred to Phase 2c.
*)

From Coq Require Import Arith Lia ZArith.
From ForcingHoare Require Import Phase1_Forcing Phase2a_IMP.
Close Scope Z_scope.

(** ** Step-indexed weakest precondition

    [wp_at n c Q s]: starting from state [s], the command [c]
    executed for at most [n] small steps is safe and ends, if at all,
    in a state satisfying [Q].  This is the canonical step-indexed
    safety / weakest-precondition predicate. *)

Fixpoint wp_at (n : nat) (c : cmd) (Q : state -> Prop) (s : state) : Prop :=
  match n with
  | O => True
  | S k =>
      (c = CSkip -> Q s) /\
      (forall c' s', step (c, s) (c', s') -> wp_at k c' Q s')
  end.

(** Monotonicity in the step index. *)
Lemma wp_at_mono :
  forall n m c Q s, m <= n -> wp_at n c Q s -> wp_at m c Q s.
Proof.
  intros n m. revert n. induction m as [|m IH]; intros n c Q s Hle Hwp.
  - simpl. trivial.
  - destruct n as [|n']; [lia|]. simpl in *.
    destruct Hwp as [Hskip Hstep]. split.
    + exact Hskip.
    + intros c' s' Hs. apply (IH n'); [lia | apply Hstep; exact Hs].
Qed.

(** Monotonicity in the postcondition. *)
Lemma wp_at_post_mono :
  forall n c Q1 Q2 s,
    (forall s', Q1 s' -> Q2 s') ->
    wp_at n c Q1 s -> wp_at n c Q2 s.
Proof.
  induction n as [|n IH]; intros c Q1 Q2 s Himp Hwp; simpl in *; auto.
  destruct Hwp as [Hskip Hstep]. split.
  - intros He. apply Himp. apply Hskip. exact He.
  - intros c' s' Hs. eapply IH; [exact Himp | apply Hstep; exact Hs].
Qed.

(** ** Lifting to iProp *)

(** The wp as an iProp (with [c], [Q], [s] as parameters). *)
Definition wp (c : cmd) (Q : state -> Prop) (s : state) : iProp :=
  MkProp (fun n => wp_at n c Q s)
         (fun n m Hmn Hn => wp_at_mono n m c Q s Hmn Hn).

(** The Hoare triple, also as an iProp. *)
Lemma hoare_at_mono (P : state -> Prop) (c : cmd) (Q : state -> Prop) :
  forall n m, m <= n ->
    (forall s, P s -> wp_at n c Q s) ->
    (forall s, P s -> wp_at m c Q s).
Proof.
  intros n m Hle H s HP.
  apply (wp_at_mono n m c Q s Hle). apply H; exact HP.
Qed.

Definition hoare (P : state -> Prop) (c : cmd) (Q : state -> Prop) : iProp :=
  MkProp (fun n => forall s, P s -> wp_at n c Q s)
         (hoare_at_mono P c Q).

(** Validity of a Hoare triple: it is forced at every condition.
    This is exactly the standard partial-correctness statement
    "for every step budget n and state s with P s, wp_at n c Q s." *)
Definition hoare_valid (P : state -> Prop) (c : cmd) (Q : state -> Prop) : Prop :=
  ⊤ ⊢ hoare P c Q.

Lemma hoare_valid_alt P c Q :
  hoare_valid P c Q <-> (forall n s, P s -> wp_at n c Q s).
Proof.
  unfold hoare_valid, ientails. split.
  - intros H n s HP. apply (H n I s HP).
  - intros H n _ s HP. apply H, HP.
Qed.

(** ** Soundness of structural rules *)

(** *** Skip *)
Lemma hoare_skip P : hoare_valid P CSkip P.
Proof.
  apply hoare_valid_alt. intros n s HP.
  destruct n as [|n']; simpl; auto. split.
  - intros _; exact HP.
  - intros c' s' Hstep; inversion Hstep.
Qed.

(** *** Assignment *)
Definition asgn_pre (Q : state -> Prop) (x : var) (a : aexp) : state -> Prop :=
  fun s => Q (update s x (aeval s a)).

Lemma hoare_assign Q x a :
  hoare_valid (asgn_pre Q x a) (CAssign x a) Q.
Proof.
  apply hoare_valid_alt. intros n s HP. unfold asgn_pre in HP.
  destruct n as [|n']; simpl; auto. split.
  - discriminate.
  - intros c' s' Hstep. inversion Hstep; subst.
    destruct n' as [|n'']; simpl; auto. split.
    + intros _; exact HP.
    + intros c'' s'' Hstep'; inversion Hstep'.
Qed.

(** *** Sequencing *)

(** Selectively unfolding lemma: lets us destructure the outer
    [wp_at (S n)] without also unfolding any inner occurrences. *)
Lemma wp_at_S n c Q s :
  wp_at (S n) c Q s =
  ((c = CSkip -> Q s) /\
   (forall c' s', step (c, s) (c', s') -> wp_at n c' Q s')).
Proof. reflexivity. Qed.

(** Key lemma: the wp of a sequence is the wp of the first command
    targeting the wp of the second. *)
Lemma wp_seq :
  forall n c1 c2 Q s,
    wp_at n c1 (fun s' => wp_at n c2 Q s') s ->
    wp_at n (CSeq c1 c2) Q s.
Proof.
  induction n as [|n IH]; intros c1 c2 Q s Hwp.
  - simpl. trivial.
  - rewrite wp_at_S in Hwp. destruct Hwp as [Hskip Hstep].
    rewrite wp_at_S. split.
    + discriminate.
    + intros c' s' Hs. inversion Hs; subst.
      * (* StepSeqL: c1 makes a step *)
        apply IH.
        eapply wp_at_post_mono.
        2: { eapply Hstep; eassumption. }
        intros s'' Hpre.
        eapply wp_at_mono.
        2: { exact Hpre. }
        lia.
      * (* StepSeqSkip: c1 = CSkip *)
        eapply wp_at_mono.
        2: { apply Hskip; reflexivity. }
        lia.
Qed.

Lemma hoare_seq P c1 R c2 Q :
  hoare_valid P c1 R ->
  hoare_valid R c2 Q ->
  hoare_valid P (CSeq c1 c2) Q.
Proof.
  intros H1 H2. apply hoare_valid_alt. intros n s HP.
  rewrite hoare_valid_alt in H1, H2.
  apply wp_seq.
  eapply wp_at_post_mono; [|apply H1, HP].
  intros s' Hr. apply H2, Hr.
Qed.

(** *** Conditional *)
Lemma hoare_if P b c1 c2 Q :
  hoare_valid (fun s => P s /\ beval s b = true) c1 Q ->
  hoare_valid (fun s => P s /\ beval s b = false) c2 Q ->
  hoare_valid P (CIf b c1 c2) Q.
Proof.
  intros H1 H2. apply hoare_valid_alt. intros n s HP.
  rewrite hoare_valid_alt in H1, H2.
  destruct n as [|n']; simpl; auto. split.
  - discriminate.
  - intros c' s' Hstep. inversion Hstep; subst.
    + apply H1; split; assumption.
    + apply H2; split; assumption.
Qed.

(** *** Consequence *)
Lemma hoare_consequence P P' c Q Q' :
  (forall s, P s -> P' s) ->
  hoare_valid P' c Q' ->
  (forall s, Q' s -> Q s) ->
  hoare_valid P c Q.
Proof.
  intros HP HV HQ. apply hoare_valid_alt. intros n s HPs.
  rewrite hoare_valid_alt in HV.
  eapply wp_at_post_mono; [exact HQ|]. apply HV, HP, HPs.
Qed.

(** ** Smoke test: an end-to-end derivation

    [{ x = x } x := 42 { x = 42 }] — the assignment rule applied
    via the consequence rule. *)

Lemma demo_assign :
  hoare_valid (fun _ => True) (CAssign x_var (ANum 42%Z))
              (fun s => s x_var = 42%Z).
Proof.
  eapply hoare_consequence with
    (P' := asgn_pre (fun s => s x_var = 42%Z) x_var (ANum 42%Z))
    (Q' := fun s => s x_var = 42%Z).
  - intros s _. unfold asgn_pre. simpl. apply update_eq.
  - apply hoare_assign.
  - intros s H; exact H.
Qed.
