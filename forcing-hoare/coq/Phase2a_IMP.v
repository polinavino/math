(** * Phase 2a: IMP — syntax, state, small-step operational semantics

    A tiny imperative language [IMP] consisting of variables, arithmetic
    and boolean expressions, and the standard control-flow commands.
    The semantics is given in small-step style: each step of execution
    corresponds to one "tick" of the step-index clock, which is the
    granularity at which we will define forcing-style Hoare triples in
    Phase 2b.
*)

From Coq Require Import Arith Lia ZArith.

Open Scope Z_scope.

(** ** Variables and state *)

Definition var : Type := nat.
Definition state : Type := var -> Z.

Definition update (s : state) (x : var) (v : Z) : state :=
  fun y => if Nat.eqb x y then v else s y.

Lemma update_eq s x v : update s x v x = v.
Proof. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq s x y v : x <> y -> update s x v y = s y.
Proof.
  intros H. unfold update.
  destruct (Nat.eqb x y) eqn:E; [|reflexivity].
  exfalso. apply H. apply Nat.eqb_eq. exact E.
Qed.

(** ** Arithmetic and boolean expressions *)

Inductive aexp : Type :=
  | ANum   : Z -> aexp
  | AVar   : var -> aexp
  | APlus  : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult  : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue  : bexp
  | BFalse : bexp
  | BEq    : aexp -> aexp -> bexp
  | BLe    : aexp -> aexp -> bexp
  | BNot   : bexp -> bexp
  | BAnd   : bexp -> bexp -> bexp.

Fixpoint aeval (s : state) (a : aexp) : Z :=
  match a with
  | ANum n      => n
  | AVar x      => s x
  | APlus a1 a2 => aeval s a1 + aeval s a2
  | AMinus a1 a2 => aeval s a1 - aeval s a2
  | AMult a1 a2 => aeval s a1 * aeval s a2
  end.

Fixpoint beval (s : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => Z.eqb (aeval s a1) (aeval s a2)
  | BLe a1 a2   => Z.leb (aeval s a1) (aeval s a2)
  | BNot b'     => negb (beval s b')
  | BAnd b1 b2  => andb (beval s b1) (beval s b2)
  end.

(** ** Commands *)

Inductive cmd : Type :=
  | CSkip   : cmd
  | CAssign : var -> aexp -> cmd
  | CSeq    : cmd -> cmd -> cmd
  | CIf     : bexp -> cmd -> cmd -> cmd
  | CWhile  : bexp -> cmd -> cmd.

(** ** Small-step operational semantics

    [step (c, s) (c', s')] means one execution step takes the
    configuration [(c, s)] to [(c', s')].  [CSkip] is the only terminal
    command (it has no outgoing transitions).  Each transition will
    correspond to one decrement of the step index in Phase 2b. *)

Reserved Notation "cs1 '~>' cs2" (at level 70).

Inductive step : cmd * state -> cmd * state -> Prop :=
  | StepAssign : forall s x a,
      (CAssign x a, s) ~> (CSkip, update s x (aeval s a))
  | StepSeqL : forall c1 c1' c2 s s',
      (c1, s) ~> (c1', s') ->
      (CSeq c1 c2, s) ~> (CSeq c1' c2, s')
  | StepSeqSkip : forall c2 s,
      (CSeq CSkip c2, s) ~> (c2, s)
  | StepIfTrue : forall b c1 c2 s,
      beval s b = true ->
      (CIf b c1 c2, s) ~> (c1, s)
  | StepIfFalse : forall b c1 c2 s,
      beval s b = false ->
      (CIf b c1 c2, s) ~> (c2, s)
  | StepWhileTrue : forall b c s,
      beval s b = true ->
      (CWhile b c, s) ~> (CSeq c (CWhile b c), s)
  | StepWhileFalse : forall b c s,
      beval s b = false ->
      (CWhile b c, s) ~> (CSkip, s)
where "cs1 '~>' cs2" := (step cs1 cs2).

(** Iterated reduction: [steps n cs cs'] means [cs] reduces to [cs']
    in exactly [n] small steps. *)

Inductive steps : nat -> cmd * state -> cmd * state -> Prop :=
  | StepsO : forall cs, steps 0 cs cs
  | StepsS : forall n cs1 cs2 cs3,
      cs1 ~> cs2 -> steps n cs2 cs3 -> steps (S n) cs1 cs3.

(** A configuration is *safe* if it can either step or is terminal.
    This is the standard notion underlying step-indexed safety
    semantics: a Hoare triple will assert safety for the appropriate
    number of steps. *)

Definition safe (cs : cmd * state) : Prop :=
  fst cs = CSkip \/ exists cs', cs ~> cs'.

(** ** Smoke test *)

Definition x_var : var := 0%nat.

Example tiny_runs :
  exists s, steps 1 (CAssign x_var (ANum 42), fun _ => 0)
                    (CSkip, s)
            /\ s x_var = 42.
Proof.
  eexists. split.
  - eapply StepsS; [apply StepAssign | apply StepsO].
  - apply update_eq.
Qed.
