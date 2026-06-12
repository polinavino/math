(** * Phase 3a: An untyped λ-calculus with general recursion

    The setting in which step-indexing earns its keep. Without
    recursion, the basic IMP Hoare logic of Phase 2 needed Löb only
    for the [while] rule, and even there a direct induction worked.
    Once we add [fix], the wp predicate itself becomes recursive in
    the program, and step-indexing is no longer an option — it is the
    only way to define the wp without circularity.

    The language has integer constants, addition, an [if0] conditional
    that branches on whether its argument is zero, λ-abstraction and
    application, and a fix-point operator [fix]. Variables are
    represented in de Bruijn index style.

    We give a call-by-value small-step semantics. As in Phase 2a, each
    small step corresponds to one decrement of the step-index clock.
*)

From Coq Require Import Arith Lia ZArith.

(** ** Syntax *)

Inductive expr : Type :=
  | EVar  : nat -> expr               (* de Bruijn index *)
  | EInt  : Z -> expr
  | EPlus : expr -> expr -> expr
  | EIf0  : expr -> expr -> expr -> expr
  | ELam  : expr -> expr               (* λ. body *)
  | EApp  : expr -> expr -> expr
  | EFix  : expr -> expr.              (* fix. body — self-ref at index 0 *)

(** Values: integers and the two value-forms of binders.  [EFix] is
    treated as a value so that it can be passed as an argument; the
    self-unfolding happens only when it is applied. *)

Inductive value : expr -> Prop :=
  | VInt : forall n, value (EInt n)
  | VLam : forall body, value (ELam body)
  | VFix : forall body, value (EFix body).

(** ** Lift and substitution

    Standard de Bruijn machinery. [shift d e] shifts every free
    variable of [e] at depth [≥ d] up by one. [subst_at k v e]
    substitutes [v] for the variable [k] in [e] and decrements every
    free variable strictly greater than [k]. [subst v e] is the
    common single-substitution at the top binder, used by both [β]
    and [fix] reduction. *)

Fixpoint shift (d : nat) (e : expr) : expr :=
  match e with
  | EVar n      => if Nat.leb d n then EVar (S n) else EVar n
  | EInt z      => EInt z
  | EPlus a b   => EPlus (shift d a) (shift d b)
  | EIf0 a b c  => EIf0 (shift d a) (shift d b) (shift d c)
  | ELam body   => ELam (shift (S d) body)
  | EApp f a    => EApp (shift d f) (shift d a)
  | EFix body   => EFix (shift (S d) body)
  end.

Fixpoint subst_at (k : nat) (v : expr) (e : expr) : expr :=
  match e with
  | EVar n =>
      match Nat.compare n k with
      | Eq => v
      | Lt => EVar n
      | Gt => EVar (pred n)
      end
  | EInt z      => EInt z
  | EPlus a b   => EPlus (subst_at k v a) (subst_at k v b)
  | EIf0 a b c  => EIf0 (subst_at k v a) (subst_at k v b) (subst_at k v c)
  | ELam body   => ELam (subst_at (S k) (shift 0 v) body)
  | EApp f a    => EApp (subst_at k v f) (subst_at k v a)
  | EFix body   => EFix (subst_at (S k) (shift 0 v) body)
  end.

Definition subst (v : expr) (e : expr) : expr := subst_at 0 v e.

(** ** Call-by-value small-step semantics *)

Reserved Notation "e1 '~>' e2" (at level 70).

Inductive step : expr -> expr -> Prop :=
  (* Arithmetic *)
  | StepPlusL : forall a a' b,
      a ~> a' -> EPlus a b ~> EPlus a' b
  | StepPlusR : forall v b b',
      value v -> b ~> b' -> EPlus v b ~> EPlus v b'
  | StepPlus  : forall n m,
      EPlus (EInt n) (EInt m) ~> EInt (n + m)%Z
  (* Conditional *)
  | StepIfCond : forall e1 e1' e2 e3,
      e1 ~> e1' -> EIf0 e1 e2 e3 ~> EIf0 e1' e2 e3
  | StepIf0    : forall e2 e3,
      EIf0 (EInt 0) e2 e3 ~> e2
  | StepIfN    : forall n e2 e3,
      n <> 0%Z -> EIf0 (EInt n) e2 e3 ~> e3
  (* Application *)
  | StepAppL : forall e1 e1' e2,
      e1 ~> e1' -> EApp e1 e2 ~> EApp e1' e2
  | StepAppR : forall v e2 e2',
      value v -> e2 ~> e2' -> EApp v e2 ~> EApp v e2'
  | StepBeta : forall body v,
      value v -> EApp (ELam body) v ~> subst v body
  (* Fix unfolding: the recursive function self-applies, then ordinary
     β does the rest of the work. *)
  | StepFix  : forall body v,
      value v -> EApp (EFix body) v ~> EApp (subst (EFix body) body) v
where "e1 '~>' e2" := (step e1 e2).

(** Iterated reduction.  Same shape as in Phase 2a. *)

Inductive steps : nat -> expr -> expr -> Prop :=
  | StepsO : forall e, steps 0 e e
  | StepsS : forall n e1 e2 e3,
      e1 ~> e2 -> steps n e2 e3 -> steps (S n) e1 e3.

(** ** Smoke test: the identity function applied to 5 *)

Example id_app_5 :
  steps 1 (EApp (ELam (EVar 0)) (EInt 5)) (EInt 5).
Proof.
  eapply StepsS; [apply StepBeta; constructor | apply StepsO].
Qed.

(** Smoke test: 2 + 3 reduces to 5. *)

Example two_plus_three :
  steps 1 (EPlus (EInt 2) (EInt 3)) (EInt 5).
Proof.
  eapply StepsS; [apply StepPlus | apply StepsO].
Qed.

(** Smoke test: fix unfolds when applied.

    Take [body = λ. (EVar 0)] — the identity (ignoring self-ref).
    Then [fix body] is [VFix (ELam (EVar 0))], and applied to [5]
    we should reduce to [5] in a small number of steps. *)

Example fix_id_5 :
  exists n, steps n (EApp (EFix (ELam (EVar 0))) (EInt 5)) (EInt 5).
Proof.
  exists 2.
  eapply StepsS.
  - apply StepFix. constructor.
  - simpl.
    eapply StepsS.
    + apply StepBeta. constructor.
    + simpl. apply StepsO.
Qed.
