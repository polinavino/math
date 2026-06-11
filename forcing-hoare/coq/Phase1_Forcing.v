(** * Phase 1: A forcing-style semantics for step-indexed propositional logic

    We give a Kripke / Cohen-style forcing semantics for an
    intuitionistic propositional logic equipped with a "later" modality
    [▷].  The forcing conditions are natural numbers — the
    "approximation depths" of step-indexed reasoning.

    ** Dictionary with set-theoretic forcing

    In set-theoretic forcing one takes a poset of conditions (P, ≤)
    where p ≤ q means "p extends / is stronger than q," and a
    proposition φ is forced by p iff every stronger condition also
    forces φ.  Here we take P := nat with the convention that
    SMALLER naturals are STRONGER conditions: condition n records
    "we have observed n steps of the program; smaller n means we
    have committed to a weaker, less-refined view."  Under this
    reading the forcing extension order is the OPPOSITE of [≤_nat],
    and propositions are downward-closed in [≤_nat] — equivalently
    upward-closed in the (Cohen) extension order.

    This is the topos-of-trees / Iris uPred convention; the order-dual
    matches the usual Cohen presentation but breaks monotonicity of [▷].
*)

From Coq Require Import Arith Lia.

(** ** Conditions and propositions *)

Definition cond : Type := nat.

(** A step-indexed proposition: a predicate on conditions that is
    downward-closed in [<=] on naturals. *)
Record iProp : Type := MkProp {
  ihold : cond -> Prop;
  imono : forall n m, m <= n -> ihold n -> ihold m
}.

(** Forcing notation: [n ⊩ φ] reads "condition n forces φ." *)
Notation "n ⊩ φ" := (ihold φ n) (at level 80, no associativity).

(** Internal entailment: [φ ⊢ ψ] iff every condition forcing φ
    also forces ψ. *)
Definition ientails (φ ψ : iProp) : Prop :=
  forall n, n ⊩ φ -> n ⊩ ψ.
Notation "φ ⊢ ψ" := (ientails φ ψ) (at level 99, no associativity).

Lemma ientails_refl φ : φ ⊢ φ.
Proof. intros n H; exact H. Qed.

Lemma ientails_trans φ ψ χ : φ ⊢ ψ -> ψ ⊢ χ -> φ ⊢ χ.
Proof. intros H1 H2 n H; apply H2, H1, H. Qed.

(** ** Propositional connectives *)

Definition iTrue : iProp :=
  MkProp (fun _ => True) (fun _ _ _ _ => I).

Definition iFalse : iProp :=
  MkProp (fun _ => False) (fun _ _ _ H => H).

Lemma iAnd_mono (φ ψ : iProp) :
  forall n m, m <= n -> (n ⊩ φ /\ n ⊩ ψ) -> (m ⊩ φ /\ m ⊩ ψ).
Proof. intros n m Hmn [H1 H2]; split; eapply imono; eauto. Qed.

Definition iAnd (φ ψ : iProp) : iProp :=
  MkProp (fun n => n ⊩ φ /\ n ⊩ ψ) (iAnd_mono φ ψ).

Lemma iOr_mono (φ ψ : iProp) :
  forall n m, m <= n -> (n ⊩ φ \/ n ⊩ ψ) -> (m ⊩ φ \/ m ⊩ ψ).
Proof. intros n m Hmn [H|H]; [left|right]; eapply imono; eauto. Qed.

Definition iOr (φ ψ : iProp) : iProp :=
  MkProp (fun n => n ⊩ φ \/ n ⊩ ψ) (iOr_mono φ ψ).

(** Kripke implication: [φ → ψ] at n iff every m ≤ n that forces
    φ also forces ψ.  The quantification over stronger conditions
    (= smaller naturals) is essential for intuitionistic implication. *)
Lemma iImpl_mono (φ ψ : iProp) :
  forall n m, m <= n ->
    (forall k, k <= n -> k ⊩ φ -> k ⊩ ψ) ->
    (forall k, k <= m -> k ⊩ φ -> k ⊩ ψ).
Proof. intros n m Hmn H k Hk Hφ; apply H; [lia | exact Hφ]. Qed.

Definition iImpl (φ ψ : iProp) : iProp :=
  MkProp (fun n => forall m, m <= n -> m ⊩ φ -> m ⊩ ψ) (iImpl_mono φ ψ).

Notation "'⊤'" := iTrue.
Notation "'⊥'" := iFalse.
Notation "φ '∧' ψ" := (iAnd φ ψ) (at level 80, right associativity).
Notation "φ '∨' ψ" := (iOr φ ψ) (at level 85, right associativity).
Notation "φ '→' ψ" := (iImpl φ ψ) (at level 99, right associativity).

(** ** The later modality

    [▷ φ] holds at depth n iff n = 0 (we have no observation budget
    left and the modality is vacuously satisfied) or φ holds at the
    shallower depth n-1.  Equivalently, [▷ φ] "forgets one step of
    refinement." *)

Definition later_at (φ : iProp) (n : cond) : Prop :=
  match n with 0 => True | S k => k ⊩ φ end.

Lemma iLater_mono_helper (φ : iProp) :
  forall n m, m <= n -> later_at φ n -> later_at φ m.
Proof.
  intros n m Hmn Hn.
  destruct n as [|n']; destruct m as [|m']; simpl in *; auto; try lia.
  eapply imono; [|exact Hn]. lia.
Qed.

Definition iLater (φ : iProp) : iProp :=
  MkProp (later_at φ) (iLater_mono_helper φ).

Notation "'▷' φ" := (iLater φ) (at level 20, right associativity).

(** ** Heyting algebra laws *)

Lemma iTrue_intro φ : φ ⊢ ⊤.
Proof. intros n _; exact I. Qed.

Lemma iFalse_elim φ : ⊥ ⊢ φ.
Proof. intros n []. Qed.

Lemma iAnd_proj_l φ ψ : φ ∧ ψ ⊢ φ.
Proof. intros n [H _]; exact H. Qed.

Lemma iAnd_proj_r φ ψ : φ ∧ ψ ⊢ ψ.
Proof. intros n [_ H]; exact H. Qed.

Lemma iAnd_intro φ ψ χ : φ ⊢ ψ -> φ ⊢ χ -> φ ⊢ ψ ∧ χ.
Proof. intros H1 H2 n Hn; split; auto. Qed.

Lemma iOr_intro_l φ ψ : φ ⊢ φ ∨ ψ.
Proof. intros n H; left; exact H. Qed.

Lemma iOr_intro_r φ ψ : ψ ⊢ φ ∨ ψ.
Proof. intros n H; right; exact H. Qed.

Lemma iOr_elim φ ψ χ : φ ⊢ χ -> ψ ⊢ χ -> φ ∨ ψ ⊢ χ.
Proof. intros H1 H2 n [H|H]; auto. Qed.

Lemma iImpl_intro φ ψ χ : φ ∧ ψ ⊢ χ -> φ ⊢ (ψ → χ).
Proof.
  intros H n Hn m Hm Hψ.
  apply H; split; [eapply imono; eauto | exact Hψ].
Qed.

Lemma iImpl_elim φ ψ : (φ → ψ) ∧ φ ⊢ ψ.
Proof. intros n [H1 H2]; apply H1; [lia | exact H2]. Qed.

(** ** Properties of the later modality *)

Lemma iLater_mono φ ψ : φ ⊢ ψ -> ▷ φ ⊢ ▷ ψ.
Proof.
  intros H n Hn; destruct n as [|n']; simpl in *; auto.
Qed.

Lemma iLater_intro φ : φ ⊢ ▷ φ.
Proof.
  intros n Hn; destruct n as [|n']; simpl; auto.
  eapply imono; [|exact Hn]; lia.
Qed.

Lemma iLater_True : ⊤ ⊢ ▷ ⊤.
Proof. intros n _; destruct n; simpl; exact I. Qed.

Lemma iLater_and_intro φ ψ : ▷ φ ∧ ▷ ψ ⊢ ▷ (φ ∧ ψ).
Proof.
  intros n [H1 H2]; destruct n as [|n']; simpl in *; auto.
Qed.

Lemma iLater_and_elim φ ψ : ▷ (φ ∧ ψ) ⊢ ▷ φ ∧ ▷ ψ.
Proof.
  intros n H; destruct n as [|n']; simpl in *; auto.
Qed.

(** Löb's rule.  This is the rule that distinguishes step-indexed
    logic from ordinary intuitionistic logic and powers all recursive
    reasoning in step-indexed Hoare logic. *)
Lemma iLob φ : (▷ φ → φ) ⊢ φ.
Proof.
  intros n Hn.
  induction n as [|n IH].
  - apply (Hn 0); [lia | exact I].
  - apply (Hn (S n)); [lia | simpl].
    apply IH.
    intros m Hm Hlate.
    apply (Hn m); [lia | exact Hlate].
Qed.

(** ** Sanity check: [▷ ⊥ ⊬ ⊥]

    In pure intuitionistic logic, [▷ ⊥] and [⊥] would be
    interderivable; here they are not.  This is the canonical witness
    that step-indexing genuinely changes the propositional theory.
*)

Lemma iLater_False_distinct : ~ (▷ ⊥ ⊢ ⊥).
Proof. intros H. apply (H 0); simpl; exact I. Qed.

Lemma iLater_False_intro : ⊥ ⊢ ▷ ⊥.
Proof. apply iLater_intro. Qed.
