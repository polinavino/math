(** * Phase 5: Metatheoretic results — Löb's rule is essential

    In the abstract framework of Phase 4, the [ForcingStructure]
    record required the strict refinement relation [fs_lt] to be
    well-founded.  Is this axiom essential, or just a convenience
    used in the [iLob] proof?

    We answer: essential.  We exhibit a "would-be" forcing notion
    where the carrier is [Z] with [<=] and [<].  All the iProp
    constructions go through except [iLob].  Concretely, we show that
    the premise of Löb's rule, [(▷ ⊥) → ⊥], is forced at every
    condition, while [⊥] is not.  Hence Löb's rule fails.

    This is the step-indexed analog of the well-known characterisation
    in modal logic: the Gödel–Löb axiom is sound on the class of
    transitive Kripke frames whose accessibility relation is *converse
    well-founded*.  Without that converse well-foundedness — here,
    well-foundedness of the strict refinement relation — Löb's rule
    cannot be derived.

    The conceptual upshot is that the "ramification" in ramified
    forcing is not merely a presentation convenience: the well-founded
    level structure is *constitutive* of the modal logic.  Step-indexed
    Hoare logic *requires* a well-founded forcing notion. *)

From Coq Require Import ZArith Lia.

Open Scope Z_scope.

(** ** A would-be iProp framework over [Z]

    Note: there is no [ForcingStructure] instance here, because [Z]
    does not satisfy well-foundedness of [<].  We build the iProp
    structure directly. *)

Record iPropZ : Type := MkPropZ {
  iholdZ : Z -> Prop;
  imonoZ : forall p q, q <= p -> iholdZ p -> iholdZ q
}.

Notation "p '⊩' φ" := (iholdZ φ p) (at level 80, no associativity).

Definition ientailsZ (φ ψ : iPropZ) : Prop :=
  forall p, p ⊩ φ -> p ⊩ ψ.

Notation "φ '⊨⊢' ψ" := (ientailsZ φ ψ) (at level 99, no associativity).

(** ** Connectives we need: ⊥, →, ▷ *)

Definition iFalseZ : iPropZ :=
  MkPropZ (fun _ => False) (fun _ _ _ H => H).

Lemma iImplZ_mono (φ ψ : iPropZ) :
  forall p q, q <= p ->
    (forall r, r <= p -> r ⊩ φ -> r ⊩ ψ) ->
    (forall r, r <= q -> r ⊩ φ -> r ⊩ ψ).
Proof. intros p q Hpq H r Hrq. apply H. lia. Qed.

Definition iImplZ (φ ψ : iPropZ) : iPropZ :=
  MkPropZ
    (fun p => forall q, q <= p -> q ⊩ φ -> q ⊩ ψ)
    (iImplZ_mono φ ψ).

Lemma iLaterZ_mono (φ : iPropZ) :
  forall p q, q <= p ->
    (forall p', p' < p -> p' ⊩ φ) ->
    (forall q', q' < q -> q' ⊩ φ).
Proof. intros p q Hpq H q' Hq'. apply H. lia. Qed.

Definition iLaterZ (φ : iPropZ) : iPropZ :=
  MkPropZ
    (fun p => forall p', p' < p -> p' ⊩ φ)
    (iLaterZ_mono φ).

Notation "'⊥Z'" := iFalseZ.
Notation "'▷Z' φ" := (iLaterZ φ) (at level 20, right associativity).

(** ** The counterexample

    The premise of Löb's rule, [(▷ ⊥) → ⊥], is forced at every
    condition.  Reason: [▷ ⊥] requires "[⊥] at every strict
    predecessor."  Because [Z] has no minimum, every condition [q]
    has the strict predecessor [q - 1], at which [⊥] is False.  So
    [q ⊩ ▷ ⊥] is False at every [q] — and a false antecedent makes
    the implication vacuously true. *)

Lemma lob_premise_at p :
  p ⊩ iImplZ (▷Z ⊥Z) ⊥Z.
Proof.
  intros q Hqp Hlater.
  (* [Hlater : ∀ q' < q, False]. Apply at [q' := q - 1]. *)
  apply (Hlater (q - 1)); lia.
Qed.

Lemma lob_premise_valid :
  forall p, p ⊩ iImplZ (▷Z ⊥Z) ⊥Z.
Proof. apply lob_premise_at. Qed.

(** The conclusion of Löb's rule — that [⊥] itself is forced
    everywhere — is plainly false: at any [p], [p ⊩ ⊥] is just
    [False]. *)

Lemma lob_conclusion_fails :
  ~ (forall p, p ⊩ ⊥Z).
Proof. intros H. exact (H 0). Qed.

(** ** The main theorem: Löb's rule does not hold over [Z]. *)

Theorem lob_fails_over_Z :
  ~ (iImplZ (▷Z ⊥Z) ⊥Z ⊨⊢ ⊥Z).
Proof.
  intros Hent. apply lob_conclusion_fails.
  intros p. apply Hent. apply lob_premise_valid.
Qed.

(** ** Corollary: well-foundedness is essential

    Phase 4's [ForcingStructure] requires [fs_lt_wf : well_founded fs_lt].
    The above shows that this axiom cannot be dropped while preserving
    the validity of [iLob]: any "ForcingStructure-without-wf" admits
    interpretations like the one above where [iLob] fails. *)
