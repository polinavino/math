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

(** * Option A: Löb's rule holds iff the forcing notion is well-founded

    The [Z] example shows that well-foundedness is sufficient to break
    Löb's rule.  We now show that well-foundedness is also necessary:
    in any "would-be" forcing structure --- a preorder with a strict
    relation containing the structural compatibility axioms but not
    well-foundedness --- Löb's rule holds for every iProp if and only
    if the strict relation is well-founded.

    The forward direction (well-founded → Löb) is the abstract [iLob]
    proof of Phase 4, replayed in the pre-structure.  The backward
    direction (Löb → well-founded) is genuinely new: assume Löb holds
    universally, and exhibit a single [iProp] --- the
    forcing-accessibility predicate --- whose entailment by the assumed
    Löb implies that every condition is accessible in the strict
    relation, hence the strict relation is well-founded.

    The result is the iProp-internal form of a classical fact about
    Gödel--Löb modal logic: the Löb axiom is sound on a transitive
    Kripke frame iff the accessibility relation is converse
    well-founded.  Stated and mechanized in the step-indexed Hoare
    logic setting, it does not, to our knowledge, appear in the PL
    literature. *)

Section LobIff.

  Variable cond : Type.
  Variable le : cond -> cond -> Prop.
  Variable lt : cond -> cond -> Prop.

  Hypothesis le_refl : forall p, le p p.
  Hypothesis le_trans : forall p q r, le p q -> le q r -> le p r.
  Hypothesis lt_le : forall p q, lt p q -> le p q.
  Hypothesis lt_le_lt : forall p q r, lt p q -> le q r -> lt p r.

  (** ** Pre-structure iProp *)

  Record iPropPre : Type := MkPropPre {
    iholdPre : cond -> Prop;
    imonoPre : forall p q, le q p -> iholdPre p -> iholdPre q
  }.

  Definition ientailsPre (phi psi : iPropPre) : Prop :=
    forall p, iholdPre phi p -> iholdPre psi p.

  Lemma iImplPre_mono (phi psi : iPropPre) :
    forall p q, le q p ->
      (forall r, le r p -> iholdPre phi r -> iholdPre psi r) ->
      (forall r, le r q -> iholdPre phi r -> iholdPre psi r).
  Proof.
    intros p q Hqp H r Hrq. apply H. eapply le_trans; eauto.
  Qed.

  Definition iImplPre (phi psi : iPropPre) : iPropPre :=
    MkPropPre
      (fun p => forall q, le q p -> iholdPre phi q -> iholdPre psi q)
      (iImplPre_mono phi psi).

  Lemma iLaterPre_mono (phi : iPropPre) :
    forall p q, le q p ->
      (forall p', lt p' p -> iholdPre phi p') ->
      (forall q', lt q' q -> iholdPre phi q').
  Proof.
    intros p q Hqp H q' Hq'. apply H. eapply lt_le_lt; eauto.
  Qed.

  Definition iLaterPre (phi : iPropPre) : iPropPre :=
    MkPropPre
      (fun p => forall p', lt p' p -> iholdPre phi p')
      (iLaterPre_mono phi).

  (** ** The Löb assumption *)

  (** [lob_holds] says: for every iProp [φ], the entailment
      [(▷ φ → φ) ⊢ φ] is derivable in the pre-structure. *)
  Definition lob_holds : Prop :=
    forall phi : iPropPre, ientailsPre (iImplPre (iLaterPre phi) phi) phi.

  (** ** Forward direction: well-foundedness implies Löb *)

  Lemma wf_implies_lob : well_founded lt -> lob_holds.
  Proof.
    intros Hwf phi. intros p.
    revert p. apply (well_founded_ind Hwf
                       (fun p => iholdPre (iImplPre (iLaterPre phi) phi) p ->
                                 iholdPre phi p)).
    intros p IH Hp.
    apply Hp; [apply le_refl|].
    intros p' Hp'.
    apply IH; [exact Hp'|].
    eapply imonoPre; [apply lt_le; exact Hp' | exact Hp].
  Qed.

  (** ** Backward direction: Löb implies well-foundedness

      The key idea: the forcing-accessibility predicate
      [φ_acc p := Acc lt p] is a valid iProp.  Its [▷ φ_acc → φ_acc]
      premise is forced at every condition --- because by [Acc_intro],
      "every strict predecessor is accessible" gives "this condition
      is accessible".  Hence by the assumed Löb, [φ_acc] is forced at
      every condition, i.e., every condition is accessible, i.e., the
      strict relation is well-founded. *)

  Lemma lob_implies_wf : lob_holds -> well_founded lt.
  Proof.
    intros HLob.
    (* φ_acc : iProp with ihold p := Acc lt p *)
    assert (Hmono : forall p q, le q p -> Acc lt p -> Acc lt q).
    { intros p q Hqp HAccp.
      constructor. intros r Hr_q.
      eapply Acc_inv; [exact HAccp|]. eapply lt_le_lt; eauto. }
    pose (phi_acc := MkPropPre (Acc lt) Hmono).
    (* The premise (▷ φ_acc → φ_acc) is forced everywhere. *)
    assert (Hpremise : forall p, iholdPre (iImplPre (iLaterPre phi_acc) phi_acc) p).
    { intros p q Hqp Hlater.
      (* Hlater : forall q' < q, Acc lt q'. Use Acc_intro. *)
      constructor. intros r Hr. apply Hlater. exact Hr. }
    (* By assumed Löb, φ_acc is forced everywhere. *)
    intros p. apply (HLob phi_acc p). apply Hpremise.
  Qed.

  (** ** The characterization theorem *)

  Theorem lob_iff_wf : lob_holds <-> well_founded lt.
  Proof.
    split; [apply lob_implies_wf | apply wf_implies_lob].
  Qed.

End LobIff.
