(** * Phase 6: Bridge to forcing translations

    The Jaber–Tabareau–Sozeau forcing translation of CIC produces,
    for each forcing notion [P], a translation of any CIC term [M : T]
    into a forced term [M^P : T^P], where [T^P] is the "P-forced
    version" of [T].  At the level of propositions, the forced version
    of [Prop] is a downward-closed presheaf on the forcing conditions
    — which is exactly the [iProp] of Phase 1, and more generally the
    [iProp FS] of Phase 4.

    Phase 4's [iProp FS] is therefore *literally* the propositional
    fragment of the JTS forcing translation, instantiated at the
    forcing structure [FS].  This file makes the correspondence
    explicit.  The genuinely new content of step-indexed logic, over
    and above what the translation alone produces, is the [▷] modality
    (introduced via the well-founded strict refinement) and Löb's
    rule.

    The *propositional* half of that correspondence is mechanized in
    [Phase6b_JTS.v]: the translation itself, as a syntactic
    [Fixpoint], with the factorization theorem [jts_is_interp]
    (translation = iProp semantics, over any forcing structure) and
    [jts_Lob] (Löb transported to the translated syntax).  The
    *term-level* translation of full CIC remains future work.  Here we
    formalise the other, easy ingredient: the constant embedding
    [Prop → iProp] and the verification that it commutes with the
    Heyting-algebra connectives. *)

From Coq Require Import Arith Lia.
From ForcingHoare Require Import Phase1_Forcing.

(** ** The constant embedding

    [⌜ P ⌝] is the iProp that holds at every condition iff the meta-
    level proposition [P] is true.  This is the trivial part of the
    forcing translation: classical propositional reasoning lifts to
    the forcing framework without change. *)

Lemma embed_mono (P : Prop) :
  forall n m, m <= n -> (fun _ : cond => P) n -> (fun _ : cond => P) m.
Proof. auto. Qed.

Definition embed (P : Prop) : iProp :=
  MkProp (fun _ => P) (embed_mono P).

Notation "⌜ P ⌝" := (embed P) (at level 1, format "⌜ P ⌝").

(** ** Commutation with the connectives

    [⌜·⌝] is a Heyting algebra homomorphism: it commutes with [True],
    [False], [∧], and [→] up to entailment in both directions. *)

Lemma embed_True_l : ⌜ True ⌝ ⊢ iTrue.
Proof. intros n _; exact I. Qed.

Lemma embed_True_r : iTrue ⊢ ⌜ True ⌝.
Proof. intros n _; exact I. Qed.

Lemma embed_False_l : ⌜ False ⌝ ⊢ iFalse.
Proof. intros n H; exact H. Qed.

Lemma embed_False_r : iFalse ⊢ ⌜ False ⌝.
Proof. intros n H; exact H. Qed.

Lemma embed_and_intro P Q : ⌜ P /\ Q ⌝ ⊢ ⌜ P ⌝ ∧ ⌜ Q ⌝.
Proof. intros n [H1 H2]; split; assumption. Qed.

Lemma embed_and_elim P Q : ⌜ P ⌝ ∧ ⌜ Q ⌝ ⊢ ⌜ P /\ Q ⌝.
Proof. intros n [H1 H2]; split; assumption. Qed.

Lemma embed_or_intro P Q : ⌜ P \/ Q ⌝ ⊢ ⌜ P ⌝ ∨ ⌜ Q ⌝.
Proof. intros n [H|H]; [left|right]; assumption. Qed.

Lemma embed_or_elim P Q : ⌜ P ⌝ ∨ ⌜ Q ⌝ ⊢ ⌜ P \/ Q ⌝.
Proof. intros n [H|H]; [left|right]; assumption. Qed.

Lemma embed_impl_intro P Q : ⌜ P -> Q ⌝ ⊢ (⌜ P ⌝ → ⌜ Q ⌝).
Proof. intros n HPQ m Hmn HP. exact (HPQ HP). Qed.

Lemma embed_impl_elim P Q : (⌜ P ⌝ → ⌜ Q ⌝) ⊢ ⌜ P -> Q ⌝.
Proof. intros n H. exact (H n (Nat.le_refl n)). Qed.

(** ** The [▷] modality is genuine new content

    The embedded image of [Prop] in [iProp] does not include [▷]
    non-trivially: [▷ ⌜ P ⌝] is not, in general, entailment-equivalent
    to [⌜ P ⌝].  We exhibit a concrete witness. *)

Lemma embed_later_distinct :
  ~ (▷ ⌜ False ⌝ ⊢ ⌜ False ⌝).
Proof.
  intros H. apply (H 0). simpl. trivial.
Qed.

(** This mirrors [iLater_False_distinct] from Phase 1: the [▷]
    modality is what makes step-indexed logic *more* than the constant
    embedding of [Prop].  The JTS forcing translation alone produces
    the embedded image (and its closure under Heyting-algebra
    connectives, plus quantifiers).  Adding [▷] — equivalently,
    requiring a well-founded forcing notion and defining [▷ φ] as
    universal-over-strict-predecessors — is the step-indexed-specific
    move that gives us Löb's rule and lets us define recursive
    iProps. *)

(** ** Summary of the bridge

    - The framework of [Phase 4_Abstract.v] is the propositional
      fragment of the JTS forcing translation, parameterised by an
      arbitrary [ForcingStructure].
    - The instantiation at [nat_FS] recovers the topos-of-trees /
      Iris uPred convention used throughout Phases 1–3.
    - The constant embedding [⌜·⌝] formalised above shows that the
      classical propositional theory embeds faithfully into [iProp].
    - The [▷] modality and Löb's rule are not in the embedded image:
      they are the *forcing-specific* structure of the framework. *)
