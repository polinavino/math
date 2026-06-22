(** * Phase 5c: The induction-on-n / internal-Löb equivalence,
      for depth-recursive soundness predicates

    Section 5 of the paper observes that for IMP-style recursive Hoare
    rules, meta-level induction on the step index and an appeal to the
    internal Löb rule produce structurally identical proofs.  We try
    to formalize this observation here.

    The cleanest statement we can extract is the following.  Suppose
    [Phi : nat -> Prop] is any downward-closed predicate.  Let
    [embed Phi : iProp] be the corresponding iProp.  Then the three
    statements

    - [forall n, Phi n]              (meta-level induction on n)
    - [⊤ ⊢ embed Phi]                (iProp validity)
    - [⊤ ⊢ ▷ (embed Phi) → embed Phi] (Löb-form)

    are equivalent.  The third entailment is the form of statement
    that [iLob] discharges.  The equivalence shows that for any
    depth-recursive iProp [φ], the meta-level induction-on-[n] proof
    and the internal-Löb proof close the same goal.

    This equivalence does not extend to predicates whose recursion
    locus is in the program (Section~\ref{sec:imp-vs-lam} of the
    paper).  For [recursive_spec (EFix body) S], the iProp is not of
    the shape [embed Phi] for any [Phi : nat -> Prop] that decomposes
    cleanly into a step-counting predicate alone; the program
    [EFix body] is a parameter, and the recursion in the spec touches
    it.  The equivalence we exhibit here is therefore a precise tool
    that applies in the IMP-style setting and explains why both proof
    styles work there, but does not apply to the [λ-fix] case --- a
    structural reason for the recursion-locus distinction. *)

From Coq Require Import Arith Lia.
From ForcingHoare Require Import Phase1_Forcing.

(** ** Embedding a downward-closed nat-predicate as an iProp *)

Definition embed_nat (Phi : nat -> Prop)
                     (Hmono : forall n m, m <= n -> Phi n -> Phi m)
                     : iProp :=
  MkProp Phi Hmono.

(** ** Forward and backward equivalences *)

Lemma embed_meta_to_iprop (Phi : nat -> Prop)
                          (Hmono : forall n m, m <= n -> Phi n -> Phi m) :
  (forall n, Phi n) -> ⊤ ⊢ embed_nat Phi Hmono.
Proof. intros H n _. apply H. Qed.

Lemma embed_iprop_to_meta (Phi : nat -> Prop)
                          (Hmono : forall n m, m <= n -> Phi n -> Phi m) :
  ⊤ ⊢ embed_nat Phi Hmono -> (forall n, Phi n).
Proof. intros H n. apply (H n I). Qed.

(** ** The Löb form, and the three-way equivalence

    The Löb-form entailment [⊤ ⊢ ▷ φ → φ] is the input to [iLob].  We
    show it is equivalent to [⊤ ⊢ φ] in our setting, via [iLob] in one
    direction and the trivial entailment [φ ⊢ ▷ φ → φ] in the other.
    The three-way equivalence with [forall n, Phi n] follows. *)

Lemma lob_form_to_iprop (phi : iProp) :
  ⊤ ⊢ (▷ phi → phi) -> ⊤ ⊢ phi.
Proof.
  intros H. eapply ientails_trans; [exact H | apply iLob].
Qed.

Lemma iprop_to_lob_form (phi : iProp) :
  ⊤ ⊢ phi -> ⊤ ⊢ (▷ phi → phi).
Proof.
  intros H n _ m Hmn Hlater.
  apply (H m I).
Qed.

(** ** The packaged equivalence *)

Theorem induction_iLob_equiv (Phi : nat -> Prop)
                             (Hmono : forall n m, m <= n -> Phi n -> Phi m) :
  let phi := embed_nat Phi Hmono in
  (forall n, Phi n) <->
  (⊤ ⊢ phi) /\
  ((⊤ ⊢ phi) <-> (⊤ ⊢ (▷ phi → phi))).
Proof.
  simpl. split.
  - intros Hmeta.
    split.
    + apply embed_meta_to_iprop, Hmeta.
    + split.
      * apply iprop_to_lob_form.
      * apply lob_form_to_iprop.
  - intros [Hphi _].
    apply (embed_iprop_to_meta Phi Hmono Hphi).
Qed.

(** ** Application to the IMP setting

    The IMP wp-at predicate [fun n => forall s, P s -> wp_at n c Q s]
    is exactly of the [embed_nat]-able shape: it is a predicate on
    [nat] whose body refers to a step-indexed wp_at, which is
    downward-closed in [n].  The equivalence above therefore explains
    why both [hoare_while] and [hoare_while_iLob] close the same goal:
    they are two routes between the equivalent forms of a single
    statement about a depth-recursive iProp. *)
