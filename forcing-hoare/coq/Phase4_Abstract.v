(** * Phase 4: An abstract forcing framework

    Phase 1 was specific to ω = [nat] with [<=].  Here we abstract the
    forcing notion: given any preorder equipped with a well-founded
    strict refinement relation, the whole step-indexed logic — Heyting
    algebra, the later modality, and Löb's rule — goes through with
    no change.  Phase 1 is exactly the instantiation at the natural
    numbers; we recover it at the end of the file.

    The conceptual point: the "ramification" in "ramified forcing" is
    not specifically the [nat]-indexed stratification.  Any
    well-founded forcing notion supports the same internal logic with
    the same modal structure.  This is what makes the "ramification"
    description appropriate — it is the well-founded level
    stratification, irrespective of which order indexes it.

    The slick definition of [▷]: at a condition [p], [▷ φ] holds iff
    [φ] holds at *every strict predecessor* of [p].  At a minimal
    condition (one with no predecessors), this is vacuously [True].
    On [(nat, <=)] this is equivalent (via downward closure) to the
    "shift" definition of [▷] from Phase 1.

    The slick proof of Löb: well-founded induction on the strict
    refinement relation.  At each [p], the induction hypothesis gives
    [φ] at every strict predecessor, which is exactly the antecedent
    [▷ φ] of the rule's premise. *)

From Coq Require Import Arith Lia Wellfounded Wf_nat.

(** ** The structure of an abstract forcing notion *)

Record ForcingStructure : Type := MkFS {
  fs_cond : Type;
  fs_le : fs_cond -> fs_cond -> Prop;
  fs_lt : fs_cond -> fs_cond -> Prop;
  fs_le_refl : forall p, fs_le p p;
  fs_le_trans : forall p q r, fs_le p q -> fs_le q r -> fs_le p r;
  fs_lt_le : forall p q, fs_lt p q -> fs_le p q;
  fs_lt_le_lt : forall p q r, fs_lt p q -> fs_le q r -> fs_lt p r;
  fs_lt_wf : well_founded fs_lt
}.

Section AbstractForcing.
  Variable FS : ForcingStructure.

  Let cond := fs_cond FS.
  Let le := fs_le FS.
  Let lt := fs_lt FS.

  Local Notation "p ≼ q" := (le p q) (at level 70).
  Local Notation "p ≺ q" := (lt p q) (at level 70).

  (** ** Step-indexed propositions *)

  Record iProp : Type := MkProp {
    ihold : cond -> Prop;
    imono : forall p q, q ≼ p -> ihold p -> ihold q
  }.

  Local Notation "p ⊩ φ" := (ihold φ p) (at level 80, no associativity).

  Definition ientails (φ ψ : iProp) : Prop :=
    forall p, p ⊩ φ -> p ⊩ ψ.
  Local Notation "φ ⊢ ψ" := (ientails φ ψ) (at level 99, no associativity).

  Lemma ientails_refl φ : φ ⊢ φ.
  Proof. intros p H; exact H. Qed.

  Lemma ientails_trans φ ψ χ : φ ⊢ ψ -> ψ ⊢ χ -> φ ⊢ χ.
  Proof. intros H1 H2 p H. apply H2, H1, H. Qed.

  (** ** Connectives *)

  Definition iTrue : iProp :=
    MkProp (fun _ => True) (fun _ _ _ _ => I).

  Definition iFalse : iProp :=
    MkProp (fun _ => False) (fun _ _ _ H => H).

  Lemma iAnd_mono (φ ψ : iProp) :
    forall p q, q ≼ p -> (p ⊩ φ /\ p ⊩ ψ) -> (q ⊩ φ /\ q ⊩ ψ).
  Proof. intros p q Hpq [H1 H2]. split; eapply imono; eauto. Qed.

  Definition iAnd (φ ψ : iProp) : iProp :=
    MkProp (fun p => p ⊩ φ /\ p ⊩ ψ) (iAnd_mono φ ψ).

  Lemma iOr_mono (φ ψ : iProp) :
    forall p q, q ≼ p -> (p ⊩ φ \/ p ⊩ ψ) -> (q ⊩ φ \/ q ⊩ ψ).
  Proof.
    intros p q Hpq [H|H]; [left|right]; eapply imono; eauto.
  Qed.

  Definition iOr (φ ψ : iProp) : iProp :=
    MkProp (fun p => p ⊩ φ \/ p ⊩ ψ) (iOr_mono φ ψ).

  Lemma iImpl_mono (φ ψ : iProp) :
    forall p q, q ≼ p ->
      (forall r, r ≼ p -> r ⊩ φ -> r ⊩ ψ) ->
      (forall r, r ≼ q -> r ⊩ φ -> r ⊩ ψ).
  Proof.
    intros p q Hpq H r Hrq.
    apply H. eapply (fs_le_trans FS); eauto.
  Qed.

  Definition iImpl (φ ψ : iProp) : iProp :=
    MkProp (fun p => forall q, q ≼ p -> q ⊩ φ -> q ⊩ ψ) (iImpl_mono φ ψ).

  Local Notation "'⊤'" := iTrue.
  Local Notation "'⊥'" := iFalse.
  Local Notation "φ '∧' ψ" := (iAnd φ ψ) (at level 80, right associativity).
  Local Notation "φ '→' ψ" := (iImpl φ ψ) (at level 99, right associativity).

  (** ** The later modality, as universal-over-strict-predecessors

      [▷ φ] at [p]: at every strict predecessor of [p], [φ] holds.
      At a minimal condition (no strict predecessors), this is
      vacuously [True].  Specialised to [nat] with [<=], this is
      equivalent — by downward closure of [φ] — to the "shift by one"
      [▷] of Phase 1. *)

  Lemma iLater_mono_helper (φ : iProp) :
    forall p q, q ≼ p ->
      (forall p', p' ≺ p -> p' ⊩ φ) ->
      (forall q', q' ≺ q -> q' ⊩ φ).
  Proof.
    intros p q Hpq H q' Hq'.
    apply H. eapply (fs_lt_le_lt FS); eauto.
  Qed.

  Definition iLater (φ : iProp) : iProp :=
    MkProp (fun p => forall p', p' ≺ p -> p' ⊩ φ) (iLater_mono_helper φ).

  Local Notation "'▷' φ" := (iLater φ) (at level 20, right associativity).

  (** ** Löb's rule, via well-founded induction *)

  Lemma iLob (φ : iProp) : (▷ φ → φ) ⊢ φ.
  Proof.
    intros p. revert p.
    apply (well_founded_ind (fs_lt_wf FS)
                            (fun p => p ⊩ (▷ φ → φ) -> p ⊩ φ)).
    intros p IH Hp.
    (* [Hp] is the premise of Löb applied at [p].  Apply it at [p]
       itself (via [le_refl]); we owe it a proof of [▷ φ at p]. *)
    apply Hp; [apply (fs_le_refl FS)|].
    (* [▷ φ at p] means: at every strict predecessor [p'], [φ] holds.
       For each such [p'], the well-founded IH applies. *)
    intros p' Hp'.
    apply IH; [exact Hp'|].
    (* IH needs [p' ⊩ (▷ φ → φ)], which we get from [Hp] (= [p ⊩ ...])
       by downward closure, since [p' ≺ p] implies [p' ≼ p]. *)
    eapply imono; [apply (fs_lt_le FS); exact Hp' | exact Hp].
  Qed.

End AbstractForcing.

(** ** Instantiation: the natural numbers with [<=]

    The Phase 1 framework is the instantiation of this abstract
    framework at [nat] with the standard [<=].  The strict relation
    is the standard [<], which is well-founded.  At this instance,
    the [▷] of Phase 4 (universal over strict predecessors) coincides
    — via downward closure of [iProp]s — with the "shift by one" [▷]
    of Phase 1. *)

Definition nat_FS : ForcingStructure :=
  {| fs_cond := nat;
     fs_le := Nat.le;
     fs_lt := Nat.lt;
     fs_le_refl := Nat.le_refl;
     fs_le_trans := Nat.le_trans;
     fs_lt_le := Nat.lt_le_incl;
     fs_lt_le_lt := Nat.lt_le_trans;
     fs_lt_wf := lt_wf
  |}.

(** A small confirmation that [iLob] does instantiate at [nat_FS].
    (The framework's [iLob] takes [FS] as a first argument; here we
    just check that the [nat] instance is well-typed.) *)
Check iLob nat_FS.

(** ** A second instance: [nat × nat] with pointwise order

    The pointwise (product) order on [nat × nat] is genuinely a
    different poset from [nat] — it is not totally ordered.  Its
    natural interpretation is independent step-indices for two
    parallel components (two threads of a concurrent computation,
    two independent observers, etc.). The framework applies without
    change. *)

Definition le_pair (p q : nat * nat) : Prop :=
  fst p <= fst q /\ snd p <= snd q.

Definition lt_pair (p q : nat * nat) : Prop :=
  le_pair p q /\ ~ (fst p = fst q /\ snd p = snd q).

Lemma le_pair_refl p : le_pair p p.
Proof. unfold le_pair; lia. Qed.

Lemma le_pair_trans p q r :
  le_pair p q -> le_pair q r -> le_pair p r.
Proof. unfold le_pair; intros [] []; lia. Qed.

Lemma lt_pair_le_pair p q : lt_pair p q -> le_pair p q.
Proof. intros [Hle _]; exact Hle. Qed.

Lemma lt_pair_le_pair_lt p q r :
  lt_pair p q -> le_pair q r -> lt_pair p r.
Proof.
  intros [Hpq Hneq] Hqr. split.
  - eapply le_pair_trans; eauto.
  - intros [Hf Hs]. apply Hneq.
    destruct p, q, r; simpl in *.
    unfold le_pair in *; simpl in *.
    split; lia.
Qed.

Lemma lt_pair_wf : well_founded lt_pair.
Proof.
  apply (well_founded_lt_compat _ (fun p => fst p + snd p)).
  intros p q [[Hf Hs] Hneq].
  destruct p, q; simpl in *.
  destruct (Nat.eq_dec n n1).
  - subst. destruct (Nat.eq_dec n0 n2).
    + subst. exfalso. apply Hneq. split; reflexivity.
    + lia.
  - lia.
Qed.

Definition prod_FS : ForcingStructure :=
  {| fs_cond := nat * nat;
     fs_le := le_pair;
     fs_lt := lt_pair;
     fs_le_refl := le_pair_refl;
     fs_le_trans := le_pair_trans;
     fs_lt_le := lt_pair_le_pair;
     fs_lt_le_lt := lt_pair_le_pair_lt;
     fs_lt_wf := lt_pair_wf
  |}.

(** Sanity: the abstract [iLob] instantiates here too. *)
Check iLob prod_FS.
