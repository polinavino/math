(** * Phase 4b: A transfinite instance, and a sentence that separates it from ω

    Phase 4 proves that the step-indexed logic — connectives, [▷],
    Löb — works over an arbitrary well-founded forcing structure.
    This file makes the abstraction *earn its keep*: we instantiate
    the framework at the lexicographic order on [nat * nat], whose
    order type is ω·ω = ω², and we mechanize a concrete propositional
    sentence that distinguishes it from the ω-instance [nat_FS].

    ω² is not an arbitrary choice: it is exactly the index structure
    of Svendsen–Sieczkowski–Birkedal's *transfinite step-indexing*
    (ESOP 2016), introduced there to decouple concrete from logical
    steps; Transfinite Iris (Spies et al., 2021) generalizes the same
    move to arbitrary ordinals to recover liveness-style
    ("existential") properties that ω-indexing provably cannot
    express.  The separation below is the propositional core of that
    phenomenon, stated and proved inside our framework:

    - **Over ω, the later modality exhausts.**  For every condition
      [n], the iterate [▷^(n+1) ⊥] is forced at [n]
      ([nat_laterN_bot]): once the iteration depth exceeds the index,
      [▷^k φ] is forced *no matter what φ is* — iterated [▷] runs out
      of content.  Every condition trivializes some finite iterate
      ([nat_exhausts]).

    - **Over ω², it does not.**  At the condition [(1,0)] — the
      first limit point, with the infinite descending fan
      [(0,0) ≺ (0,1) ≺ (0,2) ≺ ⋯ ≺ (1,0)] — *no* finite iterate
      [▷^k ⊥] is ever forced ([lex_laterN_bot_never]): there are
      strict descending chains of every finite length below [(1,0)],
      so iterated [▷] retains content at every depth.

    The two facts together refute, for [lex_FS], the exhaustion
    property that holds for [nat_FS] ([nat_exhausts] vs.
    [lex_not_exhausts]) — a machine-checked, purely propositional
    witness that the choice of forcing structure is observable inside
    the logic, and that the abstract framework of Phase 4 crosses the
    ω boundary with no change whatsoever (both instances use the same
    [iLob], the same connectives, the same definitions). *)

From Coq Require Import Arith Lia Wellfounded Wf_nat.
From ForcingHoare Require Import Phase4_Abstract.

(** ** The lexicographic order on [nat * nat] (order type ω²) *)

Definition lex_le (p q : nat * nat) : Prop :=
  fst p < fst q \/ (fst p = fst q /\ snd p <= snd q).

Definition lex_lt (p q : nat * nat) : Prop :=
  fst p < fst q \/ (fst p = fst q /\ snd p < snd q).

Lemma lex_le_refl p : lex_le p p.
Proof. unfold lex_le; lia. Qed.

Lemma lex_le_trans p q r : lex_le p q -> lex_le q r -> lex_le p r.
Proof. unfold lex_le; lia. Qed.

Lemma lex_lt_le p q : lex_lt p q -> lex_le p q.
Proof. unfold lex_lt, lex_le; lia. Qed.

Lemma lex_lt_le_lt p q r : lex_lt p q -> lex_le q r -> lex_lt p r.
Proof. unfold lex_lt, lex_le; lia. Qed.

(** Well-foundedness, by a nested strong induction: first on the
    first component, then on the second.  (The lexicographic order
    has order type ω², so no single [nat]-valued measure can witness
    this — contrast [lt_pair_wf] in Phase 4, which is justified by
    the measure [fst + snd].) *)

Lemma lex_acc : forall a b, Acc lex_lt (a, b).
Proof.
  induction a using (well_founded_induction lt_wf).
  rename H into IHa.
  intro b.
  induction b using (well_founded_induction lt_wf).
  rename H into IHb.
  constructor.
  intros [c d] Hcd.
  destruct Hcd as [Hlt | [Heq Hlt]]; simpl in *.
  - apply IHa; exact Hlt.
  - subst c. apply IHb; exact Hlt.
Qed.

Lemma lex_lt_wf : well_founded lex_lt.
Proof. intros [a b]; apply lex_acc. Qed.

Definition lex_FS : ForcingStructure :=
  {| fs_cond := nat * nat;
     fs_le := lex_le;
     fs_lt := lex_lt;
     fs_le_refl := lex_le_refl;
     fs_le_trans := lex_le_trans;
     fs_lt_le := lex_lt_le;
     fs_lt_le_lt := lex_lt_le_lt;
     fs_lt_wf := lex_lt_wf
  |}.

(** The abstract Löb rule instantiates here as everywhere. *)
Check iLob lex_FS.

(** ** Iterated later *)

Fixpoint iLaterN (FS : ForcingStructure) (k : nat) (f : iProp FS) : iProp FS :=
  match k with
  | 0 => f
  | S k' => iLater FS (iLaterN FS k' f)
  end.

(** ** Over ω, iterated [▷] exhausts

    [▷^(n+1) ⊥] is forced at [n]: every strict descending chain from
    [n] has length at most [n], so an iteration depth exceeding the
    index is forced vacuously.  Note the formula is [⊥] — the
    strongest possible — so a fortiori [▷^(n+1) φ] is forced at [n]
    for *every* φ: beyond the index, [▷]-iteration says nothing. *)

Lemma nat_laterN_bot :
  forall n, ihold nat_FS (iLaterN nat_FS (S n) (iFalse nat_FS)) n.
Proof.
  induction n.
  - (* at 0: no strict predecessors, so ▷ ⊥ holds vacuously *)
    simpl. intros q Hq. exfalso. simpl in Hq. lia.
  - (* at S n: every q < S n satisfies q <= n, so downward closure
       applies to the induction hypothesis *)
    simpl. intros q Hq.
    apply (imono nat_FS (iLaterN nat_FS (S n) (iFalse nat_FS)) n q).
    + simpl. lia.
    + exact IHn.
Qed.

(** Every ω-condition trivializes some finite iterate of [▷ ⊥]. *)
Theorem nat_exhausts :
  forall n, exists k, ihold nat_FS (iLaterN nat_FS k (iFalse nat_FS)) n.
Proof. intro n. exists (S n). apply nat_laterN_bot. Qed.

(** ** Over ω², iterated [▷] retains content

    Column 0 calibrates the depth: [▷^k ⊥] fails at [(0, k)], because
    [(0,0) ≺ (0,1) ≺ ⋯ ≺ (0,k)] is a strict descending chain of
    length exactly [k]. *)

Lemma lex_laterN_bot_fails_col0 :
  forall k, ~ ihold lex_FS (iLaterN lex_FS k (iFalse lex_FS)) (0, k).
Proof.
  induction k.
  - (* ▷^0 ⊥ = ⊥ *)
    simpl. intro H. exact H.
  - intro H. apply IHk.
    (* (0,k) is a strict predecessor of (0, S k) *)
    apply (H (0, k)).
    right. simpl. lia.
Qed.

(** The limit point [(1,0)] sits above the whole fan
    [(0,k) ≺ (1,0)], so *no* finite iterate [▷^k ⊥] is forced there:
    iterated [▷] never runs out. *)

Theorem lex_laterN_bot_never :
  forall k, ~ ihold lex_FS (iLaterN lex_FS k (iFalse lex_FS)) (1, 0).
Proof.
  intro k. destruct k.
  - simpl. intro H. exact H.
  - intro H. apply (lex_laterN_bot_fails_col0 k).
    apply (H (0, k)).
    left. simpl. lia.
Qed.

(** ** The separating sentence

    "Every condition forces some finite iterate of [▷ ⊥]" — true at
    ω, refuted at ω².  A propositional, machine-checked observable
    that distinguishes forcing structures *inside* the logic, while
    the entire framework (connectives, [▷], Löb) is shared.  This is
    the propositional core of why ω-step-indexing cannot express
    unbounded (liveness-style) content, and why transfinite
    step-indexing recovers it. *)

Definition laterN_exhausts (FS : ForcingStructure) : Prop :=
  forall p, exists k, ihold FS (iLaterN FS k (iFalse FS)) p.

Theorem nat_FS_exhausts : laterN_exhausts nat_FS.
Proof. exact nat_exhausts. Qed.

Theorem lex_FS_not_exhausts : ~ laterN_exhausts lex_FS.
Proof.
  intro H. destruct (H (1, 0)) as [k Hk].
  exact (lex_laterN_bot_never k Hk).
Qed.
