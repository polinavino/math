/-
# Choice-free versions of finite results

No `Mathlib` import: core Lean only, `ℕ`-valued weights, explicit sums. `#print axioms` reports
at most `propext` and `Quot.sound` for every theorem here.

* `Sierpinski`: the Sierpiński space as an explicit two-point space (no bivalence of `Prop`):
  `¬halts = ⊥`, the frontier of the halting point is the other point, and slack is its mass.
* `slack_eq_boundary_fin`: on a finite space given by a list of open sets, the mass of `U`, of
  its exterior and of its boundary add up to the total mass (slack is boundary mass).
* `kraft`: the Kraft inequality for finite prefix-free sets of binary words, the inequality
  bounding the partial sums of Chaitin's `Ω`.
-/

namespace ConstructiveProb.Constr

/-! ### Finite sums over `Fin n` -/

def fs : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, by omega⟩ + fs n (fun i => f ⟨i.val + 1, by omega⟩)

theorem fs_add : ∀ (n : Nat) (f g : Fin n → Nat), fs n (fun i => f i + g i) = fs n f + fs n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    simp only [fs]
    rw [fs_add n]
    omega

theorem fs_congr : ∀ (n : Nat) (f g : Fin n → Nat), (∀ i, f i = g i) → fs n f = fs n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    simp only [fs]
    rw [h, fs_congr n _ _ (fun i => h _)]

/-- Indicator weight. -/
def wt (b : Bool) (m : Nat) : Nat := if b then m else 0

/-! ### The Sierpiński space, explicitly -/

namespace Sierpinski

/-- The opens of the Sierpiński space on the points `{halts, silent}`. -/
inductive Op | bot | halts | top
  deriving DecidableEq

open Op

/-- Points: `true` = the computation halts, `false` = it is silent. -/
def mem : Op → Bool → Bool
  | bot, _ => false
  | halts, b => b
  | top, _ => true

def le (o o' : Op) : Bool := mem o true ≤ mem o' true && mem o false ≤ mem o' false

def inf : Op → Op → Op
  | bot, _ => bot
  | _, bot => bot
  | halts, _ => halts
  | top, o => o

/-- The Heyting complement. -/
def neg : Op → Op
  | bot => top
  | halts => bot
  | top => bot

/-- `neg o` is the largest open disjoint from `o`. -/
theorem neg_spec : ∀ o o' : Op, (inf o' o = bot) ↔ le o' (neg o) = true := by
  intro o o'; cases o <;> cases o' <;> decide

/-- **The Σ₁ asymmetry**: `¬halts = ⊥`. -/
theorem neg_halts : neg halts = bot := rfl

/-- The valuation of a two-point measure with weights `wT` (halts) and `wF` (silent). -/
def val (wT wF : Nat) (o : Op) : Nat := wt (mem o true) wT + wt (mem o false) wF

/-- `x` is in the closure of the halting point: every open containing `x` contains `true`. -/
def inClosure (x : Bool) : Bool := [bot, halts, top].all fun o => !mem o x || mem o true

/-- The frontier of the halting point: closure minus interior. -/
def frontier (x : Bool) : Bool := inClosure x && !mem halts x

theorem frontier_iff : ∀ x : Bool, frontier x = true ↔ x = false := by decide

/-- **Slack is the mass of the silent point.** -/
theorem slack_eq (wT wF : Nat) :
    val wT wF top = val wT wF halts + val wT wF (neg halts) + wt (frontier false) wF := by
  simp [val, mem, neg, wt, frontier, inClosure]

end Sierpinski

/-! ### Slack is boundary mass on finite spaces -/

section Boundary

variable {n : Nat}

/-- `∀ i : Fin n, p i` as a Boolean. -/
def allFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p ⟨0, by omega⟩ && allFin n (fun i => p ⟨i.val + 1, by omega⟩)

theorem allFin_spec : ∀ (n : Nat) (p : Fin n → Bool), allFin n p = true ↔ ∀ i, p i = true
  | 0, _ => ⟨fun _ i => absurd i.isLt (Nat.not_lt_zero _), fun _ => rfl⟩
  | n + 1, p => by
    simp only [allFin, Bool.and_eq_true, allFin_spec n]
    constructor
    · rintro ⟨h0, h⟩ ⟨i, hi⟩
      cases i with
      | zero => exact h0
      | succ k => exact h ⟨k, by omega⟩
    · intro h; exact ⟨h _, fun i => h _⟩

/-- `x` lies in the exterior of `U`: some open from `ops` contains `x` and misses `U`. -/
def ext (ops : List (Fin n → Bool)) (U : Fin n → Bool) (x : Fin n) : Bool :=
  ops.any fun O => O x && allFin n (fun y => !(O y && U y))

/-- The boundary of `U`: neither in `U` nor in its exterior. -/
def bd (ops : List (Fin n → Bool)) (U : Fin n → Bool) (x : Fin n) : Bool :=
  !U x && !ext ops U x

theorem not_ext_of_mem {ops : List (Fin n → Bool)} {U : Fin n → Bool} {x : Fin n}
    (hx : U x = true) : ext ops U x = false := by
  unfold ext
  rw [List.any_eq_false]
  intro O _ h
  rw [Bool.and_eq_true, allFin_spec] at h
  have := h.2 x
  rw [h.1, hx] at this
  exact absurd this (by decide)

/-- Every open from `ops` that misses `U` lies in the exterior. -/
theorem sub_ext {ops : List (Fin n → Bool)} {U : Fin n → Bool} {O : Fin n → Bool}
    (hO : O ∈ ops) (hd : ∀ y, (!(O y && U y)) = true) {x : Fin n} (hx : O x = true) :
    ext ops U x = true := by
  unfold ext
  rw [List.any_eq_true]
  exact ⟨O, hO, by rw [Bool.and_eq_true, allFin_spec]; exact ⟨hx, hd⟩⟩

/-- **Slack is boundary mass.** The masses of `U`, its exterior and its boundary sum to the
total mass. With the exterior as the Heyting complement of `U` among the opens, this is
`1 = v U + v ¬U + μ(∂U)`. -/
theorem slack_eq_boundary_fin (ops : List (Fin n → Bool)) (U : Fin n → Bool) (μ : Fin n → Nat) :
    fs n μ = fs n (fun x => wt (U x) (μ x)) + fs n (fun x => wt (ext ops U x) (μ x)) +
      fs n (fun x => wt (bd ops U x) (μ x)) := by
  rw [← fs_add, ← fs_add]
  apply fs_congr
  intro x
  unfold bd
  cases hU : U x
  · cases hE : ext ops U x <;> simp [wt]
  · rw [not_ext_of_mem hU]; simp [wt]

end Boundary

/-! ### The Kraft inequality -/

section Kraft

/-- `u` is a prefix of `v`. -/
def isPre : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: u, b :: v => a == b && isPre u v

/-- Neither word is a prefix of the other. -/
def Incomp (u v : List Bool) : Prop := isPre u v = false ∧ isPre v u = false

/-- `∑_{w ∈ S} 2^(L - |w|)`, i.e. `2^L ∑ 2^(-|w|)`. -/
def ksum (L : Nat) : List (List Bool) → Nat
  | [] => 0
  | w :: S => 2 ^ (L - w.length) + ksum L S

/-- Pairwise incomparable lists. -/
def PF : List (List Bool) → Prop
  | [] => True
  | w :: S => (∀ v ∈ S, Incomp w v) ∧ PF S

def tails (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | [] :: S => tails b S
  | (a :: t) :: S => if a = b then t :: tails b S else tails b S

theorem nil_singleton : ∀ S : List (List Bool), PF S → [] ∈ S → S.length ≤ 1
  | [], _, _ => by simp
  | w :: S, ⟨hw, hS⟩, hm => by
    cases S with
    | nil => simp
    | cons v S' =>
      exfalso
      rcases List.mem_cons.1 hm with h | h
      · subst h
        have := (hw v (List.mem_cons_self ..)).1
        simp [isPre] at this
      · have := (hw [] h).2
        simp [isPre] at this

theorem ksum_le_len (L : Nat) : ∀ S : List (List Bool), ksum L S ≤ S.length * 2 ^ L
  | [] => by simp [ksum]
  | w :: S => by
    simp only [ksum, List.length_cons]
    have h1 : 2 ^ (L - w.length) ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 := ksum_le_len L S
    rw [Nat.succ_mul]; omega

theorem ksum_split (k : Nat) : ∀ S : List (List Bool), [] ∉ S →
    ksum (k + 1) S = ksum k (tails false S) + ksum k (tails true S)
  | [], _ => rfl
  | [] :: _, h => absurd (List.mem_cons_self ..) h
  | (a :: t) :: S, h => by
    have h' : [] ∉ S := fun hm => h (List.mem_cons_of_mem _ hm)
    have ih := ksum_split k S h'
    have hp : k + 1 - (a :: t).length = k - t.length := by
      simp only [List.length_cons]; omega
    cases a <;> (simp [ksum, tails, hp, ih]; try omega)

theorem mem_tails {b : Bool} {t : List Bool} : ∀ {S : List (List Bool)},
    t ∈ tails b S → (b :: t) ∈ S
  | [], h => by simp [tails] at h
  | [] :: S, h => List.mem_cons_of_mem _ (mem_tails (S := S) h)
  | (a :: u) :: S, h => by
    unfold tails at h
    by_cases ha : a = b
    · rw [if_pos ha] at h
      rcases List.mem_cons.1 h with h | h
      · subst h; subst ha; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_tails h)
    · rw [if_neg ha] at h
      exact List.mem_cons_of_mem _ (mem_tails h)

theorem PF_tails (b : Bool) : ∀ S : List (List Bool), PF S → PF (tails b S)
  | [], _ => trivial
  | [] :: S, ⟨_, hS⟩ => PF_tails b S hS
  | (a :: u) :: S, ⟨hw, hS⟩ => by
    unfold tails
    by_cases ha : a = b
    · rw [if_pos ha]
      refine ⟨fun v hv => ?_, PF_tails b S hS⟩
      have := hw (b :: v) (mem_tails hv)
      subst ha
      simpa [Incomp, isPre] using this
    · rw [if_neg ha]; exact PF_tails b S hS

theorem len_tails {b : Bool} {L : Nat} : ∀ {S : List (List Bool)},
    (∀ w ∈ S, w.length ≤ L + 1) → ∀ t ∈ tails b S, t.length ≤ L := by
  intro S hS t ht
  have := hS _ (mem_tails ht)
  simp [List.length_cons] at this
  omega

/-- **Kraft's inequality**: for a finite prefix-free set `S` of binary words of length at most
`L`, `∑_{w ∈ S} 2^(L - |w|) ≤ 2^L`. -/
theorem kraft : ∀ (L : Nat) (S : List (List Bool)), PF S → (∀ w ∈ S, w.length ≤ L) →
    ksum L S ≤ 2 ^ L := by
  intro L
  induction L with
  | zero =>
    intro S hS hl
    by_cases hm : [] ∈ S
    · have := nil_singleton S hS hm
      have := ksum_le_len 0 S
      simp at this ⊢; omega
    · cases S with
      | nil => simp [ksum]
      | cons w S =>
        have := hl w (List.mem_cons_self ..)
        cases w with
        | nil => exact absurd (List.mem_cons_self ..) hm
        | cons a t => simp [List.length_cons] at this
  | succ k ih =>
    intro S hS hl
    by_cases hm : [] ∈ S
    · have := nil_singleton S hS hm
      have := ksum_le_len (k + 1) S
      calc ksum (k + 1) S ≤ S.length * 2 ^ (k + 1) := this
        _ ≤ 1 * 2 ^ (k + 1) := Nat.mul_le_mul_right _ ‹_›
        _ = 2 ^ (k + 1) := Nat.one_mul _
    · rw [ksum_split k S hm]
      have h0 := ih _ (PF_tails false S hS) (len_tails hl)
      have h1 := ih _ (PF_tails true S hS) (len_tails hl)
      rw [Nat.pow_succ]; omega

end Kraft

end ConstructiveProb.Constr
