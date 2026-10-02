/-
# Fourier–Motzkin elimination over ℤ, without choice

Homogeneous integer systems of rows `c · w ≥ 0`, some strict (`c · w > 0`). `fm` proves, by
eliminating variables one at a time, that such a system either has an integer solution or derives
the contradictory row `0 > 0` by nonnegative integer combinations (`Der`). Back-substitution uses
an explicit integer midpoint, so no rationals are needed. The only tactic beyond core Lean is
`ring`, whose proofs over `ℤ` do not use `Classical.choice`.

`Farkas.complete` applies this to convex hulls: a rational point `y / d` is a convex combination
of finitely many integer points `S j` iff every integer affine law valid on all `S j` holds at
`y / d`. `#print axioms` reports at most `propext` and `Quot.sound`.
-/
import Mathlib.Tactic.Ring

namespace ConstructiveProb.Farkas

/-! ### Dot products -/

def dot : (n : Nat) → (Fin n → Int) → (Fin n → Int) → Int
  | 0, _, _ => 0
  | n + 1, c, w => dot n (fun i => c i.castSucc) (fun i => w i.castSucc) +
      c (Fin.last n) * w (Fin.last n)

theorem dot_add_left : ∀ (n : Nat) (c c' w : Fin n → Int),
    dot n (fun i => c i + c' i) w = dot n c w + dot n c' w
  | 0, _, _, _ => rfl
  | n + 1, c, c', w => by
    simp only [dot]; rw [dot_add_left n]; ring

theorem dot_smul_left : ∀ (n : Nat) (k : Int) (c w : Fin n → Int),
    dot n (fun i => k * c i) w = k * dot n c w
  | 0, k, _, _ => by simp only [dot]; ring
  | n + 1, k, c, w => by
    simp only [dot]; rw [dot_smul_left n]; ring

theorem dot_smul_right : ∀ (n : Nat) (k : Int) (c w : Fin n → Int),
    dot n c (fun i => k * w i) = k * dot n c w
  | 0, k, _, _ => by simp only [dot]; ring
  | n + 1, k, c, w => by
    simp only [dot]; rw [dot_smul_right n]; ring

theorem dot_add_right : ∀ (n : Nat) (c w w' : Fin n → Int),
    dot n c (fun i => w i + w' i) = dot n c w + dot n c w'
  | 0, _, _, _ => rfl
  | n + 1, c, w, w' => by
    simp only [dot]; rw [dot_add_right n]; ring

theorem dot_zero_left : ∀ (n : Nat) (w : Fin n → Int), dot n (fun _ => 0) w = 0
  | 0, _ => rfl
  | n + 1, w => by simp only [dot]; rw [dot_zero_left n]; ring

theorem dot_congr : ∀ (n : Nat) (c c' w : Fin n → Int), (∀ i, c i = c' i) → dot n c w = dot n c' w
  | 0, _, _, _, _ => rfl
  | n + 1, c, c', w, h => by
    simp only [dot]; rw [dot_congr n _ (fun i => c' i.castSucc) _ (fun i => h _), h]

theorem dot_comm : ∀ (n : Nat) (c w : Fin n → Int), dot n c w = dot n w c
  | 0, _, _ => rfl
  | n + 1, c, w => by simp only [dot]; rw [dot_comm n]; ring

theorem dot_single : ∀ (n : Nat) (e : Fin n) (w : Fin n → Int),
    dot n (fun i => if i = e then 1 else 0) w = w e
  | 0, e, _ => Fin.elim0 e
  | n + 1, e, w => by
    simp only [dot]
    by_cases he : e.val < n
    · have hl : Fin.last n ≠ e := fun h => by rw [← h] at he; simp [Fin.last] at he
      rw [if_neg hl]
      rw [dot_congr n (fun i => if i.castSucc = e then 1 else 0)
        (fun i => if i = ⟨e.val, he⟩ then 1 else 0) _ (fun i => by
          by_cases h : i = ⟨e.val, he⟩
          · rw [if_pos h, if_pos (by subst h; exact Fin.ext rfl)]
          · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by
              have := congrArg Fin.val h'; simpa using this)))])]
      rw [dot_single n ⟨e.val, he⟩ (fun i => w i.castSucc)]
      have : (⟨e.val, he⟩ : Fin n).castSucc = e := Fin.ext rfl
      rw [this]; ring
    · have he' : e = Fin.last n := Fin.ext (by have := e.isLt; simp [Fin.last]; omega)
      subst he'
      rw [if_pos rfl, dot_congr n _ (fun _ => 0) _ (fun i => if_neg (fun h => by
        have := congrArg Fin.val h; simp [Fin.last] at this; omega)), dot_zero_left]
      ring

/-! ### Rows and derivations -/

structure Row (n : Nat) where
  c : Fin n → Int
  s : Bool

def Sat {n : Nat} (r : Row n) (w : Fin n → Int) : Prop :=
  0 ≤ dot n r.c w ∧ (r.s = true → 0 < dot n r.c w)

def comb {n : Nat} (p q : Int) (r₁ r₂ : Row n) : Row n :=
  ⟨fun i => p * r₁.c i + q * r₂.c i, (decide (0 < p) && r₁.s) || (decide (0 < q) && r₂.s)⟩

/-- The contradictory row `0 > 0`. -/
def zeroS (n : Nat) : Row n := ⟨fun _ => 0, true⟩

/-- Rows derivable from `rows` by nonnegative integer combinations. -/
inductive Der {n : Nat} (rows : List (Row n)) : Row n → Prop
  | base {r : Row n} : r ∈ rows → Der rows r
  | comb {r₁ r₂ : Row n} (p q : Int) : 0 ≤ p → 0 ≤ q → Der rows r₁ → Der rows r₂ →
      Der rows (comb p q r₁ r₂)

/-! ### One elimination step -/

section Step

variable {n : Nat}

def lastc (r : Row (n + 1)) : Int := r.c (Fin.last n)

def proj (r : Row (n + 1)) : Row n := ⟨fun i => r.c i.castSucc, r.s⟩

def lift (r : Row n) : Row (n + 1) := ⟨fun i => if h : i.val < n then r.c ⟨i.val, h⟩ else 0, r.s⟩

def posR (rows : List (Row (n + 1))) := rows.filter fun r => decide (0 < lastc r)
def negR (rows : List (Row (n + 1))) := rows.filter fun r => decide (lastc r < 0)
def zerR (rows : List (Row (n + 1))) := rows.filter fun r => decide (lastc r = 0)

def pair (p q : Row (n + 1)) : Row n := proj (comb (-lastc q) (lastc p) p q)

def step (rows : List (Row (n + 1))) : List (Row n) :=
  (zerR rows).map proj ++ (posR rows).flatMap fun p => (negR rows).map fun q => pair p q

theorem lift_proj (r : Row (n + 1)) (h : lastc r = 0) : lift (proj r) = r := by
  cases r with
  | mk c s =>
    simp only [lift, proj, Row.mk.injEq, and_true]
    funext i
    by_cases hi : i.val < n
    · rw [dif_pos hi]; exact congrArg c (Fin.ext rfl)
    · rw [dif_neg hi]
      have : i = Fin.last n := Fin.ext (by have := i.isLt; simp [Fin.last]; omega)
      rw [this]; exact h.symm

theorem lastc_comb (p q : Row (n + 1)) : lastc (comb (-lastc q) (lastc p) p q) = 0 := by
  simp only [lastc, comb]; ring

theorem lift_comb (p q : Int) (r₁ r₂ : Row n) : lift (comb p q r₁ r₂) = comb p q (lift r₁) (lift r₂) := by
  simp only [lift, comb, Row.mk.injEq, and_true]
  funext i
  by_cases hi : i.val < n
  · rw [dif_pos hi, dif_pos hi, dif_pos hi]
  · rw [dif_neg hi, dif_neg hi, dif_neg hi]; ring

theorem lift_zeroS : lift (zeroS n) = zeroS (n + 1) := by
  simp only [lift, zeroS, Row.mk.injEq, and_true]
  funext i
  by_cases hi : i.val < n
  · rw [dif_pos hi]
  · rw [dif_neg hi]

/-- Derivations after elimination lift to derivations before it. -/
theorem der_lift (rows : List (Row (n + 1))) {r : Row n} (h : Der (step rows) r) :
    Der rows (lift r) := by
  induction h with
  | base hr =>
    rcases List.mem_append.1 hr with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
      have h1 := List.mem_filter.1 ha
      rw [lift_proj a (of_decide_eq_true h1.2)]
      exact Der.base h1.1
    · obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.1 h
      obtain ⟨q, hq, hpq⟩ := List.mem_map.1 hmem
      subst hpq
      have hp' := List.mem_filter.1 hp
      have hq' := List.mem_filter.1 hq
      unfold pair
      rw [lift_proj _ (lastc_comb p q)]
      exact Der.comb _ _ (by have := of_decide_eq_true hq'.2; omega)
        (by have := of_decide_eq_true hp'.2; omega) (Der.base hp'.1) (Der.base hq'.1)
  | comb p q hp hq _ _ ih₁ ih₂ =>
    rw [lift_comb]; exact Der.comb p q hp hq ih₁ ih₂

/-- The extension of a solution by a scaling `D` and a last coordinate `W`. -/
def extd (D W : Int) (w' : Fin n → Int) : Fin (n + 1) → Int :=
  fun i => if h : i.val < n then D * w' ⟨i.val, h⟩ else W

theorem dot_extd (r : Row (n + 1)) (D W : Int) (w' : Fin n → Int) :
    dot (n + 1) r.c (extd D W w') = D * dot n (proj r).c w' + lastc r * W := by
  simp only [dot, proj, lastc]
  have h1 : (fun i : Fin n => extd D W w' i.castSucc) = fun i => D * w' i := by
    funext i; simp only [extd]; rw [dif_pos (by simp)]
    exact congrArg (fun k => D * w' k) (Fin.ext rfl)
  have h2 : extd D W w' (Fin.last n) = W := by simp [extd, Fin.last]
  rw [h1, h2, dot_smul_right]

theorem dot_pair (p q : Row (n + 1)) (w' : Fin n → Int) :
    dot n (pair p q).c w' = -lastc q * dot n (proj p).c w' + lastc p * dot n (proj q).c w' := by
  simp only [pair, proj, comb]
  rw [dot_add_left, dot_smul_left, dot_smul_left]

theorem pair_s (p q : Row (n + 1)) (hp : 0 < lastc p) (hq : lastc q < 0) :
    (pair p q).s = (p.s || q.s) := by
  simp only [pair, proj, comb]
  rw [decide_eq_true (by omega : 0 < -lastc q), decide_eq_true hp]
  simp

/-- A maximum for a total, transitive relation on a nonempty list. -/
theorem exists_max {α : Type} (le : α → α → Prop) [DecidableRel le] :
    ∀ (l : List α), l ≠ [] → (∀ a ∈ l, ∀ b ∈ l, le a b ∨ le b a) →
    (∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, le a b → le b c → le a c) → ∃ m ∈ l, ∀ x ∈ l, le x m
  | [], h, _, _ => absurd rfl h
  | [a], _, ht, _ => ⟨a, List.mem_singleton_self a, fun x hx => by
      rw [List.mem_singleton.1 hx]
      rcases ht a (List.mem_singleton_self a) a (List.mem_singleton_self a) with h | h <;> exact h⟩
  | a :: b :: l, _, ht, htr => by
    have hsub : ∀ x ∈ b :: l, x ∈ a :: b :: l := fun x hx => List.mem_cons_of_mem _ hx
    obtain ⟨m, hm, hmax⟩ := exists_max le (b :: l) (List.cons_ne_nil _ _)
      (fun x hx y hy => ht x (hsub x hx) y (hsub y hy))
      (fun x hx y hy z hz => htr x (hsub x hx) y (hsub y hy) z (hsub z hz))
    by_cases hma : le m a
    · refine ⟨a, List.mem_cons_self .., fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · rcases ht x (List.mem_cons_self ..) x (List.mem_cons_self ..) with h | h <;> exact h
      · exact htr x (hsub x hx) m (hsub m hm) a (List.mem_cons_self ..) (hmax x hx) hma
    · have ham : le a m := (ht a (List.mem_cons_self ..) m (hsub m hm)).resolve_right hma
      refine ⟨m, hsub m hm, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ham
      · exact hmax x hx

/-- Transitivity of comparing fractions `x / β` with positive denominators. -/
theorem frac_trans {xa xb xc ba bb bc : Int} (hb : 0 < bb) (ha : 0 < ba) (hc : 0 < bc)
    (h1 : xa * bb ≤ xb * ba) (h2 : xb * bc ≤ xc * bb) : xa * bc ≤ xc * ba := by
  have e1 := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hc)
  have e2 := Int.mul_le_mul_of_nonneg_right h2 (Int.le_of_lt ha)
  have r1 : xa * bb * bc = (xa * bc) * bb := by ring
  have r2 : xb * ba * bc = xb * bc * ba := by ring
  have r3 : xc * bb * ba = (xc * ba) * bb := by ring
  rw [r1, r2] at e1
  rw [r3] at e2
  exact Int.le_of_mul_le_mul_right (Int.le_trans e1 e2) hb

/-- **Back-substitution.** A solution after elimination extends to a solution before it. -/
theorem feas_lift (rows : List (Row (n + 1))) (w' : Fin n → Int)
    (hw : ∀ r ∈ step rows, Sat r w') : ∃ w, ∀ r ∈ rows, Sat r w := by
  let L : Row (n + 1) → Int := fun r => dot n (proj r).c w'
  have hzer : ∀ r ∈ rows, lastc r = 0 → Sat (proj r) w' := fun r hr h =>
    hw _ (List.mem_append_left _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, decide_eq_true h⟩, rfl⟩))
  have hpair : ∀ p ∈ rows, ∀ q ∈ rows, 0 < lastc p → lastc q < 0 →
      0 ≤ -lastc q * L p + lastc p * L q ∧
      ((p.s || q.s) = true → 0 < -lastc q * L p + lastc p * L q) := by
    intro p hp q hq hpp hqn
    have := hw (pair p q) (List.mem_append_right _ (List.mem_flatMap.2 ⟨p,
      List.mem_filter.2 ⟨hp, decide_eq_true hpp⟩, List.mem_map.2 ⟨q,
        List.mem_filter.2 ⟨hq, decide_eq_true hqn⟩, rfl⟩⟩))
    rw [Sat, dot_pair, pair_s p q hpp hqn] at this
    exact this
  -- a row with zero last coefficient is satisfied by every extension with `D > 0`
  have zcase : ∀ D W, 0 < D → ∀ r ∈ rows, lastc r = 0 → Sat r (extd D W w') := by
    intro D W hD r hr h0
    obtain ⟨h1, h2⟩ := hzer r hr h0
    refine ⟨?_, fun hs => ?_⟩
    · rw [dot_extd, h0]; have := Int.mul_nonneg (Int.le_of_lt hD) h1; omega
    · rw [dot_extd, h0]; have := Int.mul_pos hD (h2 hs); omega
  -- the lower-bound and upper-bound orders
  let lo : Row (n + 1) → Row (n + 1) → Prop := fun p p' => L p' * lastc p ≤ L p * lastc p'
  let up : Row (n + 1) → Row (n + 1) → Prop := fun q q' => L q' * (-lastc q) ≤ L q * (-lastc q')
  have lo_tot : ∀ a ∈ posR rows, ∀ b ∈ posR rows, lo a b ∨ lo b a := fun a _ b _ =>
    Int.le_total _ _
  have up_tot : ∀ a ∈ negR rows, ∀ b ∈ negR rows, up a b ∨ up b a := fun a _ b _ =>
    Int.le_total _ _
  have pos_of : ∀ p ∈ posR rows, p ∈ rows ∧ 0 < lastc p := fun p hp =>
    ⟨(List.mem_filter.1 hp).1, of_decide_eq_true (List.mem_filter.1 hp).2⟩
  have neg_of : ∀ q ∈ negR rows, q ∈ rows ∧ lastc q < 0 := fun q hq =>
    ⟨(List.mem_filter.1 hq).1, of_decide_eq_true (List.mem_filter.1 hq).2⟩
  have lo_tr : ∀ a ∈ posR rows, ∀ b ∈ posR rows, ∀ c ∈ posR rows, lo a b → lo b c → lo a c := by
    intro a ha b hb c hc h1 h2
    have r := frac_trans (xa := -L a) (xb := -L b) (xc := -L c) (pos_of b hb).2 (pos_of a ha).2
      (pos_of c hc).2 (by simp only [lo] at h1; have : -L a * lastc b = -(L a * lastc b) := by ring
                          have : -L b * lastc a = -(L b * lastc a) := by ring
                          omega)
      (by simp only [lo] at h2; have : -L b * lastc c = -(L b * lastc c) := by ring
          have : -L c * lastc b = -(L c * lastc b) := by ring
          omega)
    simp only [lo]
    have : -L a * lastc c = -(L a * lastc c) := by ring
    have : -L c * lastc a = -(L c * lastc a) := by ring
    omega
  have up_tr : ∀ a ∈ negR rows, ∀ b ∈ negR rows, ∀ c ∈ negR rows, up a b → up b c → up a c := by
    intro a ha b hb c hc h1 h2
    have r := frac_trans (xa := L c) (xb := L b) (xc := L a) (ba := -lastc c) (bb := -lastc b)
      (bc := -lastc a) (by have := (neg_of b hb).2; omega) (by have := (neg_of c hc).2; omega)
      (by have := (neg_of a ha).2; omega) h2 h1
    exact r
  have decLo : DecidableRel lo := fun a b => Int.decLe _ _
  have decUp : DecidableRel up := fun a b => Int.decLe _ _
  cases hP : posR rows with
  | nil =>
    cases hN : negR rows with
    | nil =>
      refine ⟨extd 1 0 w', fun r hr => zcase 1 0 (by decide) r hr ?_⟩
      rcases Int.lt_trichotomy (lastc r) 0 with h | h | h
      · have : r ∈ negR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        rw [hN] at this; simp at this
      · exact h
      · have : r ∈ posR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        rw [hP] at this; simp at this
    | cons q₀ ql =>
      obtain ⟨qs, hqs, hqmin⟩ := exists_max up (negR rows) (by rw [hN]; simp) up_tot up_tr
      obtain ⟨hqsr, hqsn⟩ := neg_of qs hqs
      refine ⟨extd (-lastc qs) (L qs + lastc qs) w', fun r hr => ?_⟩
      rcases Int.lt_trichotomy (lastc r) 0 with h | h | h
      · have hrq : r ∈ negR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        have hF := hqmin r hrq
        simp only [up] at hF
        have hpos : 0 < lastc r * lastc qs := Int.mul_pos_of_neg_of_neg h hqsn
        have key : dot (n + 1) r.c (extd (-lastc qs) (L qs + lastc qs) w') =
            (L r * (-lastc qs) - L qs * (-lastc r)) + lastc r * lastc qs := by
          rw [dot_extd]; ring
        refine ⟨?_, fun _ => ?_⟩ <;> rw [key] <;> omega
      · exact zcase _ _ (by omega) r hr h
      · have : r ∈ posR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        rw [hP] at this; simp at this
  | cons p₀ pl =>
    obtain ⟨ps, hps, hpmax⟩ := exists_max lo (posR rows) (by rw [hP]; simp) lo_tot lo_tr
    obtain ⟨hpsr, hpsp⟩ := pos_of ps hps
    cases hN : negR rows with
    | nil =>
      refine ⟨extd (lastc ps) (lastc ps - L ps) w', fun r hr => ?_⟩
      rcases Int.lt_trichotomy (lastc r) 0 with h | h | h
      · have : r ∈ negR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        rw [hN] at this; simp at this
      · exact zcase _ _ hpsp r hr h
      · have hrp : r ∈ posR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        have hE := hpmax r hrp
        simp only [lo] at hE
        have hpos : 0 < lastc r * lastc ps := Int.mul_pos h hpsp
        have key : dot (n + 1) r.c (extd (lastc ps) (lastc ps - L ps) w') =
            (L r * lastc ps - L ps * lastc r) + lastc r * lastc ps := by
          rw [dot_extd]; ring
        refine ⟨?_, fun _ => ?_⟩ <;> rw [key] <;> omega
    | cons q₀ ql =>
      obtain ⟨qs, hqs, hqmin⟩ := exists_max up (negR rows) (by rw [hN]; simp) up_tot up_tr
      obtain ⟨hqsr, hqsn⟩ := neg_of qs hqs
      let D := -2 * lastc ps * lastc qs
      let W := L ps * lastc qs + L qs * lastc ps
      have hD : 0 < D := by
        have := Int.mul_pos hpsp (by omega : 0 < -lastc qs)
        show 0 < -2 * lastc ps * lastc qs
        have e : -2 * lastc ps * lastc qs = 2 * (lastc ps * -lastc qs) := by ring
        omega
      refine ⟨extd D W w', fun r hr => ?_⟩
      rcases Int.lt_trichotomy (lastc r) 0 with h | h | h
      · -- an upper-bound row
        have hrq : r ∈ negR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        have hF := hqmin r hrq
        simp only [up] at hF
        obtain ⟨hC, hCs⟩ := hpair ps hpsr r hr hpsp h
        have key : dot (n + 1) r.c (extd D W w') =
            (-lastc qs) * (-lastc r * L ps + lastc ps * L r) +
              lastc ps * (L r * (-lastc qs) - L qs * (-lastc r)) := by
          rw [dot_extd]; simp only [D, W]; ring
        have hq' : 0 < -lastc qs := by omega
        have hF' : 0 ≤ L r * (-lastc qs) - L qs * (-lastc r) := by omega
        refine ⟨?_, fun hs => ?_⟩
        · rw [key]
          have := Int.mul_nonneg (Int.le_of_lt hq') hC
          have := Int.mul_nonneg (Int.le_of_lt hpsp) hF'
          omega
        · rw [key]
          have := Int.mul_pos hq' (hCs (by simp [hs]))
          have := Int.mul_nonneg (Int.le_of_lt hpsp) hF'
          omega
      · exact zcase _ _ hD r hr h
      · -- a lower-bound row
        have hrp : r ∈ posR rows := List.mem_filter.2 ⟨hr, decide_eq_true h⟩
        have hE := hpmax r hrp
        simp only [lo] at hE
        obtain ⟨hC, hCs⟩ := hpair r hr qs hqsr h hqsn
        have key : dot (n + 1) r.c (extd D W w') =
            lastc ps * (-lastc qs * L r + lastc r * L qs) +
              (-lastc qs) * (L r * lastc ps - L ps * lastc r) := by
          rw [dot_extd]; simp only [D, W]; ring
        have hq' : 0 < -lastc qs := by omega
        have hE' : 0 ≤ L r * lastc ps - L ps * lastc r := by omega
        refine ⟨?_, fun hs => ?_⟩
        · rw [key]
          have := Int.mul_nonneg (Int.le_of_lt hpsp) hC
          have := Int.mul_nonneg (Int.le_of_lt hq') hE'
          omega
        · rw [key]
          have := Int.mul_pos hpsp (hCs (by simp [hs]))
          have := Int.mul_nonneg (Int.le_of_lt hq') hE'
          omega

end Step

/-- **Fourier–Motzkin.** A homogeneous system either has an integer solution or derives
`0 > 0`. -/
theorem fm : ∀ (n : Nat) (rows : List (Row n)), (∃ w, ∀ r ∈ rows, Sat r w) ∨ Der rows (zeroS n)
  | 0, rows => by
    cases h : rows.any (fun r => r.s) with
    | true =>
      right
      obtain ⟨r, hr, hs⟩ := List.any_eq_true.1 h
      have : r = zeroS 0 := by
        cases r with
        | mk c s =>
          simp only [zeroS, Row.mk.injEq]
          exact ⟨funext fun i => Fin.elim0 i, hs⟩
      rw [← this]; exact Der.base hr
    | false =>
      left
      refine ⟨fun i => Fin.elim0 i, fun r hr => ⟨by simp [dot], fun hs => ?_⟩⟩
      have := List.any_eq_false.1 h r hr
      rw [hs] at this; exact absurd rfl this
  | n + 1, rows => by
    rcases fm n (step rows) with ⟨w', hw'⟩ | hd
    · exact Or.inl (feas_lift rows w' hw')
    · right; have := der_lift rows hd; rwa [lift_zeroS] at this

theorem dot_swap : ∀ (N m : Nat) (S : Fin N → Fin m → Int) (β : Fin m → Int) (lam : Fin N → Int),
    dot N (fun j => dot m β (S j)) lam = dot m β (fun e => dot N (fun j => S j e) lam)
  | 0, m, _, β, _ => by simp only [dot]; rw [dot_comm, dot_zero_left]
  | N + 1, m, S, β, lam => by
    simp only [dot]
    have h : dot m β (fun e => S (Fin.last N) e * lam (Fin.last N)) =
        dot m β (S (Fin.last N)) * lam (Fin.last N) := by
      rw [dot_comm, dot_congr m _ (fun e => lam (Fin.last N) * S (Fin.last N) e) _
        (fun e => Int.mul_comm _ _), dot_smul_left, dot_comm]; ring
    rw [dot_swap N m (fun j => S j.castSucc) β (fun j => lam j.castSucc), dot_add_right, h]

theorem dot_negsingle {m : Nat} (e : Fin m) (g : Fin m → Int) :
    dot m (fun k => if k = e then -1 else 0) g = -g e := by
  rw [dot_congr m _ (fun k => (-1) * (if k = e then 1 else 0)) _ (fun k => by
    by_cases h : k = e
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl), dot_smul_left, dot_single]; ring

/-! ### Convex hulls -/

section Hull

variable {N m : Nat} (S : Fin N → Fin m → Int) (y : Fin m → Int) (d : Int)

/-- The coefficient vector of a row of the hull system: variables are the weights `λ j`
(`j < N`) and the denominator `t` (the last). -/
def hrow (μ : Fin N → Int) (ν α : Int) (β : Fin m → Int) : Fin (N + 1) → Int :=
  fun i => if h : i.val < N then μ ⟨i.val, h⟩ + α + d * dot m β (S ⟨i.val, h⟩)
    else ν - α - dot m β y

/-- The rows of the system `λ ≥ 0, t > 0, Σ λ = t, d Σ λ_j S_j = t y`. -/
def hullRows : List (Row (N + 1)) :=
  (List.finRange N).map (fun j => ⟨hrow S y d (fun k => if k = j then 1 else 0) 0 0 (fun _ => 0), false⟩) ++
  [⟨hrow S y d (fun _ => 0) 1 0 (fun _ => 0), true⟩,
   ⟨hrow S y d (fun _ => 0) 0 1 (fun _ => 0), false⟩,
   ⟨hrow S y d (fun _ => 0) 0 (-1) (fun _ => 0), false⟩] ++
  (List.finRange m).flatMap (fun e =>
    [⟨hrow S y d (fun _ => 0) 0 0 (fun k => if k = e then 1 else 0), false⟩,
     ⟨hrow S y d (fun _ => 0) 0 0 (fun k => if k = e then -1 else 0), false⟩])

/-- Every derivable row of the hull system has the coefficient form `hrow`. -/
theorem der_form {r : Row (N + 1)} (h : Der (hullRows S y d) r) :
    ∃ μ ν α β, (∀ j, 0 ≤ μ j) ∧ 0 ≤ ν ∧ (r.s = true → 0 < ν) ∧ r.c = hrow S y d μ ν α β := by
  induction h with
  | base hr =>
    have nf : ∀ b : Bool, b = false → b = true → 0 < (0 : Int) := fun b h1 h2 => by
      rw [h1] at h2; exact Bool.noConfusion h2
    unfold hullRows at hr
    rcases List.mem_append.1 hr with hr | hr
    · rcases List.mem_append.1 hr with hr | hr
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hr
        exact ⟨fun k => if k = j then 1 else 0, 0, 0, fun _ => 0,
          fun k => by show (0 : Int) ≤ if k = j then 1 else 0; split <;> decide,
          Int.le_refl _, nf _ rfl, rfl⟩
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨fun _ => 0, 1, 0, fun _ => 0, fun _ => Int.le_refl _, by decide,
            fun _ => by decide, rfl⟩
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨fun _ => 0, 0, 1, fun _ => 0, fun _ => Int.le_refl _, Int.le_refl _, nf _ rfl, rfl⟩
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨fun _ => 0, 0, -1, fun _ => 0, fun _ => Int.le_refl _, Int.le_refl _,
            nf _ rfl, rfl⟩
        · exact absurd hr (List.not_mem_nil)
    · obtain ⟨e, -, hr⟩ := List.mem_flatMap.1 hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨fun _ => 0, 0, 0, fun k => if k = e then 1 else 0, fun _ => Int.le_refl _,
          Int.le_refl _, nf _ rfl, rfl⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨fun _ => 0, 0, 0, fun k => if k = e then -1 else 0, fun _ => Int.le_refl _,
          Int.le_refl _, nf _ rfl, rfl⟩
      · exact absurd hr (List.not_mem_nil)
  | comb p q hp hq _ _ ih₁ ih₂ =>
    obtain ⟨μ₁, ν₁, α₁, β₁, hμ₁, hν₁, hs₁, hc₁⟩ := ih₁
    obtain ⟨μ₂, ν₂, α₂, β₂, hμ₂, hν₂, hs₂, hc₂⟩ := ih₂
    refine ⟨fun j => p * μ₁ j + q * μ₂ j, p * ν₁ + q * ν₂, p * α₁ + q * α₂,
      fun e => p * β₁ e + q * β₂ e, fun j => ?_, ?_, fun hs => ?_, ?_⟩
    · show 0 ≤ p * μ₁ j + q * μ₂ j
      have := Int.mul_nonneg hp (hμ₁ j); have := Int.mul_nonneg hq (hμ₂ j); omega
    · have := Int.mul_nonneg hp hν₁; have := Int.mul_nonneg hq hν₂; omega
    · simp only [comb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
      have := Int.mul_nonneg hp hν₁; have := Int.mul_nonneg hq hν₂
      rcases hs with ⟨hp', hs'⟩ | ⟨hq', hs'⟩
      · have := Int.mul_pos hp' (hs₁ hs'); omega
      · have := Int.mul_pos hq' (hs₂ hs'); omega
    · funext i
      simp only [comb]
      rw [hc₁, hc₂]
      by_cases hi : i.val < N
      · simp only [hrow, dif_pos hi]
        rw [dot_add_left, dot_smul_left, dot_smul_left]; ring
      · simp only [hrow, dif_neg hi]
        rw [dot_add_left, dot_smul_left, dot_smul_left]; ring

theorem hrow_eval_lam (μ : Fin N → Int) (ν α : Int) (β : Fin m → Int) (j : Fin N) :
    hrow S y d μ ν α β j.castSucc = μ j + α + d * dot m β (S j) := by
  simp only [hrow]; rw [dif_pos (by simp)]; rfl

theorem hrow_eval_t (μ : Fin N → Int) (ν α : Int) (β : Fin m → Int) :
    hrow S y d μ ν α β (Fin.last N) = ν - α - dot m β y := by
  simp only [hrow]; rw [dif_neg (by simp [Fin.last])]

/-- **Constructive completeness for convex hulls.** If every integer affine law valid on the
points `S j` holds at `y / d`, then `y / d` is a convex combination of the `S j`, with weights
`λ j / t`. -/
theorem complete (hd : 0 < d)
    (hlaw : ∀ (c : Fin m → Int) (k : Int), (∀ j, k ≤ dot m c (S j)) → k * d ≤ dot m c y) :
    ∃ (lam : Fin N → Int) (t : Int), 0 < t ∧ (∀ j, 0 ≤ lam j) ∧
      dot N (fun _ => 1) lam = t ∧ ∀ e, d * dot N lam (fun j => S j e) = t * y e := by
  rcases fm (N + 1) (hullRows S y d) with ⟨w, hw⟩ | hder
  · -- read the weights off the solution
    let lam : Fin N → Int := fun j => w j.castSucc
    let t : Int := w (Fin.last N)
    have val : ∀ (μ : Fin N → Int) (ν α : Int) (β : Fin m → Int),
        dot (N + 1) (hrow S y d μ ν α β) w =
          dot N μ lam + α * (dot N (fun _ => 1) lam - t) +
            d * dot m β (fun e => dot N (fun j => S j e) lam) + (ν - dot m β y) * t := by
      intro μ ν α β
      simp only [dot]
      rw [dot_congr N _ (fun j => μ j + α * 1 + d * dot m β (S j)) _ (fun j => by
        rw [hrow_eval_lam]; ring), hrow_eval_t, dot_add_left, dot_add_left, dot_smul_left,
        dot_smul_left, dot_swap]
      ring
    have mem_pos : ∀ j, (⟨hrow S y d (fun k => if k = j then 1 else 0) 0 0 (fun _ => 0), false⟩ :
        Row (N + 1)) ∈ hullRows S y d := fun j =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩))
    have mem3 : ∀ r ∈ ([⟨hrow S y d (fun _ => 0) 1 0 (fun _ => 0), true⟩,
        ⟨hrow S y d (fun _ => 0) 0 1 (fun _ => 0), false⟩,
        ⟨hrow S y d (fun _ => 0) 0 (-1) (fun _ => 0), false⟩] : List (Row (N + 1))),
        r ∈ hullRows S y d := fun r hr =>
      List.mem_append_left _ (List.mem_append_right _ hr)
    have mem_eq : ∀ e, (⟨hrow S y d (fun _ => 0) 0 0 (fun k => if k = e then 1 else 0), false⟩ :
        Row (N + 1)) ∈ hullRows S y d ∧
        (⟨hrow S y d (fun _ => 0) 0 0 (fun k => if k = e then -1 else 0), false⟩ :
        Row (N + 1)) ∈ hullRows S y d := fun e =>
      ⟨List.mem_append_right _ (List.mem_flatMap.2 ⟨e, List.mem_finRange e, List.mem_cons_self ..⟩),
       List.mem_append_right _ (List.mem_flatMap.2 ⟨e, List.mem_finRange e,
         List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩)⟩
    have z0 : ∀ g : Fin m → Int, dot m (fun _ => 0) g = 0 := dot_zero_left m
    have zN : ∀ g : Fin N → Int, dot N (fun _ => 0) g = 0 := dot_zero_left N
    have hneg := dot_negsingle (m := m)
    have nm := @Int.neg_mul
    refine ⟨lam, t, ?_, fun j => ?_, ?_, fun e => ?_⟩
    · have := (hw _ (mem3 _ (List.mem_cons_self ..))).2 rfl
      rw [val] at this
      simp only [zN, z0, Int.sub_zero, Int.one_mul, Int.zero_mul, Int.mul_zero, Int.add_zero,
        Int.zero_add] at this
      exact this
    · have := (hw _ (mem_pos j)).1
      rw [val, dot_single] at this
      simp only [z0, Int.sub_zero, Int.zero_sub, Int.zero_mul, Int.mul_zero, Int.add_zero,
        Int.zero_add, Int.neg_zero] at this
      exact this
    · have h1 := (hw _ (mem3 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).1
      have h2 := (hw _ (mem3 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))).1
      rw [val] at h1 h2
      simp only [zN, z0, Int.sub_zero, Int.zero_sub, Int.one_mul, Int.zero_mul, Int.mul_zero,
        Int.add_zero, Int.zero_add, Int.neg_zero] at h1 h2
      have : -1 * (dot N (fun _ => 1) lam - t) = -(dot N (fun _ => 1) lam - t) := by ring
      omega
    · have h1 := (hw _ (mem_eq e).1).1
      have h2 := (hw _ (mem_eq e).2).1
      rw [val, dot_single, dot_single] at h1
      rw [val, hneg, hneg] at h2
      simp only [zN, Int.zero_mul, Int.add_zero, Int.zero_add, Int.zero_sub] at h1 h2
      have e1 : d * -dot N (fun j => S j e) lam = -(d * dot N (fun j => S j e) lam) := by ring
      have e2 : - -y e * t = y e * t := by ring
      have e3 : -y e * t = -(y e * t) := by ring
      rw [dot_comm N lam]
      have : t * y e = y e * t := Int.mul_comm _ _
      omega
  · obtain ⟨μ, ν, α, β, hμ, hν, hs, hc⟩ := der_form S y d hder
    have hν' : 0 < ν := hs rfl
    have h0 : ∀ i, hrow S y d μ ν α β i = 0 := fun i => by rw [← hc]; rfl
    -- the separating law
    have hvalid : ∀ j, α ≤ dot m (fun e => -(d * β e)) (S j) := by
      intro j
      have := h0 j.castSucc
      rw [hrow_eval_lam] at this
      have e : dot m (fun e => -(d * β e)) (S j) = -(d * dot m β (S j)) := by
        rw [dot_congr m _ (fun e => (-d) * β e) _ (fun e => by ring), dot_smul_left]; ring
      rw [e]; have := hμ j; omega
    have hx := hlaw _ _ hvalid
    have ht := h0 (Fin.last N)
    rw [hrow_eval_t] at ht
    have e : dot m (fun e => -(d * β e)) y = -(d * dot m β y) := by
      rw [dot_congr m _ (fun e => (-d) * β e) _ (fun e => by ring), dot_smul_left]; ring
    rw [e] at hx
    have : dot m β y = ν - α := by omega
    rw [this] at hx
    have : d * ν > 0 := Int.mul_pos hd hν'
    have : α * d = d * α := Int.mul_comm _ _
    have : d * (ν - α) = d * ν - d * α := by ring
    exfalso
    omega

theorem dot_mono : ∀ (n : Nat) (lam a b : Fin n → Int), (∀ j, 0 ≤ lam j) → (∀ j, a j ≤ b j) →
    dot n lam a ≤ dot n lam b
  | 0, _, _, _, _, _ => Int.le_refl _
  | n + 1, lam, a, b, hl, hab => by
    simp only [dot]
    have := dot_mono n (fun i => lam i.castSucc) (fun i => a i.castSucc) (fun i => b i.castSucc)
      (fun i => hl _) (fun i => hab _)
    have := Int.mul_le_mul_of_nonneg_left (hab (Fin.last n)) (hl (Fin.last n))
    omega

theorem dot_const_right : ∀ (n : Nat) (lam : Fin n → Int) (k : Int),
    dot n lam (fun _ => k) = k * dot n (fun _ => 1) lam
  | 0, _, k => by simp only [dot]; ring
  | n + 1, lam, k => by simp only [dot]; rw [dot_const_right n]; ring

/-- **Soundness**: a convex combination satisfies every integer affine law valid on the points. -/
theorem sound (hd : 0 < d) (lam : Fin N → Int) (t : Int) (ht : 0 < t) (hl : ∀ j, 0 ≤ lam j)
    (hsum : dot N (fun _ => 1) lam = t) (hx : ∀ e, d * dot N lam (fun j => S j e) = t * y e)
    (c : Fin m → Int) (k : Int) (hc : ∀ j, k ≤ dot m c (S j)) : k * d ≤ dot m c y := by
  -- `t * (c · y) = d * Σ_j λ_j (c · S_j) ≥ d * k * t`
  have h1 : t * dot m c y = d * dot N lam (fun j => dot m c (S j)) := by
    rw [dot_comm N lam, dot_swap, ← dot_smul_right m t, ← dot_smul_right m d]
    apply congrArg (dot m c)
    funext e
    rw [dot_comm N (fun j => S j e) lam, hx e]
  have h2 : k * t ≤ dot N lam (fun j => dot m c (S j)) := by
    have := dot_mono N lam (fun _ => k) _ hl hc
    rw [dot_const_right, hsum] at this
    exact this
  have h3 := Int.mul_le_mul_of_nonneg_left h2 (Int.le_of_lt hd)
  have e : d * (k * t) = t * (k * d) := by ring
  rw [e, ← h1] at h3
  exact Int.le_of_mul_le_mul_left h3 ht

end Hull

end ConstructiveProb.Farkas
