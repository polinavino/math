/-
# Valuations beyond frames: how much survives without completeness

Companion to `Basic.lean` and `Points.lean`, prompted by a question the paper's conclusion
leaves open: is there an ambient category sending an event algebra to its probability calculus
functorially, beyond the single instance (frames) the paper works out?

`Basic.lean`'s four valuation axioms (`map_bot'`, `map_top'`, `mono'`, `modular'`) never
mention `sSup` or frame completeness -- only `⊥, ⊤, ⊔, ⊓`. So the structure, and `Points.lean`'s
pullback functor `Valuation.comap`, generalize verbatim from frames down to plain bounded
lattices (Part 1 below). The sharp/point correspondence (`sharp_iff_point`,
`exists_sharp_separating`) does not come along for free: tracing the proof shows it factors
through `DistribLattice.prime_ideal_of_disjoint_filter_ideal`, a genuinely
distributivity-dependent separation theorem (Part 2). `NonDistributive.lean` shows this is not
a technical artifact of the proof: it exhibits a bounded lattice on which no valuation is sharp
at all.
-/
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.PrimeSeparator
import Mathlib.Data.ENNReal.Basic

open scoped ENNReal

noncomputable section

/-! ## Part 1: the four axioms and the functor, over a plain bounded lattice -/

/-- Same four axioms as `Valuation` (`Basic.lean`), stated over any bounded lattice instead of
a frame. -/
structure LValuation (Ω : Type*) [Lattice Ω] [BoundedOrder Ω] where
  toFun : Ω → ℝ≥0∞
  map_bot' : toFun ⊥ = 0
  map_top' : toFun ⊤ = 1
  mono' : Monotone toFun
  modular' : ∀ a b, toFun a + toFun b = toFun (a ⊔ b) + toFun (a ⊓ b)

namespace LValuation

variable {Ω : Type*} [Lattice Ω] [BoundedOrder Ω]

instance : CoeFun (LValuation Ω) (fun _ => Ω → ℝ≥0∞) := ⟨toFun⟩

attribute [ext] LValuation

@[simp] theorem map_bot (v : LValuation Ω) : v ⊥ = 0 := v.map_bot'
@[simp] theorem map_top (v : LValuation Ω) : v ⊤ = 1 := v.map_top'
theorem mono (v : LValuation Ω) : Monotone v := v.mono'
theorem modular (v : LValuation Ω) (a b : Ω) :
    v a + v b = v (a ⊔ b) + v (a ⊓ b) := v.modular' a b

theorem le_one (v : LValuation Ω) (a : Ω) : v a ≤ 1 := by
  simpa using v.mono (le_top : a ≤ ⊤)

/-- A valuation is **sharp** if it only takes values `0` or `1`. -/
def IsSharp (v : LValuation Ω) : Prop := ∀ a, v a = 0 ∨ v a = 1

/-- **The functor part of `Val`, without completeness.** `Points.lean`'s `Valuation.comap` used
a `FrameHom`; the proof never touched `sSup`, so a plain `BoundedLatticeHom` suffices. -/
def comap {Γ : Type*} [Lattice Γ] [BoundedOrder Γ] (f : BoundedLatticeHom Γ Ω)
    (v : LValuation Ω) : LValuation Γ where
  toFun a := v (f a)
  map_bot' := by simp
  map_top' := by simp
  mono' _ _ h := v.mono (OrderHomClass.mono f h)
  modular' a b := by simpa only [map_sup, map_inf] using v.modular (f a) (f b)

@[simp] theorem comap_apply {Γ : Type*} [Lattice Γ] [BoundedOrder Γ] (f : BoundedLatticeHom Γ Ω)
    (v : LValuation Ω) (a : Γ) : v.comap f a = v (f a) := rfl

@[simp] theorem comap_id (v : LValuation Ω) : v.comap (BoundedLatticeHom.id Ω) = v :=
  LValuation.ext (funext fun _ => rfl)

theorem comap_comp {Γ Δ : Type*} [Lattice Γ] [BoundedOrder Γ] [Lattice Δ] [BoundedOrder Δ]
    (f : BoundedLatticeHom Γ Ω) (g : BoundedLatticeHom Δ Γ) (v : LValuation Ω) :
    v.comap (f.comp g) = (v.comap f).comap g :=
  LValuation.ext (funext fun _ => rfl)

end LValuation

/-! ## Part 2: the sharp/point correspondence needs only distributivity, not completeness

Reruns `Basic.lean`'s prime-ideal-indicator construction and `Points.lean`'s separation theorem
verbatim over `[DistribLattice Ω]` in place of `[Order.Frame Ω]`, to isolate exactly how much
of "niceness" (condition (1): the all-or-nothing valuations reconstruct the underlying logic)
survives dropping completeness while keeping distributivity. Answer: all of it. -/

section PrimeIdealValuation

variable {Ω : Type*} [DistribLattice Ω] [BoundedOrder Ω]

open scoped Classical

/-- The complement-indicator of a prime ideal `J` (with `⊤ ∉ J`) as a valuation: `0` on `J`,
`1` off it. Modularity holds because `J` is prime. -/
noncomputable def Ideal.toLValuation (J : Order.Ideal Ω) (hJ : J.IsPrime) (htop : ⊤ ∉ J) :
    LValuation Ω where
  toFun x := if x ∈ J then 0 else 1
  map_bot' := by rw [if_pos J.bot_mem]
  map_top' := by rw [if_neg htop]
  mono' a b hab := by
    change (if a ∈ J then (0 : ℝ≥0∞) else 1) ≤ if b ∈ J then 0 else 1
    split_ifs with ha hb hb
    · exact le_rfl
    · exact zero_le
    · exact absurd (J.lower hab hb) ha
    · exact le_rfl
  modular' a b := by
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · have h1 : a ⊔ b ∈ J := Order.Ideal.sup_mem ha hb
      have h2 : a ⊓ b ∈ J := J.lower inf_le_left ha
      rw [if_pos ha, if_pos hb, if_pos h1, if_pos h2]
    · have h1 : a ⊔ b ∉ J := fun h => hb (J.lower le_sup_right h)
      have h2 : a ⊓ b ∈ J := J.lower inf_le_left ha
      rw [if_pos ha, if_neg hb, if_neg h1, if_pos h2, zero_add, add_zero]
    · have h1 : a ⊔ b ∉ J := fun h => ha (J.lower le_sup_left h)
      have h2 : a ⊓ b ∈ J := J.lower inf_le_right hb
      rw [if_neg ha, if_pos hb, if_neg h1, if_pos h2]
    · have h1 : a ⊔ b ∉ J := fun h => ha (J.lower le_sup_left h)
      have h2 : a ⊓ b ∉ J := fun h => (hJ.mem_or_mem h).elim ha hb
      rw [if_neg ha, if_neg hb, if_neg h1, if_neg h2]

theorem Ideal.toLValuation_apply (J : Order.Ideal Ω) (hJ : J.IsPrime) (htop : ⊤ ∉ J) (x : Ω) :
    Ideal.toLValuation J hJ htop x = if x ∈ J then 0 else 1 := rfl

theorem Ideal.toLValuation_isSharp (J : Order.Ideal Ω) (hJ : J.IsPrime) (htop : ⊤ ∉ J) :
    (Ideal.toLValuation J hJ htop).IsSharp := by
  intro x
  rw [Ideal.toLValuation_apply]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Sharp valuations separate points, given only distributivity.** Same argument as
`Points.lean`'s `exists_sharp_separating`, with `[Order.Frame Ω]` weakened to
`[DistribLattice Ω]`: completeness was never used. -/
theorem LValuation.exists_sharp_separating {a b : Ω} (hab : ¬ a ≤ b) :
    ∃ v : LValuation Ω, v.IsSharp ∧ v a = 1 ∧ v b = 0 := by
  classical
  have hdisj : Disjoint (↑(Order.PFilter.principal a) : Set Ω)
      (↑(Order.Ideal.principal b) : Set Ω) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    rw [SetLike.mem_coe, Order.PFilter.mem_principal] at hx
    rw [SetLike.mem_coe, Order.Ideal.mem_principal] at hx2
    exact hab (hx.trans hx2)
  obtain ⟨J, hJprime, hIJ, hJF⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdisj
  have hbJ : b ∈ J := SetLike.le_def.mp hIJ Order.Ideal.mem_principal_self
  have haF : a ∈ (↑(Order.PFilter.principal a) : Set Ω) :=
    SetLike.mem_coe.mpr (Order.PFilter.mem_principal.mpr le_rfl)
  have haJ : a ∉ J := by
    have hnot := Set.disjoint_left.mp hJF haF
    rwa [SetLike.mem_coe] at hnot
  have htop : (⊤ : Ω) ∉ J := by
    have hTF : (⊤ : Ω) ∈ (↑(Order.PFilter.principal a) : Set Ω) :=
      SetLike.mem_coe.mpr (Order.PFilter.mem_principal.mpr le_top)
    have hnot := Set.disjoint_left.mp hJF hTF
    rwa [SetLike.mem_coe] at hnot
  exact ⟨Ideal.toLValuation J hJprime htop, Ideal.toLValuation_isSharp J hJprime htop,
    by rw [Ideal.toLValuation_apply, if_neg haJ], by rw [Ideal.toLValuation_apply, if_pos hbJ]⟩

end PrimeIdealValuation
