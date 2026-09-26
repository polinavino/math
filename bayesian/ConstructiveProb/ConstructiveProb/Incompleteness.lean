/-
# Abstract Gödel-incompleteness schema — a diagonal argument against sound provers

This file formalizes the *abstract schema* behind Gödel's First Incompleteness Theorem, in the
same confirm/refute-asymmetry spirit as the paper's halting-slack examples
(`Halting.lean`, `Sierpinski.lean`): if a sound theory's proofs of non-halting are themselves
recursively enumerable, there is a machine whose non-halting the theory can never certify, even
though it is true.

The concrete motivating instance is Aaronson–Yedidia's explicit Turing machine whose halting
status is independent of ZFC (assuming ZFC is consistent): `Provable c` there would be "ZFC
proves `c` does not halt on input `0`," an `REPred` since ZFC's proof system is recursively
axiomatized, and `hsound` is exactly the assumption that ZFC is consistent (a sound theory only
proves true non-halting facts). **This file mechanizes only the abstract schema.** Instantiating
`Provable` with actual ZFC-derivability and connecting the conclusion to the concrete
Aaronson–Yedidia machine is explicitly left to future work: doing so needs a formalization of
ZFC's proof calculus, which this project does not build or import.

The construction is Kleene's self-reference trick (`Nat.Partrec.Code.fixed_point₂`), used
elsewhere in computability theory to prove Gödel's and Rice's theorems without first-order syntax:
build a machine `d` that runs forever unless the theory has proved `d` itself does not halt, in
which case `d` halts immediately. If the theory ever proved `d` doesn't halt, `d` would halt,
contradicting soundness; so the theory never proves it, and hence (again by soundness's
contrapositive being unavailable to the theory) `d` genuinely does not halt.
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace ConstructiveProb

/-- The diagonal construction: on input `(c, n)`, halt with output `0` if `Provable c` (read as
"the theory proves `c` does not halt on input `0`"), and otherwise run forever. -/
noncomputable def proverDiag (Provable : Code → Prop) (c : Code) (_n : ℕ) : Part ℕ :=
  Part.assert (Provable c) (fun _ => Part.some 0)

theorem partrec₂_proverDiag {Provable : Code → Prop} (hre : REPred Provable) :
    Partrec₂ (proverDiag Provable) := by
  have h1 : Partrec (fun p : Code × ℕ => Part.assert (Provable p.1) (fun _ => Part.some ())) :=
    hre.comp Computable.fst
  have h2 := h1.map (Computable.const (0 : ℕ)).to₂
  refine h2.of_eq fun p => Part.ext fun a => ?_
  simp [proverDiag, Part.mem_map_iff, Part.mem_assert_iff, eq_comm]

/-- **Abstract Gödel incompleteness.** If a theory's proofs of non-halting form a recursively
enumerable predicate `Provable`, and the theory is sound (every non-halting it proves is true),
then some machine `d` genuinely does not halt on input `0`, yet the theory never proves this. -/
theorem exists_true_unprovable_nonhalting {Provable : Code → Prop} (hre : REPred Provable)
    (hsound : ∀ c, Provable c → ¬(eval c 0).Dom) :
    ∃ d : Code, ¬(eval d 0).Dom ∧ ¬Provable d := by
  obtain ⟨d, hd⟩ := fixed_point₂ (partrec₂_proverDiag hre)
  have hiff : (eval d 0).Dom ↔ Provable d := by
    rw [hd]
    unfold proverDiag
    simp [Part.assert]
  have hnp : ¬Provable d := fun hp => hsound d hp (hiff.mpr hp)
  exact ⟨d, hiff.not.mpr hnp, hnp⟩

/-- **No sound, recursively axiomatized theory is complete for true non-halting facts:** there is
always a true non-halting instance the theory fails to prove. -/
theorem not_complete {Provable : Code → Prop} (hre : REPred Provable)
    (hsound : ∀ c, Provable c → ¬(eval c 0).Dom) :
    ¬∀ c, ¬(eval c 0).Dom → Provable c := by
  obtain ⟨d, hnd, hnp⟩ := exists_true_unprovable_nonhalting hre hsound
  exact fun hcomplete => hnp (hcomplete d hnd)

/-- **Classical decidability of halting at a point.** The halting question for `c` is settled
either by observation — `c` halts, exhibited by running it — or by a sound proof from `Provable`
that it does not. This is the operational content of "classical probability applies to `c`": not
that a sharp truth value exists in the classical meta-theory (it always does, trivially, by
excluded middle), but that it is backed by an actual witness available to us. -/
def Decided (Provable : Code → Prop) (c : Code) : Prop :=
  (eval c 0).Dom ∨ Provable c

/-- **Pointwise failure of classical decidability.** If `Decided Provable c` held for a given
`c`, then in particular the sharp classical value at `c` would be decidable: confirmed if `c`
halts, refuted by the theory if it does not. This exhibits a specific `d` for which `Decided`
fails outright — neither half of the dichotomy is available — even though `d` genuinely does
not halt. Unlike `exists_true_unprovable_nonhalting`, which only says the theory cannot *prove*
`d`'s non-halting, this additionally records that the "confirm" side is not available either
(`d` does not halt, so running it never terminates), so *no* route to a classically decided
value exists at `d`, not just the proof-theoretic one. -/
theorem exists_not_decided {Provable : Code → Prop} (hre : REPred Provable)
    (hsound : ∀ c, Provable c → ¬(eval c 0).Dom) :
    ∃ d : Code, ¬Decided Provable d ∧ ¬(eval d 0).Dom := by
  obtain ⟨d, hnd, hnp⟩ := exists_true_unprovable_nonhalting hre hsound
  exact ⟨d, not_or.mpr ⟨hnd, hnp⟩, hnd⟩

end ConstructiveProb
