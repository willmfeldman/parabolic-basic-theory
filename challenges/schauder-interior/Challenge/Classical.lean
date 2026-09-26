import Challenge.Setting

/-!
# Challenge vocabulary: classical `C^{2,1}` functions

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Setting`). It
restates, token for token, the definition `IsC21On` of `ParabolicBasic/Defs/Classical.lean`:
`u`, `∇ₓu`, `D²ₓu` and the two-sided `∂ₜu` exist and are continuous on `U × I`.

This file is separate from `Challenge.Setting` because Comparator checks the names of the
auxiliary proofs Lean creates inside definitions, and Lean shares those only within a file; the
auxiliary proof for the numeral `2` in `IsC21On` must be created here, not reused from
`HasC2Boundary`.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- `u` is classical `C^{2,1}` on `U × I`: `u`, `∇ₓu`, `D²ₓu`, `∂ₜu` exist and are continuous on
`U × I` (the time derivative is two-sided). -/
def IsC21On (U : Set (E d)) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧
    (∀ t ∈ I, ContDiffOn ℝ 2 (fun x ↦ u (x, t)) U) ∧
    ContinuousOn (gradₓ u) (U ×ˢ I) ∧
    ContinuousOn (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1) (U ×ˢ I) ∧
    (∀ p ∈ U ×ˢ I, DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2) ∧
    ContinuousOn (dₜ u) (U ×ˢ I)

end ParabolicBasic
