import Challenge.Setting
import Challenge.Touching

/-!
# Challenge vocabulary: viscosity sub- and supersolutions

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Setting` and
`Challenge.Touching`). Restates definitions of the library file
`ParabolicBasic/Defs/Viscosity.lean`.

* **Standard notion** `IsViscSubOn Ω F u`, `IsViscSuperOn Ω F u`: viscosity sub/supersolutions of
  `dₜu - lapₓu + F p (u p) ≤ 0` (resp. `≥ 0`) on `Ω ⊆ E d × ℝ`, with global `C²` test functions
  touching relative to `Ω`. [CIL, §8]
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-- Standard viscosity subsolution of `dₜu - lapₓu + F p (u p) ≤ 0` on `Ω`:
`u` is upper semicontinuous on `Ω`, and whenever a global `C²` function `ψ` touches `u` from above
at `p ∈ Ω` (relative to `Ω`), `dₜ ψ p - lapₓ ψ p + F p (u p) ≤ 0`. -/
def IsViscSubOn (Ω : Set (E d × ℝ)) (F : E d × ℝ → ℝ → ℝ) (u : E d × ℝ → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ Ω,
    TouchesAbove ψ u Ω p → dₜ ψ p - lapₓ ψ p + F p (u p) ≤ 0

/-- Standard viscosity supersolution of `dₜu - lapₓu + F p (u p) ≥ 0` on `Ω`:
`u` is lower semicontinuous on `Ω`, and whenever a global `C²` function `ψ` touches `u` from below
at `p ∈ Ω` (relative to `Ω`), `0 ≤ dₜ ψ p - lapₓ ψ p + F p (u p)`. -/
def IsViscSuperOn (Ω : Set (E d × ℝ)) (F : E d × ℝ → ℝ → ℝ) (u : E d × ℝ → ℝ) : Prop :=
  LowerSemicontinuousOn u Ω ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ Ω,
    TouchesBelow ψ u Ω p → 0 ≤ dₜ ψ p - lapₓ ψ p + F p (u p)

end ParabolicBasic
