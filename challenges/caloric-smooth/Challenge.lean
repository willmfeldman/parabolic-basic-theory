import Challenge.Viscosity

/-!
# Challenge: viscosity solutions of the heat equation are smooth

Trusted statement surface for interior regularity of viscosity caloric functions: a continuous
viscosity solution of the heat equation `∂ₜu = Δₓu` on an open set `O ⊆ ℝᵈ × ℝ` is `C^∞` on `O`
and satisfies the equation classically. The library proves this by mollification, Bernstein-type
interior derivative estimates for smooth caloric functions, and stability of viscosity solutions
under local uniform limits.

All project vocabulary is restated inline in `Challenge/Setting.lean` and
`Challenge/Viscosity.lean`, which import `Mathlib` only. The conclusion is stated with Mathlib's
`ContDiffOn` and the slice derivatives `dₜ`, `lapₓ`, not through the library's
`IsSmoothCaloricOn`.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Viscosity caloric functions are smooth.** Let `O ⊆ ℝᵈ × ℝ` be open and `u` continuous on
`O`. Suppose `u` is a viscosity subsolution and a viscosity supersolution of `∂ₜu - Δₓu = 0` on
`O` in the standard sense (zero-order term `F = 0`): whenever a global `C²` function `ψ` touches
`u` from above (resp. below) at `p ∈ O`, `∂ₜψ p - Δₓψ p ≤ 0` (resp. `≥ 0`). Then `u` is `C^∞` on
`O` jointly in space and time, and `∂ₜu = Δₓu` at every point of `O`, with `∂ₜ` the two-sided
time derivative and `Δₓ` Mathlib's Laplacian of the time slice.

Smoothness is `ContDiffOn ℝ ∞` (`C^∞`), not `ContDiffOn ℝ ω` (analytic): caloric functions need
not be analytic in time. The continuity hypothesis `hu` is implied by `hsub` and `hsuper` (upper
and lower semicontinuity), and is kept as in the library. Valid for all `d`, including `d = 0`,
where the statement is about `u' = 0` in one time variable. Degenerate case: `O = ∅` makes the
conclusion trivial. -/
theorem challenge_caloric_smooth {O : Set (E d × ℝ)} (hO : IsOpen O) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u O) (hsub : IsViscSubOn O (fun _ _ ↦ 0) u)
    (hsuper : IsViscSuperOn O (fun _ _ ↦ 0) u) :
    ContDiffOn ℝ ∞ u O ∧ ∀ p ∈ O, dₜ u p = lapₓ u p := by
  sorry

end ParabolicBasic
