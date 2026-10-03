module

public import ParabolicBasic

@[expose] public section

/-!
# Solution: viscosity solutions of the heat equation are smooth

Discharges the challenge through the library theorem `ParabolicBasic.isSmoothCaloricOn_of_isVisc`.
Its conclusion `IsSmoothCaloricOn O u` is by definition
`ContDiffOn ℝ ∞ u O ∧ ∀ p ∈ O, dₜ u p = lapₓ u p`.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

theorem challenge_caloric_smooth {O : Set (E d × ℝ)} (hO : IsOpen O) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u O) (hsub : IsViscSubOn O (fun _ _ ↦ 0) u)
    (hsuper : IsViscSuperOn O (fun _ _ ↦ 0) u) :
    ContDiffOn ℝ ∞ u O ∧ ∀ p ∈ O, dₜ u p = lapₓ u p := by
  have h : IsSmoothCaloricOn O u := isSmoothCaloricOn_of_isVisc hO hu hsub hsuper
  exact ⟨h.1, h.2⟩

end ParabolicBasic
