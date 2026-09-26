/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Viscosity.Basic

/-!
# Smooth viscosity solutions are classical

A `C²` viscosity sub/supersolution on an open set satisfies the inequality pointwise, since it is
its own test function (`IsViscSubOn.of_contDiffOn_test`).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- A `C²` viscosity subsolution on an open set is a classical subsolution. -/
theorem IsViscSubOn.heat_le_of_contDiffOn {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hv : IsViscSubOn Ω F u) :
    ∀ p ∈ Ω, dₜ u p - lapₓ u p + F p (u p) ≤ 0 := fun _ hp ↦
  hv.of_contDiffOn_test hΩ hp hu ⟨hp, rfl, Eventually.of_forall fun _ ↦ le_rfl⟩

/-- A `C²` viscosity supersolution on an open set is a classical supersolution. -/
theorem IsViscSuperOn.le_heat_of_contDiffOn {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hv : IsViscSuperOn Ω F u) :
    ∀ p ∈ Ω, 0 ≤ dₜ u p - lapₓ u p + F p (u p) := fun _ hp ↦
  hv.of_contDiffOn_test hΩ hp hu ⟨hp, rfl, Eventually.of_forall fun _ ↦ le_rfl⟩

end ParabolicBasic
