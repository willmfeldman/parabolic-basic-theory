/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Transport.Operator
public import ParabolicBasic.Transport.Viscosity
public import ViscositySolns.Comparison.ProperComparison.Compact.ConstantShiftBoundary

/-!
# Comparison on a bounded open set against the full frontier

This is where the comparison theorem calls the comparison principle of `ViscositySolns`:
`comparison_of_constantShift_boundary_of_aleksandrov`, applied to the transported set
`toPointSet Ω ⊆ Point (d + 1)` and operator `parabolicOp G`, with the Ishii lemma supplied by
`AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external`.

The boundary data are required on the whole topological frontier of `Ω` (the
`BoundaryComparisonOn` of `ViscositySolns`); the parabolic boundary is handled in
`Comparison/Parabolic.lean`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Comparison on a bounded open set, full frontier.**
`G` has uniform slope `γ > 0` in `r` (i), is jointly continuous (ii), and has a monotone
comparison modulus in `p ∈ Ω`, uniformly in `r ≤ M` (iii). -/
theorem comparison_frontier {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {G : E d × ℝ → ℝ → ℝ} {γ M : ℝ} (hγ : 0 < γ)
    (hGmono : ∀ p r s, r ≤ s → G p r + γ * (s - r) ≤ G p s)
    (hGc : Continuous fun q : (E d × ℝ) × ℝ ↦ G q.1 q.2)
    (hGmod : ∃ ρ : ℝ → ℝ, ViscositySolns.ComparisonModulus ρ ∧ Monotone ρ ∧
      ∀ p ∈ Ω, ∀ q ∈ Ω, ∀ r ≤ M, G q r - G p r ≤ ρ (dist p q))
    {u v : E d × ℝ → ℝ} (husc : UpperSemicontinuousOn u (closure Ω))
    (hvlsc : LowerSemicontinuousOn v (closure Ω)) (huM : ∀ p ∈ Ω, u p ≤ M)
    (hsub : IsViscSubOn Ω G u) (hsuper : IsViscSuperOn Ω G v)
    (hbdry : ∀ p ∈ frontier Ω, u p ≤ v p) :
    ∀ p ∈ Ω, u p ≤ v p := by
  intro p hp
  obtain ⟨ρ, hρ, hρm, hmod⟩ := hGmod
  have := locallyCompactSpace_toPointSet hΩ
  have hmonoG : ∀ p, Monotone (G p) := fun p r s hrs ↦ by
    have := hGmono p r s hrs
    nlinarith [mul_nonneg hγ.le (sub_nonneg.2 hrs)]
  have key := ViscositySolns.comparison_of_constantShift_boundary_of_aleksandrov
    (ViscositySolns.AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external _)
    (C := toPointSet Ω) (R := Iic M) (F := parabolicOp G) (u := toPointFun u)
    (v := toPointFun v)
    (parabolicOp_proper hmonoG) (parabolicOp_operatorContinuous hGc)
    (parabolicOp_ishiiCondition hρ hρm fun p hp q hq r hr ↦ hmod p hp q hq r hr)
    (fun z hz ↦ by rw [frontier_toPointSet] at hz; exact hbdry _ hz)
    (fun z hz ↦ huM _ hz) (ViscositySolns.ClosedUnderSubNonneg.Iic M)
    (toPointSet_nonempty_iff.2 ⟨p, hp⟩)
    (compactClosure_toPointSet hΩb.isCompact_closure)
    hsub.toViscositySubsolution hsuper.toViscositySupersolution
    (by rw [closure_toPointSet]; exact upperSemicontinuousOn_toPointFun_iff.2 husc)
    (by rw [closure_toPointSet]; exact lowerSemicontinuousOn_toPointFun_iff.2 hvlsc)
    (fun η hη ↦ ⟨η, γ * η, hη, le_rfl, mul_pos hγ hη,
      parabolicOp_uniformScalarDecreaseOn fun q _ r ↦ by
        have := hGmono q (r - η) r (by linarith)
        linarith⟩)
  simpa using key (spaceTimeEquiv d p) (by simpa using hp)

end ParabolicBasic
