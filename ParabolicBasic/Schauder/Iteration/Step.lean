/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Iteration.Approx

/-!
# One step of the iteration: improvement of flatness

With `C_T := max C 1` (`C` the constant of `taylor_approx`) the contraction radius is
`ρ := (2 C_T)^{-1/(1-α)} ∈ (0, 1/2]` (so `C_T ρ^{1-α} = 1/2`; the `max · 1` keeps `ρ ≤ 1/2`, also
for `d = 0`), and the smallness of the source is `δ₀ := ρ^{k+α}/4`.
If `u` solves `dₜu − lapₓu = H` on `Q₁`, `|u| ≤ 1`, `|H| ≤ δ₀`, then a caloric polynomial `P` of
degree `≤ k` with bounded coefficients approximates `u` to order `ρ^{k+α}` on `cCyl 0 0 ρ`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Improvement of flatness.** There are `ρ ∈ (0, 1/2]` and `C₀ ≥ 0` (depending only on `d` and
`α`) such that for `k ≤ 2`: if `u` is continuous on `closure Q₁`, solves `dₜu − lapₓu = H` on `Q₁`,
`|u| ≤ 1` and `|H| ≤ ρ^{k+α}/4` on `Q₁`, then there is a caloric polynomial `P` (`src P = 0`) of
degree `≤ k` with `coeffNorm P ≤ C₀` and `|u − P| ≤ ρ^{k+α}` on `cCyl 0 0 ρ`. -/
theorem improvement_of_flatness {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ ρ C₀ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 ≤ C₀ ∧ ∀ k : ℕ, k ≤ 2 → ∀ {u H : E d × ℝ → ℝ},
      ContinuousOn u (closure (cCyl (0 : E d) 0 1)) → IsHeatSolOn (cCyl (0 : E d) 0 1) H u →
      (∀ q ∈ cCyl (0 : E d) 0 1, |u q| ≤ 1) →
      (∀ q ∈ cCyl (0 : E d) 0 1, |H q| ≤ ρ ^ ((k : ℝ) + α) / 4) →
      ∃ P : CaloricPoly d, P.src = 0 ∧ P.IsDegLE k ∧ P.coeffNorm ≤ C₀ ∧
        ∀ q ∈ cCyl (0 : E d) 0 ρ, |u q - P.eval q| ≤ ρ ^ ((k : ℝ) + α) := by
  obtain ⟨C, hC, hT⟩ := taylor_approx (d := d)
  set CT := max C 1 with hCTdef
  have hCT1 : 1 ≤ CT := le_max_right _ _
  have hCTne : CT ≠ 0 := by positivity
  have hb : 0 < 2 * CT := by positivity
  have h1α : 0 < 1 - α := by linarith
  set ρ := (2 * CT) ^ (-(1 / (1 - α))) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hb _
  have hρα : ρ ^ (1 - α) = (2 * CT)⁻¹ := by
    rw [hρdef, ← Real.rpow_mul hb.le,
      show -(1 / (1 - α)) * (1 - α) = -1 by field_simp, Real.rpow_neg_one]
  have hρ1 : ρ ≤ 1 := by
    refine (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) ?_).le
    have : 0 < 1 / (1 - α) := by positivity
    linarith
  have hρhalf : ρ ≤ 1 / 2 := by
    calc ρ = ρ ^ (1 : ℝ) := (Real.rpow_one ρ).symm
      _ ≤ ρ ^ (1 - α) := Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith)
      _ = (2 * CT)⁻¹ := hρα
      _ ≤ 2⁻¹ := inv_anti₀ two_pos (by linarith)
      _ = 1 / 2 := by norm_num
  have hkey : ∀ k : ℕ, C * ρ ^ (k + 1) ≤ ρ ^ ((k : ℝ) + α) / 2 := fun k ↦ by
    have e : ρ ^ (k + 1) = ρ ^ ((k : ℝ) + α) * ρ ^ (1 - α) := by
      rw [← Real.rpow_add hρ0, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hX : 0 ≤ ρ ^ ((k : ℝ) + α) := Real.rpow_nonneg hρ0.le _
    rw [e, hρα]
    calc C * (ρ ^ ((k : ℝ) + α) * (2 * CT)⁻¹) ≤ CT * (ρ ^ ((k : ℝ) + α) * (2 * CT)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = ρ ^ ((k : ℝ) + α) / 2 := by
        rw [show CT * (ρ ^ ((k : ℝ) + α) * (2 * CT)⁻¹) =
            ρ ^ ((k : ℝ) + α) / 2 * (CT * CT⁻¹) by ring, mul_inv_cancel₀ hCTne, mul_one]
  refine ⟨ρ, C, hρ0, hρhalf, hC, fun k hk {u H} hu hsol hu1 hH ↦ ?_⟩
  obtain ⟨h, hcal, hh1, huh⟩ := exists_caloric_approx hu hsol hH hu1
  obtain ⟨hdeg, hsrc, hcoef, herr⟩ :=
    hT k hk hcal fun q hq ↦ hh1 q (subset_closure hq)
  refine ⟨taylorPoly k h, hsrc, hdeg, hcoef, fun q hq ↦ ?_⟩
  have hq1 : q ∈ cCyl (0 : E d) 0 1 := cCyl_subset_cCyl hρ0.le hρ1 hq
  have a := huh q (subset_closure hq1)
  have b := herr ρ hρ0 hρhalf q hq
  have c := hkey k
  calc |u q - (taylorPoly k h).eval q| = |(u q - h q) + (h q - (taylorPoly k h).eval q)| := by
        ring_nf
    _ ≤ |u q - h q| + |h q - (taylorPoly k h).eval q| := abs_add_le _ _
    _ ≤ ρ ^ ((k : ℝ) + α) := by linarith

end ParabolicBasic
