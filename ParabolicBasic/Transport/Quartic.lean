/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The space-time quartic strictifier

`spaceTimeQuartic p₀ q = (‖q.1 − p₀.1‖² + (q.2 − p₀.2)²)²`, built from the Euclidean norm on `E d`
(the product sup norm of `E d × ℝ` is not `C²`). It is `C^∞`, vanishes at `p₀` together with its
`dₜ` and `lapₓ`, and dominates `dist q p₀ ^ 4` (sup metric).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-- The quartic `(‖q.1 − p₀.1‖² + (q.2 − p₀.2)²)²` (Euclidean norm on `E d`). -/
noncomputable def spaceTimeQuartic (p₀ q : E d × ℝ) : ℝ :=
  (‖q.1 - p₀.1‖ ^ 2 + (q.2 - p₀.2) ^ 2) ^ 2

theorem spaceTimeQuartic_self (p₀ : E d × ℝ) : spaceTimeQuartic p₀ p₀ = 0 := by
  simp [spaceTimeQuartic]

theorem spaceTimeQuartic_nonneg (p₀ q : E d × ℝ) : 0 ≤ spaceTimeQuartic p₀ q := by
  unfold spaceTimeQuartic; positivity

/-- `p₀` is a global minimum (value `0`). -/
theorem isMinOn_spaceTimeQuartic (p₀ : E d × ℝ) : IsMinOn (spaceTimeQuartic p₀) univ p₀ :=
  fun q _ ↦ by simpa [spaceTimeQuartic_self] using spaceTimeQuartic_nonneg p₀ q

/-- `C^∞` (`∞`, not `ω`). -/
theorem contDiff_spaceTimeQuartic (p₀ : E d × ℝ) : ContDiff ℝ ∞ (spaceTimeQuartic p₀) := by
  unfold spaceTimeQuartic
  exact (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)).add
    ((contDiff_snd.sub contDiff_const).pow 2)).pow 2

/-- `dₜ` vanishes at `p₀` (the time slice has a minimum there). -/
theorem dₜ_spaceTimeQuartic_self (p₀ : E d × ℝ) : dₜ (spaceTimeQuartic p₀) p₀ = 0 := by
  unfold dₜ
  refine IsLocalMin.deriv_eq_zero (IsMinOn.isLocalMin (fun s _ ↦ ?_) univ_mem)
  simpa [spaceTimeQuartic_self] using spaceTimeQuartic_nonneg p₀ (p₀.1, s)

/-- The second derivative of `h ^ 2` vanishes at a zero minimum of a `C²` function `h`. -/
theorem fderiv_fderiv_sq_eq_zero_of_isLocalMin {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {h : F → ℝ} (hh : ContDiff ℝ 2 h) {x₀ : F} (h0 : h x₀ = 0)
    (hmin : IsLocalMin h x₀) : fderiv ℝ (fderiv ℝ fun y ↦ h y ^ 2) x₀ = 0 := by
  have hdiff : Differentiable ℝ h := hh.differentiable two_ne_zero
  have hD : fderiv ℝ (fun y ↦ h y ^ 2) = fun y ↦ (2 * h y) • fderiv ℝ h y := by
    funext y
    rw [((hdiff y).hasFDerivAt.pow 2).fderiv]
    congr 1
    simp [two_mul]
  have hc : HasFDerivAt (fun y ↦ 2 * h y) ((2 : ℝ) • fderiv ℝ h x₀) x₀ :=
    (hdiff x₀).hasFDerivAt.const_mul 2
  have hf : HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) x₀) x₀ :=
    ((hh.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x₀).hasFDerivAt
  rw [hD]
  have := hc.smul hf
  rw [show (fun y ↦ (2 * h y) • fderiv ℝ h y) = (fun y ↦ 2 * h y) • fderiv ℝ h from rfl,
    this.fderiv]
  simp [h0, hmin.fderiv_eq_zero]

/-- `lapₓ` vanishes at `p₀`: the space slice is `h²` with `h ≥ 0`, `h(p₀.1) = 0`, so its
second derivative vanishes there. -/
theorem lapₓ_spaceTimeQuartic_self (p₀ : E d × ℝ) : lapₓ (spaceTimeQuartic p₀) p₀ = 0 := by
  unfold lapₓ spaceTimeQuartic
  set h : E d → ℝ := fun y ↦ ‖y - p₀.1‖ ^ 2 + (p₀.2 - p₀.2) ^ 2 with hhdef
  have hh : ContDiff ℝ 2 h :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add contDiff_const
  have h0 : h p₀.1 = 0 := by simp [hhdef]
  have hmin : IsLocalMin h p₀.1 :=
    IsMinOn.isLocalMin (fun y _ ↦ by simp only [mem_setOf_eq, h0]; positivity) univ_mem
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ fun y ↦ h y ^ 2) p₀.1 _ _ = 0
  rw [fderiv_fderiv_sq_eq_zero_of_isLocalMin hh h0 hmin]
  rfl

/-- `dist q p₀ ^ 4 ≤ spaceTimeQuartic p₀ q` in the sup metric of `E d × ℝ`, since
`max(a, b)² ≤ a² + b²`. -/
theorem dist_pow_four_le_spaceTimeQuartic (p₀ q : E d × ℝ) :
    dist q p₀ ^ 4 ≤ spaceTimeQuartic p₀ q := by
  have hsq : dist q p₀ ^ 2 ≤ ‖q.1 - p₀.1‖ ^ 2 + (q.2 - p₀.2) ^ 2 := by
    rw [Prod.dist_eq, dist_eq_norm, Real.dist_eq]
    rcases le_total ‖q.1 - p₀.1‖ |q.2 - p₀.2| with hle | hle
    · rw [max_eq_right hle, sq_abs]; nlinarith [sq_nonneg ‖q.1 - p₀.1‖]
    · rw [max_eq_left hle]; nlinarith [sq_nonneg (q.2 - p₀.2)]
  calc dist q p₀ ^ 4 = (dist q p₀ ^ 2) ^ 2 := by ring
    _ ≤ (‖q.1 - p₀.1‖ ^ 2 + (q.2 - p₀.2) ^ 2) ^ 2 := by gcongr
    _ = spaceTimeQuartic p₀ q := rfl

end ParabolicBasic
