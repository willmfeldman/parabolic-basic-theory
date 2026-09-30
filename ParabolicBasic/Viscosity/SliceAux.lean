/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Calculus.Slice
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The quartic strictifier of the stability lemma

The one computation of the strictification in the stability lemma: the quartic
`q ↦ ‖q.1 - x‖⁴ + (q.2 - t)⁴` has vanishing `dₜ` and `lapₓ` at `(x, t)`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace ParabolicBasic

namespace ViscAux

variable {d : ℕ}

/-! ### The quartic strictifier -/

section Quartic

/-- The Laplacian of `y ↦ ‖y - x‖⁴` vanishes at `x`. -/
theorem laplacian_norm_sub_sq_sq (x : E d) : Δ (fun y : E d ↦ (‖y - x‖ ^ 2) ^ 2) x = 0 := by
  set g : E d → ℝ := fun y ↦ ‖y - x‖ ^ 2 with hg_def
  have hg : ContDiff ℝ 2 g := (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hgd : Differentiable ℝ g := hg.differentiable two_ne_zero
  have hgx : g x = 0 := by simp [g]
  have hDgx : fderiv ℝ g x = 0 := by
    apply IsLocalMin.fderiv_eq_zero
    exact Filter.Eventually.of_forall fun y ↦ by rw [hgx]; positivity
  have hG : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hf : fderiv ℝ (fun y ↦ g y ^ 2) = fun y ↦ g y • fderiv ℝ g y + g y • fderiv ℝ g y := by
    funext y
    have := (hgd y).hasFDerivAt.fun_mul (hgd y).hasFDerivAt
    simp only [← sq] at this
    exact this.fderiv
  have hff : HasFDerivAt (fderiv ℝ (fun y ↦ g y ^ 2)) (0 : E d →L[ℝ] E d →L[ℝ] ℝ) x := by
    rw [hf]
    have h1 := (hgd x).hasFDerivAt.fun_smul (hG x).hasFDerivAt
    convert h1.add h1 using 1
    simp [hgx, hDgx]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply, hff.fderiv]
  simp

/-- The quartic strictifier `σ_p q = ‖q.1 - p.1‖⁴ + (q.2 - p.2)⁴` (with the Euclidean norm on the
space factor, not the sup norm of the product, which is not `C²`). -/
noncomputable def quartic (p : E d × ℝ) (q : E d × ℝ) : ℝ :=
  (‖q.1 - p.1‖ ^ 2) ^ 2 + (q.2 - p.2) ^ 4

theorem contDiff_quartic {n : WithTop ℕ∞} (p : E d × ℝ) : ContDiff ℝ n (quartic p) :=
  (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)).pow 2).add
    ((contDiff_snd.sub contDiff_const).pow 4)

@[simp] theorem quartic_self (p : E d × ℝ) : quartic p p = 0 := by
  simp [quartic]

theorem quartic_nonneg (p q : E d × ℝ) : 0 ≤ quartic p q := by
  unfold quartic; positivity

theorem dist_pow_four_le_quartic (p q : E d × ℝ) : dist q p ^ 4 ≤ quartic p q := by
  rw [Prod.dist_eq]
  unfold quartic
  rcases le_total (dist q.1 p.1) (dist q.2 p.2) with h | h
  · rw [max_eq_right h, Real.dist_eq]
    have : |q.2 - p.2| ^ 4 = (q.2 - p.2) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    rw [this]
    have : 0 ≤ (‖q.1 - p.1‖ ^ 2) ^ 2 := by positivity
    linarith
  · rw [max_eq_left h, dist_eq_norm, ← pow_mul]
    have : 0 ≤ (q.2 - p.2) ^ 4 := by positivity
    norm_num
    linarith

theorem dₜ_quartic (p : E d × ℝ) : dₜ (quartic p) p = 0 := by
  have h : HasDerivAt (fun s : ℝ ↦ (‖p.1 - p.1‖ ^ 2) ^ 2 + (s - p.2) ^ 4)
      (0 + 4 * (p.2 - p.2) ^ 3 * 1) p.2 := by
    refine (hasDerivAt_const _ _).add ?_
    have h4 : HasDerivAt (fun s : ℝ ↦ (s - p.2) ^ 4) _ p.2 :=
      ((hasDerivAt_id p.2).sub_const p.2).pow 4
    simpa using h4
  simp only [dₜ, quartic]
  rw [h.deriv]
  simp

theorem lapₓ_quartic (p : E d × ℝ) : lapₓ (quartic p) p = 0 := by
  have : (fun y : E d ↦ quartic p (y, p.2)) = fun y ↦ (‖y - p.1‖ ^ 2) ^ 2 := by
    funext y; simp [quartic]
  simp only [lapₓ]
  rw [this, laplacian_norm_sub_sq_sq]

end Quartic

end ViscAux

end ParabolicBasic
