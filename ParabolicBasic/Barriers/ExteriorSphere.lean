/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The pointwise exterior sphere condition

* `ExteriorSphereAt V ξ`: some closed ball `closedBall y R`, `R > 0`, meets `closure V` exactly at
  `ξ`.
* `exteriorSphereAt_ball`: balls have an exterior sphere at every frontier point, with
  `y = x₀ + 2 (ξ - x₀)`, `R = ρ`.
* `exteriorSphereAt_of_hasC2Boundary`: domains with `C²` boundary have an exterior sphere at every
  frontier point (pointwise only; no uniform radius is needed).
* `pos_of_mem_frontier`: a set with a frontier point lives in dimension `d ≥ 1` (`E 0` is a point).
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace Gradient

namespace ParabolicBasic

variable {d : ℕ}

/-- `V` has an exterior sphere at `ξ`: there are `y` and `R > 0` with
`‖ξ - y‖ = R` and `‖x - y‖ > R` for every `x ∈ closure V`, `x ≠ ξ`. -/
def ExteriorSphereAt (V : Set (E d)) (ξ : E d) : Prop :=
  ∃ y : E d, ∃ R > 0, dist ξ y = R ∧ ∀ x ∈ closure V, x ≠ ξ → R < dist x y

/-- `E 0` is a point. -/
theorem eq_zero_of_dim_zero (x : E 0) : x = 0 := by
  rw [← norm_eq_zero, EuclideanSpace.norm_eq]
  simp

/-- A set with a frontier point lives in dimension `d ≥ 1`: in `E 0` every set is `∅` or `univ`. -/
theorem pos_of_mem_frontier {V : Set (E d)} {ξ : E d} (hξ : ξ ∈ frontier V) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · exfalso
    rcases V.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp at hξ
    · have : V = univ := eq_univ_of_forall fun x ↦ by
        rwa [eq_zero_of_dim_zero x, ← eq_zero_of_dim_zero v]
      simp [this] at hξ
  · exact h

/-- `‖u - 2 v‖² = 2 ‖u - v‖² - ‖u‖² + 2 ‖v‖²` (parallelogram-type identity behind
`exteriorSphereAt_ball`). -/
theorem norm_sub_two_smul_sq (u v : E d) :
    ‖u - (2 : ℝ) • v‖ ^ 2 = 2 * ‖u - v‖ ^ 2 - ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul]
  norm_num
  ring

/-- A ball has an exterior sphere at each frontier point `ξ`, with centre
`x₀ + 2 (ξ - x₀)` and radius `ρ`: for `x ∈ closedBall x₀ ρ`,
`‖x - y‖² - ρ² = 2 ‖x - ξ‖² + (ρ² - ‖x - x₀‖²)`, which is `> 0` unless `x = ξ`. -/
theorem exteriorSphereAt_ball (x₀ : E d) {ρ : ℝ} {ξ : E d} (hξ : ξ ∈ frontier (ball x₀ ρ)) :
    ExteriorSphereAt (ball x₀ ρ) ξ := by
  have hρ : 0 < ρ := nonempty_ball.1 (closure_nonempty_iff.1 ⟨ξ, frontier_subset_closure hξ⟩)
  have hξρ : ‖ξ - x₀‖ = ρ := by
    rw [isOpen_ball.frontier_eq] at hξ
    have h1 : dist ξ x₀ ≤ ρ := closure_ball_subset_closedBall hξ.1
    have h2 : ¬ dist ξ x₀ < ρ := hξ.2
    rw [← dist_eq_norm]
    linarith [not_lt.1 h2]
  refine ⟨x₀ + (2 : ℝ) • (ξ - x₀), ρ, hρ, ?_, fun x hx hxξ ↦ ?_⟩
  · rw [dist_eq_norm, show ξ - (x₀ + (2 : ℝ) • (ξ - x₀)) = -(ξ - x₀) by module, norm_neg, hξρ]
  · have hxρ : ‖x - x₀‖ ≤ ρ := by
      rw [← dist_eq_norm]; exact closure_ball_subset_closedBall hx
    have hpos : 0 < ‖x - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 hxξ)
    have key := norm_sub_two_smul_sq (x - x₀) (ξ - x₀)
    rw [show x - x₀ - (ξ - x₀) = x - ξ by abel, hξρ,
      show x - x₀ - (2 : ℝ) • (ξ - x₀) = x - (x₀ + (2 : ℝ) • (ξ - x₀)) by module] at key
    rw [dist_eq_norm]
    have hn := norm_nonneg (x - (x₀ + (2 : ℝ) • (ξ - x₀)))
    have hx0 := norm_nonneg (x - x₀)
    nlinarith

/-- **Taylor step.** If `φ` is `C²`, then near `ξ`,
`φ x ≥ φ ξ + ⟪∇φ ξ, x - ξ⟫ - K ‖x - ξ‖²` for some `K ≥ 0` (a Lipschitz constant of `Dφ` near `ξ`;
mean value inequality for `x ↦ φ x - Dφ(ξ)(x - ξ)` on `closedBall ξ ‖x - ξ‖`). -/
theorem exists_taylor_lower_bound {φ : E d → ℝ} (hφ : ContDiff ℝ 2 φ) (ξ : E d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ r > 0, ∀ x, ‖x - ξ‖ < r →
      φ ξ + ⟪∇ φ ξ, x - ξ⟫ - K * ‖x - ξ‖ ^ 2 ≤ φ x := by
  have hfd : ∀ v, fderiv ℝ φ ξ v = ⟪∇ φ ξ, v⟫ := fun v ↦ by
    simp only [gradient, InnerProductSpace.toDual_symm_apply]
  obtain ⟨K, t, ht, hK⟩ :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).contDiffAt (x := ξ)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨K, K.2, r, hr, fun x hx ↦ ?_⟩
  set s := closedBall ξ ‖x - ξ‖ with hs
  have hsub : s ⊆ t := fun z hz ↦ hrt (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) hx))
  have hξs : ξ ∈ s := mem_closedBall_self (norm_nonneg _)
  have hxs : x ∈ s := mem_closedBall.2 (dist_eq_norm x ξ).le
  have hderiv : ∀ z ∈ s, HasFDerivWithinAt (fun z ↦ φ z - fderiv ℝ φ ξ (z - ξ))
      (fderiv ℝ φ z - fderiv ℝ φ ξ) s z := by
    intro z _
    have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
      (hφ.differentiable (by norm_num) z).hasFDerivAt
    have h2 : HasFDerivAt (fun z ↦ fderiv ℝ φ ξ (z - ξ)) (fderiv ℝ φ ξ) z := by
      have := (fderiv ℝ φ ξ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const ξ)
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    exact (h1.sub h2).hasFDerivWithinAt
  have hbound : ∀ z ∈ s, ‖fderiv ℝ φ z - fderiv ℝ φ ξ‖ ≤ K * ‖x - ξ‖ := by
    intro z hz
    have := hK.dist_le_mul z (hsub hz) ξ (hsub hξs)
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact mem_closedBall.1 hz) K.2)
  have hmv := (convex_closedBall ξ ‖x - ξ‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hbound hξs hxs
  simp only [sub_self, hfd, inner_zero_right, sub_zero, Real.norm_eq_abs] at hmv
  have := (abs_le.1 hmv).1
  nlinarith

/-- A domain with `C²` boundary has an exterior sphere at every
frontier point (pointwise only). With `g = ∇φ ξ ≠ 0`, `K`, `r` from
`exists_taylor_lower_bound`, `R = min (r / 4) (‖g‖ / (4K + 1))` and `y = ξ + (R / ‖g‖) g`:
for `x ∈ closedBall y R`, `⟪g, x - ξ⟫ ≥ ‖g‖ ‖x - ξ‖² / (2R)`, so
`φ x ≥ ‖x - ξ‖² (‖g‖ / (2R) - K) > 0` unless `x = ξ`; hence `x ∉ closure U`. -/
theorem exteriorSphereAt_of_hasC2Boundary {U : Set (E d)} (hC2 : HasC2Boundary U) {ξ : E d}
    (hξ : ξ ∈ frontier U) : ExteriorSphereAt U ξ := by
  obtain ⟨φ, hφ, hU, hgrad⟩ := hC2
  have hgpos : 0 < ‖∇ φ ξ‖ := norm_pos_iff.2 (hgrad ξ hξ)
  have hφc : Continuous φ := hφ.continuous
  have hUo : IsOpen U := hU ▸ isOpen_lt hφc continuous_const
  have hφξ : 0 ≤ φ ξ := by
    have h : ξ ∉ U := by rw [hUo.frontier_eq] at hξ; exact hξ.2
    rw [hU, mem_ofPred_eq, not_lt] at h
    exact h
  have hcl : ∀ x ∈ closure U, φ x ≤ 0 := fun x hx ↦ by
    rw [hU] at hx
    exact closure_lt_subset_le hφc continuous_const hx
  obtain ⟨K, hK0, r, hr, htaylor⟩ := exists_taylor_lower_bound hφ ξ
  set G := ‖∇ φ ξ‖ with hG
  set R := min (r / 4) (G / (4 * K + 1)) with hRdef
  have hRpos : 0 < R := lt_min (by positivity) (by positivity)
  have hRr : R ≤ r / 4 := min_le_left _ _
  have hRg : R * (4 * K + 1) ≤ G := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hnorm : ‖(R / G) • ∇ φ ξ‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← hG,
      div_mul_cancel₀ _ hgpos.ne']
  have hξy : dist ξ (ξ + (R / G) • ∇ φ ξ) = R := by
    rw [dist_eq_norm, show ξ - (ξ + (R / G) • ∇ φ ξ) = -((R / G) • ∇ φ ξ) by abel, norm_neg,
      hnorm]
  refine ⟨ξ + (R / G) • ∇ φ ξ, R, hRpos, hξy, fun x hx hxξ ↦ ?_⟩
  by_contra hle
  rw [not_lt] at hle
  have hn : 0 < ‖x - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 hxξ)
  have hxy : x - (ξ + (R / G) • ∇ φ ξ) = (x - ξ) - (R / G) • ∇ φ ξ := by abel
  have hexp : ‖(x - ξ) - (R / G) • ∇ φ ξ‖ ^ 2 =
      ‖x - ξ‖ ^ 2 - 2 * ((R / G) * ⟪x - ξ, ∇ φ ξ⟫) + R ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, hnorm]
  have hle2 : ‖(x - ξ) - (R / G) • ∇ φ ξ‖ ^ 2 ≤ R ^ 2 := by
    rw [← hxy, ← dist_eq_norm]
    exact pow_le_pow_left₀ dist_nonneg hle 2
  have hI : ‖x - ξ‖ ^ 2 * G ≤ 2 * R * ⟪∇ φ ξ, x - ξ⟫ := by
    rw [real_inner_comm]
    have h1 : ‖x - ξ‖ ^ 2 ≤ 2 * (R / G) * ⟪x - ξ, ∇ φ ξ⟫ := by nlinarith
    calc ‖x - ξ‖ ^ 2 * G ≤ 2 * (R / G) * ⟪x - ξ, ∇ φ ξ⟫ * G :=
          mul_le_mul_of_nonneg_right h1 hgpos.le
      _ = 2 * R * ⟪x - ξ, ∇ φ ξ⟫ := by field_simp
  have hur : ‖x - ξ‖ < r := by
    have h1 : ‖x - ξ‖ ≤ dist x (ξ + (R / G) • ∇ φ ξ) + dist (ξ + (R / G) • ∇ φ ξ) ξ := by
      rw [← dist_eq_norm]; exact dist_triangle _ _ _
    rw [dist_comm _ ξ, hξy] at h1
    linarith
  have hT := htaylor x hur
  have h3 : ‖x - ξ‖ ^ 2 * (R * (4 * K + 1)) ≤ 2 * R * ⟪∇ φ ξ, x - ξ⟫ :=
    (mul_le_mul_of_nonneg_left hRg (sq_nonneg _)).trans hI
  have h4 : ‖x - ξ‖ ^ 2 * (4 * K + 1) ≤ 2 * ⟪∇ φ ξ, x - ξ⟫ := by
    have : R * (‖x - ξ‖ ^ 2 * (4 * K + 1)) ≤ R * (2 * ⟪∇ φ ξ, x - ξ⟫) := by linarith
    exact le_of_mul_le_mul_left this hRpos
  have hKn : 0 ≤ K * ‖x - ξ‖ ^ 2 := by positivity
  have hn2 : 0 < ‖x - ξ‖ ^ 2 := by positivity
  linarith [hcl x hx]

end ParabolicBasic
