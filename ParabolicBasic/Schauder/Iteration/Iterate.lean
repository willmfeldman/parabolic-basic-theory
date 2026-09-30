/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Iteration.Step

/-!
# The iteration and the limit polynomial

Degree-generic form: the normalization of the iteration ((N≤1) for `k ≤ 1`: `P₀ = 0`, `σ = 0`,
`θ = 0`; (N₂) for `k = 2`: `P₀ = (0, 0, H 0, 0)`, `σ = H 0`, `θ = α`) is expressed by a starting
polynomial `P₀` of degree `≤ k` with `src P₀ = σ` and `|u − P₀| ≤ 1` on `Q₁`, and a source bound
`|H q − σ| ≤ δ₀ pdist(q, 0)^θ` with `θ ≥ 0`, `θ ≥ k + α − 2`.

* `iterate_step`: one step of the iteration at scale `ρⁿ`, via `isHeatSolOn_rescale` and
  `improvement_of_flatness`.
* `exists_limit_poly`: the increments `Rₙ = (Qₙ)_{ρ^{-n}, ρ^{-n(k+α)}}` are geometrically
  small, so the coefficients converge; the limit `P∞` satisfies `|Pₙ − P∞| ≤ C₁ ρ^{n(k+α)}` on
  `cCyl 0 0 ρⁿ`.
* `abs_le_of_forall_scale`: bounds at the scales `ρⁿ` give a bound at every scale.
* `expansion_at_origin`: the assembled iteration.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff RealInnerProductSpace

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Coefficient and evaluation bounds for caloric polynomials -/

namespace CaloricPoly

theorem abs_a_le_coeffNorm (P : CaloricPoly d) : |P.a| ≤ P.coeffNorm := by
  have : 0 ≤ ∑ i, ∑ j, |P.M i j| := by positivity
  unfold coeffNorm; linarith [norm_nonneg P.b, abs_nonneg P.c]

theorem norm_b_le_coeffNorm (P : CaloricPoly d) : ‖P.b‖ ≤ P.coeffNorm := by
  have : 0 ≤ ∑ i, ∑ j, |P.M i j| := by positivity
  unfold coeffNorm; linarith [abs_nonneg P.a, abs_nonneg P.c]

theorem abs_c_le_coeffNorm (P : CaloricPoly d) : |P.c| ≤ P.coeffNorm := by
  have : 0 ≤ ∑ i, ∑ j, |P.M i j| := by positivity
  unfold coeffNorm; linarith [abs_nonneg P.a, norm_nonneg P.b]

theorem abs_M_le_coeffNorm (P : CaloricPoly d) (i j : Fin d) : |P.M i j| ≤ P.coeffNorm := by
  have h1 : |P.M i j| ≤ ∑ j', |P.M i j'| :=
    Finset.single_le_sum (f := fun j' ↦ |P.M i j'|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', |P.M i j'| ≤ ∑ i', ∑ j', |P.M i' j'| :=
    Finset.single_le_sum (f := fun i' ↦ ∑ j', |P.M i' j'|) (fun _ _ ↦ by positivity)
      (Finset.mem_univ i)
  unfold coeffNorm; linarith [abs_nonneg P.a, norm_nonneg P.b, abs_nonneg P.c]

/-- The crude evaluation bound `|P y| ≤ |a| + ‖b‖ ‖y₁‖ + |c| |y₂| + (∑ |Mᵢⱼ|) ‖y₁‖²`. -/
theorem abs_eval_le (P : CaloricPoly d) (y : E d × ℝ) :
    |P.eval y| ≤ |P.a| + ‖P.b‖ * ‖y.1‖ + |P.c| * |y.2| + (∑ i, ∑ j, |P.M i j|) * ‖y.1‖ ^ 2 := by
  rw [eval_eq_bilin]
  have h1 := abs_real_inner_le_norm P.b y.1
  have h2 : |bilin P.M y.1 y.1| ≤ (∑ i, ∑ j, |P.M i j|) * ‖y.1‖ ^ 2 := by
    calc |bilin P.M y.1 y.1| = ‖bilin P.M y.1 y.1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖bilin P.M‖ * ‖y.1‖ * ‖y.1‖ := (bilin P.M).le_opNorm₂ y.1 y.1
      _ ≤ (∑ i, ∑ j, |P.M i j|) * ‖y.1‖ * ‖y.1‖ := by gcongr; exact norm_bilin_le P.M
      _ = (∑ i, ∑ j, |P.M i j|) * ‖y.1‖ ^ 2 := by ring
  have h3 : |P.c * y.2| = |P.c| * |y.2| := abs_mul _ _
  have h4 : |1 / 2 * bilin P.M y.1 y.1| ≤ |bilin P.M y.1 y.1| := by
    rw [abs_mul]
    have : |(1 / 2 : ℝ)| ≤ 1 := by norm_num [abs_of_pos]
    exact mul_le_of_le_one_left (abs_nonneg _) this
  have e1 := abs_add_le (P.a + ⟪P.b, y.1⟫ + P.c * y.2) (1 / 2 * bilin P.M y.1 y.1)
  have e2 := abs_add_le (P.a + ⟪P.b, y.1⟫) (P.c * y.2)
  have e3 := abs_add_le P.a ⟪P.b, y.1⟫
  linarith

/-- For `P` of degree `≤ k ≤ 2`, `τ ≥ 1`, `‖y₁‖ ≤ τ`, `|y₂| ≤ τ²`: `|P y| ≤ ‖P‖ τ^k`. -/
theorem abs_eval_le_of_isDegLE {P : CaloricPoly d} {k : ℕ} (hP : P.IsDegLE k) (hk : k ≤ 2)
    {τ : ℝ} (hτ : 1 ≤ τ) {y : E d × ℝ} (hy1 : ‖y.1‖ ≤ τ) (hy2 : |y.2| ≤ τ ^ 2) :
    |P.eval y| ≤ P.coeffNorm * τ ^ k := by
  have h := P.abs_eval_le y
  have hS : 0 ≤ ∑ i, ∑ j, |P.M i j| := by positivity
  have e1 : ‖P.b‖ * ‖y.1‖ ≤ ‖P.b‖ * τ := mul_le_mul_of_nonneg_left hy1 (norm_nonneg _)
  have e2 : |P.c| * |y.2| ≤ |P.c| * τ ^ 2 := mul_le_mul_of_nonneg_left hy2 (abs_nonneg _)
  have e3 : (∑ i, ∑ j, |P.M i j|) * ‖y.1‖ ^ 2 ≤ (∑ i, ∑ j, |P.M i j|) * τ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy1 2) hS
  have hτ2 : τ ≤ τ ^ 2 := by nlinarith
  have ha1 : |P.a| ≤ |P.a| * τ := le_mul_of_one_le_right (abs_nonneg _) hτ
  have ha2 : |P.a| ≤ |P.a| * τ ^ 2 :=
    le_mul_of_one_le_right (abs_nonneg _) (by nlinarith)
  have hb2 : ‖P.b‖ * τ ≤ ‖P.b‖ * τ ^ 2 := mul_le_mul_of_nonneg_left hτ2 (norm_nonneg _)
  interval_cases k
  · obtain ⟨hb, hc, hM⟩ := hP
    have hcn : P.coeffNorm = |P.a| := by simp [coeffNorm, hb, hc, hM]
    have hev : P.eval y = P.a := by simp [eval, hb, hc, hM]
    rw [hcn, hev, pow_zero, mul_one]
  · obtain ⟨hc, hM⟩ := hP
    have hcn : P.coeffNorm = |P.a| + ‖P.b‖ := by simp [coeffNorm, hc, hM]
    have hS0 : ∑ i, ∑ j, |P.M i j| = 0 := by simp [hM]
    rw [hcn, pow_one, add_mul]
    rw [hc, hS0, abs_zero, zero_mul, zero_mul, add_zero, add_zero] at h
    linarith
  · have hcn : P.coeffNorm * τ ^ 2 = |P.a| * τ ^ 2 + ‖P.b‖ * τ ^ 2 + |P.c| * τ ^ 2 +
        (∑ i, ∑ j, |P.M i j|) * τ ^ 2 := by rw [coeffNorm]; ring
    rw [hcn]
    linarith

/-- The coefficient norm of a rescaled polynomial. -/
theorem coeffNorm_rescale (P : CaloricPoly d) {r lam : ℝ} (hr : 0 ≤ r) (hlam : 0 < lam) :
    (P.rescale r lam).coeffNorm =
      (|P.a| + r * ‖P.b‖ + r ^ 2 * |P.c| + r ^ 2 * ∑ i, ∑ j, |P.M i j|) / lam := by
  simp only [coeffNorm, rescale_a, rescale_b, rescale_c, rescale_M, Matrix.smul_apply,
    smul_eq_mul, abs_div, abs_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hlam,
    abs_of_nonneg hr, abs_of_nonneg (sq_nonneg r), ← Finset.mul_sum]
  ring

/-- The increment `Q_{r⁻¹, r^{-(k+α)}}` of the iteration has coefficient norm `≤ ‖Q‖ r^α`
(`Q` of degree `≤ k ≤ 2`, `0 < r ≤ 1`). -/
theorem coeffNorm_rescale_inv_le {Q : CaloricPoly d} {k : ℕ} (hQ : Q.IsDegLE k) (hk : k ≤ 2)
    {α r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (Q.rescale r⁻¹ (r ^ ((k : ℝ) + α))⁻¹).coeffNorm ≤ Q.coeffNorm * r ^ α := by
  have hrk : r ^ ((k : ℝ) + α) = r ^ k * r ^ α := by rw [Real.rpow_add hr, Real.rpow_natCast]
  have hra : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have hS : 0 ≤ ∑ i, ∑ j, |Q.M i j| := by positivity
  rw [coeffNorm_rescale Q (inv_nonneg.2 hr.le) (inv_pos.2 (Real.rpow_pos_of_pos hr _)),
    div_inv_eq_mul, hrk, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hra.le
  have hr0 : r ≠ 0 := hr.ne'
  interval_cases k
  · obtain ⟨hb, hc, hM⟩ := hQ
    simp [coeffNorm, hb, hc, hM]
  · obtain ⟨hc, hM⟩ := hQ
    have e : (|Q.a| + r⁻¹ * ‖Q.b‖ + r⁻¹ ^ 2 * |Q.c| + r⁻¹ ^ 2 * ∑ i, ∑ j, |Q.M i j|) * r ^ 1 =
        |Q.a| * r + ‖Q.b‖ := by
      simp only [hc, hM, abs_zero, Matrix.zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
      field_simp
    have hcn : Q.coeffNorm = |Q.a| + ‖Q.b‖ := by simp [coeffNorm, hc, hM]
    rw [e, hcn]
    linarith [mul_le_of_le_one_right (abs_nonneg Q.a) hr1]
  · have e : (|Q.a| + r⁻¹ * ‖Q.b‖ + r⁻¹ ^ 2 * |Q.c| + r⁻¹ ^ 2 * ∑ i, ∑ j, |Q.M i j|) * r ^ 2 =
        |Q.a| * r ^ 2 + ‖Q.b‖ * r + |Q.c| + ∑ i, ∑ j, |Q.M i j| := by
      field_simp
    rw [e, coeffNorm]
    have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
    linarith [mul_le_of_le_one_right (abs_nonneg Q.a) hr2,
      mul_le_of_le_one_right (norm_nonneg Q.b) hr1]

/-- Evaluation bound for the increment: for `0 < r ≤ s`, `‖z₁‖ ≤ s`, `|z₂| ≤ s²`,
`|Q_{r⁻¹, r^{-(k+α)}}(z)| ≤ ‖Q‖ r^α s^k` (`Q` of degree `≤ k ≤ 2`). -/
theorem abs_eval_rescale_inv_le {Q : CaloricPoly d} {k : ℕ} (hQ : Q.IsDegLE k) (hk : k ≤ 2)
    {α r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) {z : E d × ℝ} (hz1 : ‖z.1‖ ≤ s)
    (hz2 : |z.2| ≤ s ^ 2) :
    |(Q.rescale r⁻¹ (r ^ ((k : ℝ) + α))⁻¹).eval z| ≤ Q.coeffNorm * r ^ α * s ^ k := by
  rw [rescale_eval, div_inv_eq_mul]
  obtain ⟨y, hy⟩ : ∃ y : E d × ℝ, y = (r⁻¹ • z.1, r⁻¹ ^ 2 * z.2) := ⟨_, rfl⟩
  rw [← hy]
  have hτ : 1 ≤ s / r := (one_le_div hr).2 hrs
  have hy1 : ‖y.1‖ ≤ s / r := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hz1 hr.le
  have hy2 : |y.2| ≤ (s / r) ^ 2 := by
    rw [hy, abs_mul, abs_pow, abs_inv, abs_of_pos hr, inv_pow, inv_mul_eq_div, div_pow]
    exact div_le_div_of_nonneg_right hz2 (by positivity)
  have hb := abs_eval_le_of_isDegLE hQ hk hτ hy1 hy2
  have hrk : r ^ ((k : ℝ) + α) = r ^ k * r ^ α := by rw [Real.rpow_add hr, Real.rpow_natCast]
  have hrk0 : r ^ k ≠ 0 := pow_ne_zero _ hr.ne'
  have hsr : (s / r) ^ k * r ^ k = s ^ k := by rw [div_pow, div_mul_cancel₀ _ hrk0]
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr _), hrk]
  calc |Q.eval y| * (r ^ k * r ^ α) ≤ Q.coeffNorm * (s / r) ^ k * (r ^ k * r ^ α) := by
        gcongr
    _ = Q.coeffNorm * ((s / r) ^ k * r ^ k) * r ^ α := by ring
    _ = Q.coeffNorm * r ^ α * s ^ k := by rw [hsr]; ring

end CaloricPoly

/-! ### One step of the iteration -/

/-- **Iteration, step.** Suppose improvement of flatness holds at radius `ρ` with source bound
`ρ^γ/4` (`hflat`), `u` solves `dₜu − lapₓu = H` on `Q₁` with `|H q − σ| ≤ ρ^γ/4 pdist(q,0)^θ`,
`θ ≥ max 0 (γ − 2)`, and `P` (with `src P = σ`) approximates `u` to order `(ρⁿ)^γ` on `cCyl 0 0 ρⁿ`.
Then there is `Q` as in `hflat` such that `P + Q_{ρ^{-n}, ρ^{-nγ}}` approximates `u` to order
`(ρ^{n+1})^γ` on `cCyl 0 0 ρ^{n+1}`. -/
theorem iterate_step {k : ℕ} {γ ρ C₀ σ θ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hflat : ∀ {u H : E d × ℝ → ℝ}, ContinuousOn u (closure (cCyl (0 : E d) 0 1)) →
      IsHeatSolOn (cCyl (0 : E d) 0 1) H u → (∀ q ∈ cCyl (0 : E d) 0 1, |u q| ≤ 1) →
      (∀ q ∈ cCyl (0 : E d) 0 1, |H q| ≤ ρ ^ γ / 4) →
      ∃ P : CaloricPoly d, P.src = 0 ∧ P.IsDegLE k ∧ P.coeffNorm ≤ C₀ ∧
        ∀ q ∈ cCyl (0 : E d) 0 ρ, |u q - P.eval q| ≤ ρ ^ γ)
    {u H : E d × ℝ → ℝ} (hu : ContinuousOn u (closure (cCyl (0 : E d) 0 1)))
    (hsol : IsHeatSolOn (cCyl (0 : E d) 0 1) H u) (hθ0 : 0 ≤ θ) (hθ : γ - 2 ≤ θ)
    (hH : ∀ q ∈ cCyl (0 : E d) 0 1, |H q - σ| ≤ ρ ^ γ / 4 * pdist q 0 ^ θ)
    (n : ℕ) {P : CaloricPoly d} (hPsrc : P.src = σ)
    (hP : ∀ q ∈ cCyl (0 : E d) 0 (ρ ^ n), |u q - P.eval q| ≤ (ρ ^ n) ^ γ) :
    ∃ Q : CaloricPoly d, Q.src = 0 ∧ Q.IsDegLE k ∧ Q.coeffNorm ≤ C₀ ∧
      ∀ q ∈ cCyl (0 : E d) 0 (ρ ^ (n + 1)),
        |u q - (P + Q.rescale (ρ ^ n)⁻¹ ((ρ ^ n) ^ γ)⁻¹).eval q| ≤ (ρ ^ (n + 1)) ^ γ := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ρ ^ n := ⟨_, rfl⟩
  rw [← hr] at hP ⊢
  have hr0 : 0 < r := hr ▸ pow_pos hρ0 n
  have hr1 : r ≤ 1 := hr ▸ pow_le_one₀ hρ0.le hρ1
  have hrγ : 0 < r ^ γ := Real.rpow_pos_of_pos hr0 γ
  have hδ : 0 ≤ ρ ^ γ / 4 := by positivity
  have hS0 : parAffine (0 : E d) 0 r 0 = 0 := by simp [parAffine]
  have hpd : ∀ y, pdist (parAffine (0 : E d) 0 r y) 0 = r * pdist y 0 := fun y ↦ by
    have := pdist_parAffine (0 : E d) 0 hr0.le y 0
    rwa [hS0] at this
  have hmaps : ∀ y ∈ cCyl (0 : E d) 0 1, parAffine (0 : E d) 0 r y ∈ cCyl (0 : E d) 0 r := by
    intro y hy
    have h := image_parAffine_cCyl (0 : E d) 0 hr0 1
    rw [mul_one] at h
    exact h ▸ mem_image_of_mem _ hy
  have hQ1 : cCyl (0 : E d) 0 r ⊆ cCyl (0 : E d) 0 1 := cCyl_subset_cCyl hr0.le hr1
  -- the rescaled function `w`
  have hw := isHeatSolOn_rescale (isOpen_cCyl (0 : E d) 0 1) hsol P 0 hr0 hrγ
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, hPsrc] at hw
  have hw' := IsHeatSolOn.mono (isOpen_cCyl (0 : E d) 0 1)
    (fun y hy ↦ (hQ1 (hmaps y hy) : parAffine (0 : E d) 0 r y ∈ cCyl (0 : E d) 0 1)) hw
  have hSc : MapsTo (parAffine (0 : E d) 0 r) (closure (cCyl (0 : E d) 0 1))
      (closure (cCyl (0 : E d) 0 1)) := by
    intro y hy
    have h1 := image_closure_subset_closure_image (continuous_parAffine (0 : E d) 0 r)
      (mem_image_of_mem _ hy)
    refine closure_mono ?_ h1
    rintro _ ⟨y', hy', rfl⟩
    exact hQ1 (hmaps y' hy')
  have hwc : ContinuousOn
      (fun y ↦ (u (parAffine (0 : E d) 0 r y) - P.eval (parAffine (0 : E d) 0 r y)) / r ^ γ)
      (closure (cCyl (0 : E d) 0 1)) :=
    ((hu.comp (continuous_parAffine (0 : E d) 0 r).continuousOn hSc).sub
      (P.continuous_eval.comp (continuous_parAffine (0 : E d) 0 r)).continuousOn).div_const _
  have hw1 : ∀ y ∈ cCyl (0 : E d) 0 1,
      |(u (parAffine (0 : E d) 0 r y) - P.eval (parAffine (0 : E d) 0 r y)) / r ^ γ| ≤ 1 := by
    intro y hy
    rw [abs_div, abs_of_pos hrγ, div_le_one hrγ]
    exact hP _ (hmaps y hy)
  have hwH : ∀ y ∈ cCyl (0 : E d) 0 1,
      |r ^ 2 * (H (parAffine (0 : E d) 0 r y) - σ) / r ^ γ| ≤ ρ ^ γ / 4 := by
    intro y hy
    have hy1 : pdist y 0 < 1 := mem_cCyl_iff.1 hy
    have hb := hH _ (hQ1 (hmaps y hy))
    rw [hpd y] at hb
    have e1 : (r * pdist y 0) ^ θ ≤ r ^ θ := by
      rw [Real.mul_rpow hr0.le (pdist_nonneg _ _)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hr0.le _)
        (Real.rpow_le_one (pdist_nonneg _ _) hy1.le hθ0)
    have e2 : r ^ 2 * r ^ θ / r ^ γ ≤ 1 := by
      rw [← Real.rpow_two, ← Real.rpow_add hr0, ← Real.rpow_sub hr0]
      exact Real.rpow_le_one hr0.le hr1 (by linarith)
    rw [abs_div, abs_mul, abs_of_pos hrγ, abs_of_nonneg (sq_nonneg r)]
    calc r ^ 2 * |H (parAffine (0 : E d) 0 r y) - σ| / r ^ γ
        ≤ r ^ 2 * (ρ ^ γ / 4 * r ^ θ) / r ^ γ := by
          gcongr; exact hb.trans (mul_le_mul_of_nonneg_left e1 hδ)
      _ = ρ ^ γ / 4 * (r ^ 2 * r ^ θ / r ^ γ) := by ring
      _ ≤ ρ ^ γ / 4 * 1 := by gcongr
      _ = ρ ^ γ / 4 := mul_one _
  obtain ⟨Q, hQsrc, hQdeg, hQc, hQap⟩ := hflat hwc hw' hw1 hwH
  refine ⟨Q, hQsrc, hQdeg, hQc, fun z hz ↦ ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : E d × ℝ, y = (r⁻¹ • z.1, r⁻¹ ^ 2 * z.2) := ⟨_, rfl⟩
  have hSy : parAffine (0 : E d) 0 r y = z := by
    refine Prod.ext ?_ ?_
    · change (0 : E d) + r • y.1 = z.1
      rw [hy, zero_add, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    · change (0 : ℝ) + r ^ 2 * y.2 = z.2
      rw [hy, zero_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr0.ne', one_pow, one_mul]
  have hyρ : y ∈ cCyl (0 : E d) 0 ρ := by
    have h1 : pdist z 0 < ρ ^ (n + 1) := mem_cCyl_iff.1 hz
    rw [← hSy, hpd y, pow_succ, ← hr] at h1
    exact mem_cCyl_iff.2 (lt_of_mul_lt_mul_left h1 hr0.le)
  have hQy := hQap y hyρ
  simp only [hSy] at hQy
  have hRz : (Q.rescale r⁻¹ (r ^ γ)⁻¹).eval z = r ^ γ * Q.eval y := by
    rw [CaloricPoly.rescale_eval, ← hy, div_inv_eq_mul, mul_comm (Q.eval y)]
  have hne : r ^ γ ≠ 0 := hrγ.ne'
  have e : u z - (P + Q.rescale r⁻¹ (r ^ γ)⁻¹).eval z =
      r ^ γ * ((u z - P.eval z) / r ^ γ - Q.eval y) := by
    rw [CaloricPoly.eval_add, hRz, mul_sub, mul_div_cancel₀ _ hne]
    ring
  rw [e, abs_mul, abs_of_pos hrγ]
  calc r ^ γ * |(u z - P.eval z) / r ^ γ - Q.eval y| ≤ r ^ γ * ρ ^ γ := by gcongr
    _ = (ρ ^ (n + 1)) ^ γ := by
      rw [pow_succ, Real.mul_rpow (pow_nonneg hρ0.le n) hρ0.le, hr]

/-! ### The limit polynomial -/

/-- **Iteration, limit.** If `P (n+1) = P n + (Q n)_{ρ^{-n}, ρ^{-n(k+α)}}` with `Q n` of degree
`≤ k` and `‖Q n‖ ≤ C₀`, and every `P n` has degree `≤ k` and source `σ`, then the coefficients of
`P n` converge to those of a caloric polynomial `P'` of degree `≤ k` with source `σ`,
`‖P'‖ ≤ ‖P 0‖ + C₀/(1 − ρ^α)`, and `|P n − P'| ≤ C₀/(1 − ρ^α) (ρⁿ)^{k+α}` on `cCyl 0 0 ρⁿ`. -/
theorem exists_limit_poly {k : ℕ} (hk : k ≤ 2) {α ρ C₀ σ : ℝ} (hα : 0 < α) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (P Q : ℕ → CaloricPoly d)
    (hPQ : ∀ n, P (n + 1) = P n + (Q n).rescale (ρ ^ n)⁻¹ ((ρ ^ n) ^ ((k : ℝ) + α))⁻¹)
    (hQdeg : ∀ n, (Q n).IsDegLE k) (hQc : ∀ n, (Q n).coeffNorm ≤ C₀)
    (hPdeg : ∀ n, (P n).IsDegLE k) (hPsrc : ∀ n, (P n).src = σ) :
    ∃ P' : CaloricPoly d, P'.IsDegLE k ∧ P'.src = σ ∧
      P'.coeffNorm ≤ (P 0).coeffNorm + C₀ / (1 - ρ ^ α) ∧
      ∀ n : ℕ, ∀ z ∈ cCyl (0 : E d) 0 (ρ ^ n),
        |(P n).eval z - P'.eval z| ≤ C₀ / (1 - ρ ^ α) * (ρ ^ n) ^ ((k : ℝ) + α) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ρ ^ α := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := hr ▸ Real.rpow_pos_of_pos hρ0 α
  have hr1 : r < 1 := hr ▸ Real.rpow_lt_one hρ0.le hρ1 hα
  have h1r : 0 < 1 - r := by linarith
  have hC₀ : 0 ≤ C₀ := (CaloricPoly.coeffNorm_nonneg _).trans (hQc 0)
  have hC₁ : 0 ≤ C₀ / (1 - r) := div_nonneg hC₀ h1r.le
  have hpow : ∀ n : ℕ, (ρ ^ n) ^ α = r ^ n := fun n ↦ by
    rw [hr, ← Real.rpow_natCast_mul hρ0.le, mul_comm (n : ℝ) α, Real.rpow_mul_natCast hρ0.le]
  obtain ⟨R, hR⟩ : ∃ R : ℕ → CaloricPoly d,
      ∀ n, R n = (Q n).rescale (ρ ^ n)⁻¹ ((ρ ^ n) ^ ((k : ℝ) + α))⁻¹ := ⟨_, fun _ ↦ rfl⟩
  have hPR : ∀ n, P (n + 1) = P n + R n := fun n ↦ by rw [hPQ n, hR n]
  have hRdeg : ∀ n, (R n).IsDegLE k := fun n ↦ by rw [hR n]; exact (hQdeg n).rescale _ _
  have hRc : ∀ n, (R n).coeffNorm ≤ C₀ * r ^ n := fun n ↦ by
    rw [hR n]
    calc _ ≤ (Q n).coeffNorm * (ρ ^ n) ^ α :=
          CaloricPoly.coeffNorm_rescale_inv_le (hQdeg n) hk (pow_pos hρ0 n)
            (pow_le_one₀ hρ0.le hρ1.le)
      _ ≤ C₀ * r ^ n := by
          rw [hpow]; exact mul_le_mul_of_nonneg_right (hQc n) (pow_nonneg hr0.le n)
  -- Cauchy sequences of coefficients
  have hdistR : ∀ (x y : ℝ), dist x (x + y) = |y| := fun x y ↦ by
    rw [Real.dist_eq, abs_sub_comm, add_sub_cancel_left]
  have ha : CauchySeq fun n ↦ (P n).a := cauchySeq_of_le_geometric r C₀ hr1 fun n ↦ by
    rw [hPR n, CaloricPoly.add_a, hdistR]
    exact (R n).abs_a_le_coeffNorm.trans (hRc n)
  have hb : CauchySeq fun n ↦ (P n).b := cauchySeq_of_le_geometric r C₀ hr1 fun n ↦ by
    rw [hPR n, CaloricPoly.add_b, dist_eq_norm, norm_sub_rev, add_sub_cancel_left]
    exact (R n).norm_b_le_coeffNorm.trans (hRc n)
  have hc : CauchySeq fun n ↦ (P n).c := cauchySeq_of_le_geometric r C₀ hr1 fun n ↦ by
    rw [hPR n, CaloricPoly.add_c, hdistR]
    exact (R n).abs_c_le_coeffNorm.trans (hRc n)
  have hM : ∀ i j, CauchySeq fun n ↦ (P n).M i j := fun i j ↦
    cauchySeq_of_le_geometric r C₀ hr1 fun n ↦ by
      rw [hPR n, CaloricPoly.add_M, Matrix.add_apply, hdistR]
      exact ((R n).abs_M_le_coeffNorm i j).trans (hRc n)
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete ha
  obtain ⟨B, hB⟩ := cauchySeq_tendsto_of_complete hb
  obtain ⟨C, hC⟩ := cauchySeq_tendsto_of_complete hc
  choose Ml hMl using fun i j ↦ cauchySeq_tendsto_of_complete (hM i j)
  have hsymm : (Matrix.of Ml).IsSymm := Matrix.IsSymm.ext fun i j ↦ by
    simp only [Matrix.of_apply]
    exact tendsto_nhds_unique (hMl j i)
      ((hMl i j).congr fun n ↦ ((P n).symm.apply i j).symm)
  obtain ⟨P', hPa, hPb, hPc, hPM⟩ : ∃ P' : CaloricPoly d,
      P'.a = A ∧ P'.b = B ∧ P'.c = C ∧ ∀ i j, P'.M i j = Ml i j :=
    ⟨⟨A, B, C, Matrix.of Ml, hsymm⟩, rfl, rfl, rfl, fun _ _ ↦ rfl⟩
  -- convergence of evaluations
  have hev : ∀ z, Tendsto (fun n ↦ (P n).eval z) atTop (𝓝 (P'.eval z)) := by
    intro z
    simp only [CaloricPoly.eval, hPa, hPb, hPc, hPM]
    exact ((hA.add (hB.inner tendsto_const_nhds)).add (hC.mul_const _)).add
      ((tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
        ((hMl i j).mul_const _).mul_const _).const_mul _)
  refine ⟨P', ?_, ?_, ?_, ?_⟩
  · -- degree
    interval_cases k
    · refine ⟨?_, ?_, ?_⟩
      · rw [hPb]
        exact tendsto_nhds_unique hB (tendsto_const_nhds.congr fun n ↦ ((hPdeg n).1).symm)
      · rw [hPc]
        exact tendsto_nhds_unique hC (tendsto_const_nhds.congr fun n ↦ ((hPdeg n).2.1).symm)
      · ext i j
        rw [hPM]
        exact tendsto_nhds_unique (hMl i j)
          (tendsto_const_nhds.congr fun n ↦ by rw [(hPdeg n).2.2])
    · refine ⟨?_, ?_⟩
      · rw [hPc]
        exact tendsto_nhds_unique hC (tendsto_const_nhds.congr fun n ↦ ((hPdeg n).1).symm)
      · ext i j
        rw [hPM]
        exact tendsto_nhds_unique (hMl i j)
          (tendsto_const_nhds.congr fun n ↦ by rw [(hPdeg n).2])
    · trivial
  · -- source
    have h1 : Tendsto (fun n ↦ (P n).src) atTop (𝓝 P'.src) := by
      simp only [CaloricPoly.src, Matrix.trace, Matrix.diag, hPc, hPM]
      exact hC.sub (tendsto_finsetSum _ fun i _ ↦ hMl i i)
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun n ↦ (hPsrc n).symm)
  · -- coefficient norm
    have hcn : ∀ n, (P n).coeffNorm ≤ (P 0).coeffNorm + C₀ / (1 - r) * (1 - r ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hPR n]
        have e : C₀ / (1 - r) * (1 - r ^ n) + C₀ * r ^ n =
            C₀ / (1 - r) * (1 - r ^ (n + 1)) := by
          field_simp
          ring
        calc _ ≤ (P n).coeffNorm + (R n).coeffNorm := CaloricPoly.coeffNorm_add_le _ _
          _ ≤ (P 0).coeffNorm + C₀ / (1 - r) * (1 - r ^ n) + C₀ * r ^ n :=
            add_le_add ih (hRc n)
          _ = _ := by rw [add_assoc, e]
    have hcn' : ∀ n, (P n).coeffNorm ≤ (P 0).coeffNorm + C₀ / (1 - r) := fun n ↦ by
      have : C₀ / (1 - r) * (1 - r ^ n) ≤ C₀ / (1 - r) :=
        mul_le_of_le_one_right hC₁ (by linarith [pow_nonneg hr0.le n])
      linarith [hcn n]
    have hlim : Tendsto (fun n ↦ (P n).coeffNorm) atTop (𝓝 P'.coeffNorm) := by
      simp only [CaloricPoly.coeffNorm, hPa, hPb, hPc, hPM]
      exact ((hA.abs.add hB.norm).add hC.abs).add
        (tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ (hMl i j).abs)
    exact le_of_tendsto' hlim hcn'
  · -- tail bound
    intro n z hz
    have hz1 : ‖z.1‖ ≤ ρ ^ n := by
      have := hz.1
      rw [mem_ball_zero_iff] at this
      exact this.le
    have hz2 : |z.2| ≤ (ρ ^ n) ^ 2 := by
      have h := hz.2
      simp only [mem_Ioo, zero_sub, zero_add] at h
      exact (abs_lt.2 h).le
    have hγn : (ρ ^ n) ^ ((k : ℝ) + α) = (ρ ^ n) ^ k * r ^ n := by
      rw [Real.rpow_add (pow_pos hρ0 n), Real.rpow_natCast, hpow]
    have hv : ∀ j : ℕ, dist ((P (j + n)).eval z) ((P (j + 1 + n)).eval z) ≤
        C₀ * (ρ ^ n) ^ ((k : ℝ) + α) * r ^ j := by
      intro j
      rw [show j + 1 + n = (j + n) + 1 by omega, hPR (j + n), CaloricPoly.eval_add, hdistR,
        hR (j + n)]
      have hle : ρ ^ (j + n) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
      calc _ ≤ (Q (j + n)).coeffNorm * (ρ ^ (j + n)) ^ α * (ρ ^ n) ^ k :=
            CaloricPoly.abs_eval_rescale_inv_le (hQdeg _) hk (pow_pos hρ0 _) hle hz1 hz2
        _ ≤ C₀ * r ^ (j + n) * (ρ ^ n) ^ k := by
            rw [hpow]
            gcongr
            exact hQc _
        _ = C₀ * (ρ ^ n) ^ ((k : ℝ) + α) * r ^ j := by rw [hγn, pow_add]; ring
    have hvlim : Tendsto (fun j ↦ (P (j + n)).eval z) atTop (𝓝 (P'.eval z)) :=
      (tendsto_add_atTop_iff_nat n).2 (hev z)
    have key := dist_le_of_le_geometric_of_tendsto₀ r _ hr1 hv hvlim
    rw [zero_add, Real.dist_eq] at key
    calc _ ≤ C₀ * (ρ ^ n) ^ ((k : ℝ) + α) / (1 - r) := key
      _ = _ := by ring

/-! ### All scales -/

/-- Between two consecutive powers: for `0 < x < 1` and `0 < ρ < 1` there is `m` with
`ρ^{m+1} ≤ x < ρ^m`. -/
theorem exists_pow_succ_le_lt {ρ x : ℝ} (hρ1 : ρ < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ m : ℕ, ρ ^ (m + 1) ≤ x ∧ x < ρ ^ m := by
  classical
  have hex : ∃ n : ℕ, ρ ^ n ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 hρ1
    exact ⟨n, hn.le⟩
  have hn := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := fun h ↦ by
    rw [h, pow_zero] at hn
    linarith
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)]
    exact hn
  · by_contra h
    have := Nat.find_min' hex (not_lt.1 h)
    omega

/-- **Iteration, all scales.** Bounds `|f| ≤ B (ρⁿ)^γ` on `cCyl 0 0 ρⁿ` for every `n` give
`|f q| ≤ B ρ^{-γ} pdist(q, 0)^γ` for `pdist(q, 0) < 1`. -/
theorem abs_le_of_forall_scale {f : E d × ℝ → ℝ} {ρ B γ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : 0 < γ) (hB : 0 ≤ B)
    (h : ∀ n : ℕ, ∀ z ∈ cCyl (0 : E d) 0 (ρ ^ n), |f z| ≤ B * (ρ ^ n) ^ γ) :
    ∀ q : E d × ℝ, pdist q 0 < 1 → |f q| ≤ B / ρ ^ γ * pdist q 0 ^ γ := by
  intro q hq
  have hργ : 0 < ρ ^ γ := Real.rpow_pos_of_pos hρ0 γ
  have hmem : ∀ n : ℕ, pdist q 0 < ρ ^ n → q ∈ cCyl (0 : E d) 0 (ρ ^ n) := fun n hn ↦
    mem_cCyl_iff.2 hn
  rcases (pdist_nonneg q 0).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hγ.ne', mul_zero]
    have hlim : Tendsto (fun n : ℕ ↦ B * (ρ ^ γ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hργ.le
        (Real.rpow_lt_one hρ0.le hρ1 hγ)).const_mul B
    refine ge_of_tendsto' hlim fun n ↦ ?_
    have := h n q (hmem n (by rw [← h0]; positivity))
    rwa [← Real.rpow_natCast_mul hρ0.le, mul_comm (n : ℝ) γ, Real.rpow_mul_natCast hρ0.le]
      at this
  · obtain ⟨m, hm1, hm2⟩ := exists_pow_succ_le_lt hρ1 hpos hq
    calc |f q| ≤ B * (ρ ^ m) ^ γ := h m q (hmem m hm2)
      _ = B / ρ ^ γ * (ρ ^ (m + 1)) ^ γ := by
        rw [pow_succ, Real.mul_rpow (pow_nonneg hρ0.le m) hρ0.le, div_mul_eq_mul_div,
          mul_div_assoc, mul_div_cancel_right₀ _ hργ.ne']
      _ ≤ B / ρ ^ γ * pdist q 0 ^ γ := by
        gcongr

/-! ### The assembled iteration -/

/-- **Iteration: expansion at the origin.** For `k ≤ 2` and `α ∈ (0, 1)` there are `δ₀ > 0`,
`C₁ ≥ 0`, `A ≥ 0` (depending only on `d`, `α`, `k`) such that: if `u` is continuous on `closure Q₁`
and solves `dₜu − lapₓu = H` on `Q₁`, `P₀` has degree `≤ k` and `src P₀ = σ`, `|u − P₀| ≤ 1` on
`Q₁`, and `|H q − σ| ≤ δ₀ pdist(q, 0)^θ` on `Q₁` with `θ ≥ 0`, `θ ≥ k + α − 2`, then there is a
caloric polynomial `P` of degree `≤ k` with `src P = σ`, `coeffNorm P ≤ coeffNorm P₀ + C₁` and
`|u q − P q| ≤ A pdist(q, 0)^{k+α}` for `pdist(q, 0) < 1`. -/
theorem expansion_at_origin (k : ℕ) (hk : k ≤ 2) {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ δ₀ C₁ A : ℝ, 0 < δ₀ ∧ 0 ≤ C₁ ∧ 0 ≤ A ∧ ∀ {u H : E d × ℝ → ℝ} {σ θ : ℝ}
      {P₀ : CaloricPoly d},
      ContinuousOn u (closure (cCyl (0 : E d) 0 1)) → IsHeatSolOn (cCyl (0 : E d) 0 1) H u →
      P₀.IsDegLE k → P₀.src = σ → (∀ q ∈ cCyl (0 : E d) 0 1, |u q - P₀.eval q| ≤ 1) →
      0 ≤ θ → (k : ℝ) + α - 2 ≤ θ →
      (∀ q ∈ cCyl (0 : E d) 0 1, |H q - σ| ≤ δ₀ * pdist q 0 ^ θ) →
      ∃ P : CaloricPoly d, P.IsDegLE k ∧ P.src = σ ∧ P.coeffNorm ≤ P₀.coeffNorm + C₁ ∧
        ∀ q : E d × ℝ, pdist q 0 < 1 → |u q - P.eval q| ≤ A * pdist q 0 ^ ((k : ℝ) + α) := by
  obtain ⟨ρ, C₀, hρ0, hρhalf, hC₀, hflat⟩ := improvement_of_flatness (d := d) hα
  have hρ1 : ρ < 1 := by linarith
  have hρα1 : ρ ^ α < 1 := Real.rpow_lt_one hρ0.le hρ1 hα.1
  have h1r : 0 < 1 - ρ ^ α := by linarith
  have hγ0 : 0 < (k : ℝ) + α := add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) hα.1
  have hργ : 0 < ρ ^ ((k : ℝ) + α) := Real.rpow_pos_of_pos hρ0 _
  have hC₁ : 0 ≤ C₀ / (1 - ρ ^ α) := div_nonneg hC₀ h1r.le
  refine ⟨ρ ^ ((k : ℝ) + α) / 4, C₀ / (1 - ρ ^ α), (1 + C₀ / (1 - ρ ^ α)) / ρ ^ ((k : ℝ) + α),
    by positivity, hC₁, div_nonneg (by linarith) hργ.le, ?_⟩
  intro u H σ θ P₀ hu hsol hP₀ hσ hu₀ hθ0 hθ hH
  have : Nonempty (CaloricPoly d) := ⟨0⟩
  have hstep : ∀ (n : ℕ) (P : CaloricPoly d), (P.IsDegLE k ∧ P.src = σ ∧
      ∀ q ∈ cCyl (0 : E d) 0 (ρ ^ n), |u q - P.eval q| ≤ (ρ ^ n) ^ ((k : ℝ) + α)) →
      ∃ Q : CaloricPoly d, Q.src = 0 ∧ Q.IsDegLE k ∧ Q.coeffNorm ≤ C₀ ∧
        ∀ q ∈ cCyl (0 : E d) 0 (ρ ^ (n + 1)),
          |u q - (P + Q.rescale (ρ ^ n)⁻¹ ((ρ ^ n) ^ ((k : ℝ) + α))⁻¹).eval q| ≤
            (ρ ^ (n + 1)) ^ ((k : ℝ) + α) :=
    fun n P hP ↦ iterate_step hρ0 hρ1.le (hflat k hk) hu hsol hθ0 hθ hH n hP.2.1 hP.2.2
  choose! Qf hQf using hstep
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → CaloricPoly d, seq 0 = P₀ ∧ ∀ n,
      seq (n + 1) = seq n + (Qf n (seq n)).rescale (ρ ^ n)⁻¹ ((ρ ^ n) ^ ((k : ℝ) + α))⁻¹ :=
    ⟨fun n ↦ Nat.rec P₀
      (fun n P ↦ P + (Qf n P).rescale (ρ ^ n)⁻¹ ((ρ ^ n) ^ ((k : ℝ) + α))⁻¹) n,
      rfl, fun _ ↦ rfl⟩
  have hI : ∀ n, (seq n).IsDegLE k ∧ (seq n).src = σ ∧
      ∀ q ∈ cCyl (0 : E d) 0 (ρ ^ n), |u q - (seq n).eval q| ≤ (ρ ^ n) ^ ((k : ℝ) + α) := by
    intro n
    induction n with
    | zero =>
      rw [hseq0]
      refine ⟨hP₀, hσ, fun q hq ↦ ?_⟩
      rw [pow_zero, Real.one_rpow]
      exact hu₀ q (by simpa using hq)
    | succ n ih =>
      obtain ⟨hQs, hQd, -, hQb⟩ := hQf n (seq n) ih
      refine ⟨?_, ?_, ?_⟩
      · rw [hseqs]; exact ih.1.add (hQd.rescale _ _)
      · rw [hseqs, CaloricPoly.src_add, CaloricPoly.src_rescale, hQs, ih.2.1]; simp
      · rw [hseqs]; exact hQb
  obtain ⟨P', hP'deg, hP'src, hP'c, hP'tail⟩ := exists_limit_poly hk hα.1 hρ0 hρ1 seq
    (fun n ↦ Qf n (seq n)) hseqs (fun n ↦ (hQf n _ (hI n)).2.1)
    (fun n ↦ (hQf n _ (hI n)).2.2.1) (fun n ↦ (hI n).1) (fun n ↦ (hI n).2.1)
  refine ⟨P', hP'deg, hP'src, by rwa [hseq0] at hP'c, ?_⟩
  have hall : ∀ n : ℕ, ∀ z ∈ cCyl (0 : E d) 0 (ρ ^ n),
      |u z - P'.eval z| ≤ (1 + C₀ / (1 - ρ ^ α)) * (ρ ^ n) ^ ((k : ℝ) + α) := by
    intro n z hz
    have a := (hI n).2.2 z hz
    have b := hP'tail n z hz
    calc |u z - P'.eval z| ≤ |u z - (seq n).eval z| + |(seq n).eval z - P'.eval z| :=
          abs_sub_le _ _ _
      _ ≤ _ := by rw [add_mul, one_mul]; exact add_le_add a b
  exact abs_le_of_forall_scale hρ0 hρ1 hγ0 (by linarith) hall

end ParabolicBasic
