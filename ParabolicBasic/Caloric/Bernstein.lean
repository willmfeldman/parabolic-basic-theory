/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Caloric.BernsteinBasic
public import ParabolicBasic.Classical.MaxPrinciple
public import ParabolicBasic.Classical.ToViscosity

/-!
# Bernstein interior estimates for smooth caloric functions

* `IsSmoothCaloricOn.sum_sq_partialDeriv_le` / `abs_partialDeriv_space_le` /
  `IsSmoothCaloricOn.norm_gradₓ_le`: if `v` is smooth caloric on an open `O ⊇ closedParCyl x₀ t₀ r`
  and `|v| ≤ M` there, then `|∇ₓ v(x₀, t₀)| ≤ C M / r`, with `C = C(d)`.
* `IsSmoothCaloricOn.abs_iterPartial_le`: for every word `w` of partials,
  `|∂^w v(x₀, t₀)| ≤ C(d, w) M / r ^ parOrder w`.

## Proof of the gradient bound

By the parabolic rescaling `parAffine x₀ t₀ r` we may take `(x₀, t₀) = 0`, `r = 1`. Let `ζ` be a
fixed smooth bump on space-time, `ζ = 1` near `0`, supported in the (sup-metric) unit ball, so
`ζ = 0` on the parabolic boundary of `B₁ × (-1, 0)`. With `H := ∂ₜ - Δₓ` (in partials, `heatP`),
`K ≥ H(ζ²) + 8|∇ₓζ|²` on the closed cylinder (compactness) and `A := K/2`, the Bernstein function
`w := ζ²|∇ₓv|² + A v²` satisfies `Hw ≤ 0` (product rule, `H ∂ᵢv = 0`, and
`8ab ≤ 2a² + 8b²` on the cross term), so the classical maximum principle
(`comparison_classical_cyl_sub_of_continuousOn`) gives `|∇ₓ v(0)|² ≤ w(0) ≤ A M²`. No explicit
cutoff calculus is needed: only the existence of `K` (the constant is not made explicit).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### The cutoff -/

/-- The fixed space-time bump of the Bernstein argument: `1` on the sup-ball of radius `1/2`,
`0` outside the sup-ball of radius `1`. -/
noncomputable def bernsteinBump (d : ℕ) : ContDiffBump (0 : E d × ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The Bernstein cutoff `ζ`. -/
noncomputable def bernsteinCutoff (d : ℕ) : E d × ℝ → ℝ := bernsteinBump d

theorem contDiff_bernsteinCutoff : ContDiff ℝ ∞ (bernsteinCutoff d) :=
  (bernsteinBump d).contDiff

theorem bernsteinCutoff_zero : bernsteinCutoff d 0 = 1 :=
  (bernsteinBump d).one_of_mem_closedBall (mem_closedBall_self (by norm_num [bernsteinBump]))

theorem bernsteinCutoff_eq_zero {q : E d × ℝ} (hq : 1 ≤ ‖q‖) : bernsteinCutoff d q = 0 :=
  (bernsteinBump d).zero_of_le_dist (by simpa [bernsteinBump] using hq)

/-! ### An algebraic inequality (the cross-term absorption) -/

/-- The pointwise inequality behind `H w ≤ 0`: with `ζ` the cutoff value, `a = ∇ₓζ`, `b = ∇ₓv`,
`D = D²ₓv` (`D i k = ∂ᵢ∂ₖ v`), `hZ = H(ζ²)`, and `hZ + 8|a|² ≤ 2A`. -/
theorem bernstein_algebra (ζ hZ A : ℝ) (a b : Fin d → ℝ) (D : Fin d → Fin d → ℝ)
    (hA : hZ + 8 * ∑ i, a i ^ 2 ≤ 2 * A) :
    ζ * ζ * ∑ k, (-2 * ∑ i, D i k ^ 2) + (∑ k, b k ^ 2) * hZ -
        2 * ∑ i, (2 * ζ * a i) * (∑ k, 2 * b k * D i k) + A * (-2 * ∑ k, b k ^ 2) ≤ 0 := by
  have hcross : -(2 * ∑ i, (2 * ζ * a i) * (∑ k, 2 * b k * D i k)) ≤
      ∑ i, ∑ k, (2 * ζ ^ 2 * D i k ^ 2 + 8 * a i ^ 2 * b k ^ 2) := by
    rw [← neg_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    nlinarith [sq_nonneg (ζ * D i k + 2 * a i * b k)]
  have hsplit : ∑ i, ∑ k, (2 * ζ ^ 2 * D i k ^ 2 + 8 * a i ^ 2 * b k ^ 2) =
      2 * ζ ^ 2 * ∑ k, ∑ i, D i k ^ 2 + 8 * (∑ i, a i ^ 2) * ∑ k, b k ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hG : 0 ≤ ∑ k, b k ^ 2 := Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  have h1 : ζ * ζ * ∑ k, (-2 * ∑ i, D i k ^ 2) = -(2 * ζ ^ 2 * ∑ k, ∑ i, D i k ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [h1]
  rw [hsplit] at hcross
  nlinarith [mul_le_mul_of_nonneg_left hA hG]

/-! ### The gradient bound at unit scale -/

theorem closedParCyl_zero_one : closedParCyl (0 : E d) 0 1 = closedBall 0 1 ×ˢ Icc (-1) 0 := by
  simp only [closedParCyl]; norm_num

private theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

/-- `K` bounds `H(ζ²) + 8|∇ₓζ|²` on the unit closed cylinder (compactness; no cutoff calculus). -/
private theorem exists_cutoff_bound : ∃ K : ℝ, ∀ z ∈ closedParCyl (0 : E d) 0 1,
    heatP (fun y ↦ bernsteinCutoff d y * bernsteinCutoff d y) z +
      8 * ∑ i : Fin d, partialDeriv i.castSucc (bernsteinCutoff d) z ^ 2 ≤ K := by
  have hζ : ContDiffOn ℝ ∞ (bernsteinCutoff d) univ := contDiff_bernsteinCutoff.contDiffOn
  have hZ : ContDiffOn ℝ ∞ (fun y ↦ bernsteinCutoff d y * bernsteinCutoff d y) univ := hζ.mul hζ
  have hp := fun w ↦ (ContDiffOn.iterPartial isOpen_univ hZ w).continuousOn
  have hq := fun w ↦ (ContDiffOn.iterPartial isOpen_univ hζ w).continuousOn
  have hc : ContinuousOn (fun z ↦ heatP (fun y ↦ bernsteinCutoff d y * bernsteinCutoff d y) z +
      8 * ∑ i : Fin d, partialDeriv i.castSucc (bernsteinCutoff d) z ^ 2) univ := by
    refine ContinuousOn.add ?_ ?_
    · exact (hp [Fin.last d]).sub (continuousOn_finsetSum _ fun i _ ↦
        hp [i.castSucc, i.castSucc])
    · exact continuousOn_const.mul (continuousOn_finsetSum _ fun i _ ↦ (hq [i.castSucc]).pow 2)
  obtain ⟨K, hK⟩ := (isCompact_closedParCyl (0 : E d) 0 1).exists_bound_of_continuousOn
    (hc.mono (subset_univ _))
  exact ⟨K, fun z hz ↦ (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK z hz)⟩

/-- The gradient bound at unit scale. -/
private theorem unit_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {M : ℝ},
    IsOpen O → closedParCyl (0 : E d) 0 1 ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ closedParCyl (0 : E d) 0 1, |v q| ≤ M) →
    ∑ i : Fin d, partialDeriv i.castSucc v 0 ^ 2 ≤ A * M ^ 2 := by
  obtain ⟨K, hK⟩ := exists_cutoff_bound (d := d)
  refine ⟨max K 0 / 2, by positivity, fun {v O M} hO hsub hv hM ↦ ?_⟩
  set A : ℝ := max K 0 / 2 with hAdef
  set ζ : E d × ℝ → ℝ := bernsteinCutoff d with hζdef
  set Z : E d × ℝ → ℝ := fun y ↦ ζ y * ζ y with hZdef
  set G : E d × ℝ → ℝ := fun y ↦ ∑ k : Fin d, partialDeriv k.castSucc v y ^ 2 with hGdef
  set w : E d × ℝ → ℝ := fun y ↦ 1 * (Z y * G y) + A * (v y * v y) with hwdef
  have hvs : ContDiffOn ℝ ∞ v O := hv.1
  have hζs : ContDiffOn ℝ ∞ ζ O := contDiff_bernsteinCutoff.contDiffOn
  have hZs : ContDiffOn ℝ ∞ Z O := hζs.mul hζs
  have hDs : ∀ k : Fin d, ContDiffOn ℝ ∞ (partialDeriv k.castSucc v) O := fun k ↦
    contDiffOn_partialDeriv hO hvs _
  have hDDs : ∀ k : Fin d, ContDiffOn ℝ ∞ (fun y ↦ partialDeriv k.castSucc v y ^ 2) O := fun k ↦
    (hDs k).pow 2
  have hGs : ContDiffOn ℝ ∞ G O := ContDiffOn.sum fun k _ ↦ hDDs k
  have hvv : ContDiffOn ℝ ∞ (fun y ↦ v y * v y) O := hvs.mul hvs
  have hZG : ContDiffOn ℝ ∞ (fun y ↦ Z y * G y) O := hZs.mul hGs
  have hws : ContDiffOn ℝ ∞ w O := (contDiffOn_const.mul hZG).add (contDiffOn_const.mul hvv)
  rw [closedParCyl_zero_one] at hsub hM hK
  -- `H w ≤ 0` on the unit cylinder
  have hheat : ∀ z ∈ closedBall (0 : E d) 1 ×ˢ Icc (-1 : ℝ) 0, heatP w z ≤ 0 := by
    intro z hz
    have hzO : z ∈ O := hsub hz
    have hsq : ∀ k : Fin d, (fun y ↦ partialDeriv k.castSucc v y ^ 2) =
        fun y ↦ partialDeriv k.castSucc v y * partialDeriv k.castSucc v y := fun k ↦ by
      funext y; ring
    have hGheat : heatP G z = ∑ k : Fin d,
        (-2 * ∑ i : Fin d, partialDeriv i.castSucc (partialDeriv k.castSucc v) z ^ 2) := by
      rw [hGdef, heatP_finset_sum hO (fun k _ ↦ hDDs k) hzO]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hsq k, heatP_mul hO (hDs k) (hDs k) hzO,
        (hv.partial hO k.castSucc).heatP_eq_zero hO hzO]
      simp only [sq]
      ring
    have hvvheat : heatP (fun y ↦ v y * v y) z = -2 * G z := by
      rw [heatP_mul hO hvs hvs hzO, hv.heatP_eq_zero hO hzO, hGdef]
      simp only [sq]
      ring
    have hdZ : ∀ i : Fin d, partialDeriv i.castSucc Z z =
        2 * ζ z * partialDeriv i.castSucc ζ z := fun i ↦ by
      rw [hZdef, partialDeriv_mul (differentiableAt_of_contDiffOn hO hζs hzO)
        (differentiableAt_of_contDiffOn hO hζs hzO)]
      ring
    have hdG : ∀ i : Fin d, partialDeriv i.castSucc G z = ∑ k : Fin d,
        2 * partialDeriv k.castSucc v z *
          partialDeriv i.castSucc (partialDeriv k.castSucc v) z := fun i ↦ by
      rw [hGdef, partialDeriv_sum (F := fun (k : Fin d) y ↦ partialDeriv k.castSucc v y ^ 2) _
        (fun (k : Fin d) _ ↦
        ((differentiableAt_partialDeriv hO hvs k.castSucc hzO).pow 2))]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hsq k, partialDeriv_mul (differentiableAt_partialDeriv hO hvs k.castSucc hzO)
        (differentiableAt_partialDeriv hO hvs k.castSucc hzO)]
      ring
    have hA : heatP Z z + 8 * ∑ i : Fin d, partialDeriv i.castSucc ζ z ^ 2 ≤ 2 * A := by
      rw [hAdef]
      have := hK z hz
      have := le_max_left K 0
      linarith
    have key := bernstein_algebra (ζ z) (heatP Z z) A (fun i ↦ partialDeriv i.castSucc ζ z)
      (fun k ↦ partialDeriv k.castSucc v z)
      (fun i k ↦ partialDeriv i.castSucc (partialDeriv k.castSucc v) z) hA
    have hw : heatP w z = 1 * (Z z * heatP G z + G z * heatP Z z -
        2 * ∑ i : Fin d, partialDeriv i.castSucc Z z * partialDeriv i.castSucc G z) +
          A * heatP (fun y ↦ v y * v y) z := by
      rw [hwdef, heatP_linear_comb hO hZG hvv 1 A hzO, heatP_mul hO hZs hGs hzO]
    rw [hw, hGheat, hvvheat]
    simp only [hdZ, hdG]
    have hG' : G z = ∑ k : Fin d, partialDeriv k.castSucc v z ^ 2 := rfl
    have hZ' : Z z = ζ z * ζ z := rfl
    rw [hG', hZ', one_mul]
    exact key
  -- the maximum principle on `B₁ × (-1, 0)` against the constant `A M²`
  have hΩO : ball (0 : E d) 1 ×ˢ Ioo (-1 : ℝ) 0 ⊆ O := fun q hq ↦
    hsub ⟨ball_subset_closedBall hq.1, Ioo_subset_Icc_self hq.2⟩
  have hcl : closure (ball (0 : E d) 1) ×ˢ Icc (-1 : ℝ) 0 ⊆ closedBall 0 1 ×ˢ Icc (-1) 0 :=
    prod_mono closure_ball_subset_closedBall subset_rfl
  have hW : IsViscSubOn (ball (0 : E d) 1 ×ˢ Ioo (-1 : ℝ) 0) (fun p _ ↦ (fun _ ↦ (0 : ℝ)) p) w := by
    refine isViscSubOn_of_contDiffOn (isOpen_ball.prod isOpen_Ioo)
      ((hws.of_le two_le_infty).mono hΩO) fun p hp ↦ ?_
    rw [← heatP_eq_dₜ_sub_lapₓ hO (hws.of_le two_le_infty) (hΩO hp), add_zero]
    exact hheat p ⟨ball_subset_closedBall hp.1, Ioo_subset_Icc_self hp.2⟩
  have hbdry : ∀ p ∈ parBdry (ball (0 : E d) 1) (-1) 0, w p ≤ A * M ^ 2 := by
    intro p hp
    have hpc : p ∈ closedBall (0 : E d) 1 ×ˢ Icc (-1 : ℝ) 0 := by
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨closure_ball_subset_closedBall h1, by rw [h2]; norm_num⟩
      · exact ⟨closure_ball_subset_closedBall (frontier_subset_closure h1), h2⟩
    have hnorm : 1 ≤ ‖p‖ := by
      rcases hp with ⟨-, h2⟩ | ⟨h1, -⟩
      · have : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
        rw [mem_singleton_iff.1 h2] at this
        simpa using this
      · have h1' := frontier_ball_subset_sphere h1
        rw [mem_sphere_zero_iff_norm] at h1'
        exact h1' ▸ norm_fst_le p
    have hζ0 : ζ p = 0 := bernsteinCutoff_eq_zero hnorm
    have hMp := abs_le.1 (hM p hpc)
    have : w p = A * (v p * v p) := by simp [hwdef, hZdef, hζ0]
    rw [this]
    have hA0 : 0 ≤ A := by positivity
    exact mul_le_mul_of_nonneg_left (by nlinarith) hA0
  have hcmp := comparison_classical_cyl_sub_of_continuousOn (A := ball (0 : E d) 1)
    (T₀ := -1) (T₁ := 0) (F := fun _ ↦ (0 : ℝ)) (W := w) (b := fun _ ↦ A * M ^ 2)
    isOpen_ball isBounded_ball (by norm_num) hW
    (hws.continuousOn.mono (hcl.trans hsub)) continuousOn_const contDiffOn_const
    (fun p _ ↦ by simp [dₜ, lapₓ]) hbdry
  have h0 := hcmp 0 ⟨subset_closure (mem_ball_self one_pos), by norm_num⟩
  have hw0 : w 0 = ∑ k : Fin d, partialDeriv k.castSucc v 0 ^ 2 + A * (v 0 * v 0) := by
    have : ζ 0 = 1 := bernsteinCutoff_zero
    simp [hwdef, hZdef, hGdef, this]
  rw [hw0] at h0
  have : 0 ≤ A * (v 0 * v 0) := mul_nonneg (by positivity) (mul_self_nonneg _)
  linarith

/-! ### The gradient bound at any scale -/

/-- The parabolic affine map sends the unit closed cylinder onto `closedParCyl x₀ t₀ r`. -/
theorem parAffine_mem_closedParCyl {x₀ : E d} {t₀ r : ℝ} (hr : 0 ≤ r) {q : E d × ℝ}
    (hq : q ∈ closedParCyl (0 : E d) 0 1) : parAffine x₀ t₀ r q ∈ closedParCyl x₀ t₀ r := by
  rw [closedParCyl_zero_one] at hq
  obtain ⟨h1, h2, h3⟩ := hq
  rw [mem_closedBall_zero_iff] at h1
  refine ⟨?_, ?_, ?_⟩
  · rw [parAffine_fst, mem_closedBall, dist_self_add_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr]
    nlinarith [norm_nonneg q.1]
  · rw [parAffine_snd]
    nlinarith [mul_nonneg (sq_nonneg r) (by linarith : (0 : ℝ) ≤ q.2 + 1)]
  · rw [parAffine_snd]
    nlinarith [mul_nonneg (sq_nonneg r) (by linarith : (0 : ℝ) ≤ -q.2)]

theorem abs_le_of_mem_closedParCyl_center {v : E d × ℝ → ℝ} {x₀ : E d} {t₀ r M : ℝ}
    (hr : 0 ≤ r) (hM : ∀ q ∈ closedParCyl x₀ t₀ r, |v q| ≤ M) : 0 ≤ M :=
  (abs_nonneg _).trans (hM _ (center_mem_closedParCyl x₀ t₀ hr))

/-- **Bernstein gradient bound** (in partials): `|∇ₓ v(x₀, t₀)|² ≤ (C M / r)²`. -/
theorem IsSmoothCaloricOn.sum_sq_partialDeriv_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → closedParCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ closedParCyl x₀ t₀ r, |v q| ≤ M) →
    ∑ i : Fin d, partialDeriv i.castSucc v (x₀, t₀) ^ 2 ≤ (C * M / r) ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := unit_bound (d := d)
  refine ⟨Real.sqrt A, Real.sqrt_nonneg A, fun {v O x₀ t₀ r M} hO hr hsub hv hM ↦ ?_⟩
  have hO' : IsOpen (parAffine x₀ t₀ r ⁻¹' O) := hO.preimage (continuous_parAffine x₀ t₀ r)
  have hsub' : closedParCyl (0 : E d) 0 1 ⊆ parAffine x₀ t₀ r ⁻¹' O := fun q hq ↦
    hsub (parAffine_mem_closedParCyl hr.le hq)
  have h := hA hO' hsub' (hv.comp_parAffine hO x₀ t₀ r)
    (fun q hq ↦ hM _ (parAffine_mem_closedParCyl hr.le hq))
  have h0 : parAffine x₀ t₀ r 0 = (x₀, t₀) := by simp [parAffine]
  have hscale : ∀ i : Fin d, partialDeriv i.castSucc (v ∘ parAffine x₀ t₀ r) 0 =
      r * partialDeriv i.castSucc v (x₀, t₀) := by
    intro i
    have := iterPartial_comp_parAffine hO hv.1 [i.castSucc] 0
      (by rw [mem_preimage, h0]; exact hsub (center_mem_closedParCyl x₀ t₀ hr.le))
    simpa [h0, Fin.castSucc_ne_last] using this
  simp only [hscale, mul_pow] at h
  rw [← Finset.mul_sum] at h
  rw [div_pow, mul_pow, Real.sq_sqrt hA0, le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- **Bernstein gradient bound**, componentwise: `|∂ᵢ v(x₀, t₀)| ≤ C M / r` for every space
direction. -/
theorem IsSmoothCaloricOn.abs_partialDeriv_space_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → closedParCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ closedParCyl x₀ t₀ r, |v q| ≤ M) →
    ∀ i : Fin d, |partialDeriv i.castSucc v (x₀, t₀)| ≤ C * M / r := by
  obtain ⟨C, hC0, hC⟩ := IsSmoothCaloricOn.sum_sq_partialDeriv_le (d := d)
  refine ⟨C, hC0, fun {v O x₀ t₀ r M} hO hr hsub hv hM i ↦ ?_⟩
  have hM0 := abs_le_of_mem_closedParCyl_center hr.le hM
  have hi : partialDeriv i.castSucc v (x₀, t₀) ^ 2 ≤ (C * M / r) ^ 2 :=
    (Finset.single_le_sum (fun j _ ↦ sq_nonneg (partialDeriv j.castSucc v (x₀, t₀)))
      (Finset.mem_univ i)).trans (hC hO hr hsub hv hM)
  exact abs_le_of_sq_le_sq hi (by positivity)

/-- **Bernstein gradient bound**: `‖∇ₓ v(x₀, t₀)‖ ≤ C M / r`. -/
theorem IsSmoothCaloricOn.norm_gradₓ_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → closedParCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ closedParCyl x₀ t₀ r, |v q| ≤ M) → ‖gradₓ v (x₀, t₀)‖ ≤ C * M / r := by
  obtain ⟨C, hC0, hC⟩ := IsSmoothCaloricOn.sum_sq_partialDeriv_le (d := d)
  refine ⟨C, hC0, fun {v O x₀ t₀ r M} hO hr hsub hv hM ↦ ?_⟩
  have hM0 := abs_le_of_mem_closedParCyl_center hr.le hM
  have hp : (x₀, t₀) ∈ O := hsub (center_mem_closedParCyl x₀ t₀ hr.le)
  have hdiff : DifferentiableAt ℝ v (x₀, t₀) := differentiableAt_of_contDiffOn hO hv.1 hp
  have hn : ‖gradₓ v (x₀, t₀)‖ ^ 2 = ∑ i : Fin d, partialDeriv i.castSucc v (x₀, t₀) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [partialDeriv_castSucc_eq_gradₓ hdiff i, Real.norm_eq_abs, sq_abs]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    (hn ▸ hC hO hr hsub hv hM)

/-! ### All orders -/

private theorem half_scale (CB C' M r : ℝ) (p : ℕ) (hr : 0 < r) :
    CB * (C' * M / (r / 2) ^ p) / (r / 2) = CB * C' * 2 ^ (p + 1) * M / r ^ (1 + p) := by
  have := hr.ne'
  rw [div_pow]
  field_simp
  ring

/-- The induction measure on words: space letters weigh `1`, the time letter weighs `3`
(so that `∂ₜ ↦ ∑ᵢ ∂ᵢ∂ᵢ` decreases it). -/
def bernsteinMeasure : List (Fin (d + 1)) → ℕ
  | [] => 0
  | j :: w => (if j = Fin.last d then 3 else 1) + bernsteinMeasure w

/-- **Bernstein bounds of all orders.** For every word `w` of partials there is `C = C(d, w)` with
`|∂^w v(x₀, t₀)| ≤ C M / r ^ parOrder w` whenever `v` is smooth caloric on an open
`O ⊇ closedParCyl x₀ t₀ r` and `|v| ≤ M` there. -/
theorem IsSmoothCaloricOn.abs_iterPartial_le (w : List (Fin (d + 1))) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → closedParCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ closedParCyl x₀ t₀ r, |v q| ≤ M) →
    |iterPartial w v (x₀, t₀)| ≤ C * M / r ^ parOrder w := by
  obtain ⟨CB, hCB0, hCB⟩ := IsSmoothCaloricOn.abs_partialDeriv_space_le (d := d)
  suffices H : ∀ n, ∀ w : List (Fin (d + 1)), bernsteinMeasure w = n → ∃ C : ℝ, 0 ≤ C ∧
      ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
      IsOpen O → 0 < r → closedParCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
      (∀ q ∈ closedParCyl x₀ t₀ r, |v q| ≤ M) →
      |iterPartial w v (x₀, t₀)| ≤ C * M / r ^ parOrder w from H _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn
  rcases w with _ | ⟨j, w'⟩
  · refine ⟨1, zero_le_one, fun {v O x₀ t₀ r M} hO hr hsub hv hM ↦ ?_⟩
    simpa using hM _ (center_mem_closedParCyl x₀ t₀ hr.le)
  induction j using Fin.lastCases with
  | cast i =>
    -- a space letter: Bernstein on the half cylinder, applied to `∂^{w'} v`
    have hlt : bernsteinMeasure w' < n := by
      rw [← hn, bernsteinMeasure, if_neg (Fin.castSucc_ne_last i)]; omega
    obtain ⟨C', hC'0, hC'⟩ := ih _ hlt w' rfl
    refine ⟨CB * C' * 2 ^ (parOrder w' + 1), by positivity,
      fun {v O x₀ t₀ r M} hO hr hsub hv hM ↦ ?_⟩
    have hr2 : 0 < r / 2 := half_pos hr
    have hg := hv.iteratedPartial hO w'
    have hhalf : closedParCyl x₀ t₀ (r / 2) ⊆ closedParCyl x₀ t₀ r :=
      closedParCyl_half_subset (x := x₀) (t := t₀) (r := r) (q := (x₀, t₀))
        (center_mem_closedParCyl x₀ t₀ hr2.le)
    have hbd : ∀ q ∈ closedParCyl x₀ t₀ (r / 2),
        |iterPartial w' v q| ≤ C' * M / (r / 2) ^ parOrder w' := by
      intro q hq
      have hsq := closedParCyl_half_subset hq
      exact hC' hO hr2 (hsq.trans hsub) hv fun q' hq' ↦ hM q' (hsq hq')
    have h := hCB hO hr2 (hhalf.trans hsub) hg hbd i
    simp only [iterPartial_cons, parOrder_cons, if_neg (Fin.castSucc_ne_last i)]
    exact h.trans (le_of_eq (half_scale CB C' M r (parOrder w') hr))
  | last =>
    -- the time letter: `∂ₜ g = ∑ᵢ ∂ᵢ∂ᵢ g` on the smooth caloric `g = ∂^{w'} v`
    have hlt : ∀ i : Fin d, bernsteinMeasure (i.castSucc :: i.castSucc :: w') < n := by
      intro i
      rw [← hn]
      simp only [bernsteinMeasure, if_neg (Fin.castSucc_ne_last i), if_true]
      omega
    have hC := fun i : Fin d ↦ ih _ (hlt i) (i.castSucc :: i.castSucc :: w') rfl
    choose C hC0 hC using hC
    refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ ↦ hC0 i,
      fun {v O x₀ t₀ r M} hO hr hsub hv hM ↦ ?_⟩
    have hp : (x₀, t₀) ∈ O := hsub (center_mem_closedParCyl x₀ t₀ hr.le)
    have hg := hv.iteratedPartial hO w'
    simp only [iterPartial_cons, parOrder_cons, if_true]
    rw [hg.partialDeriv_last_eq hO hp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have := hC i hO hr hsub hv hM
    simp only [iterPartial_cons, parOrder_cons, if_neg (Fin.castSucc_ne_last i)] at this
    rw [show 1 + (1 + parOrder w') = 2 + parOrder w' by omega] at this
    exact this

end ParabolicBasic
