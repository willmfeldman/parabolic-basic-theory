/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Caloric.Bernstein

/-!
# Taylor bounds for smooth caloric functions on centred cylinders

For `v` smooth caloric on an open `O ⊇ cCyl x₀ t₀ r` with `|v| ≤ M` on `cCyl x₀ t₀ r`,
`p₀ = (x₀, t₀)`, `0 < ρ ≤ r/2` and `q ∈ cCyl x₀ t₀ ρ`:

* `taylor0_le`: `|v q - v p₀| ≤ C M (ρ/r)`;
* `taylor1_le`: `|v q - caloricTaylor1 v p₀ q| ≤ C M (ρ/r)²`;
* `taylor2_le`: `|v q - caloricTaylor2 v p₀ q| ≤ C M (ρ/r)³`;
* coefficient bounds: `‖∇ₓ v p₀‖ ≤ C M / r`, `|∂ₜ v p₀| ≤ C M / r²`,
  `|D²ₓ v p₀ [eᵢ, eⱼ]| ≤ C M / r²`.

The Taylor polynomials are written in raw form, with `gradₓ`, `dₜ` and
`hessₓ` (the second derivative of the spatial slice):
`caloricTaylor2 v p₀ q = v p₀ + ⟪∇ₓv p₀, q₁ - x₀⟫ + ∂ₜv p₀ (q₂ - t₀)
  + ½ D²ₓv p₀ [q₁ - x₀, q₁ - x₀]`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- The degree-1 caloric Taylor polynomial at `p₀`: `v p₀ + ⟪∇ₓ v p₀, q₁ - p₀₁⟫`. -/
noncomputable def caloricTaylor1 (v : E d × ℝ → ℝ) (p₀ q : E d × ℝ) : ℝ :=
  v p₀ + inner ℝ (gradₓ v p₀) (q.1 - p₀.1)

/-- The parabolic degree-2 caloric Taylor polynomial at `p₀`:
`v p₀ + ⟪∇ₓ v p₀, q₁ - p₀₁⟫ + ∂ₜ v p₀ (q₂ - p₀₂) + ½ D²ₓ v p₀ [q₁ - p₀₁, q₁ - p₀₁]`. -/
noncomputable def caloricTaylor2 (v : E d × ℝ → ℝ) (p₀ q : E d × ℝ) : ℝ :=
  caloricTaylor1 v p₀ q + dₜ v p₀ * (q.2 - p₀.2) +
    1 / 2 * hessₓ v p₀ ![q.1 - p₀.1, q.1 - p₀.1]

/-! ### One-dimensional Taylor bounds (crude constants) -/

/-- Mean value inequality on `[0, x] ⊆ [0, 1]`. -/
theorem abs_sub_le_of_hasDerivAt_Icc {φ φ' : ℝ → ℝ} {K x : ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' s) s) (hx : x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ s ∈ Icc (0 : ℝ) x, |φ' s| ≤ K) : |φ x - φ 0| ≤ K * x := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (f' := φ') (a := 0) (b := x)
    (C := K) (fun y hy ↦ (hφ y ⟨hy.1, hy.2.trans hx.2⟩).hasDerivWithinAt)
    (fun y hy ↦ by rw [Real.norm_eq_abs]; exact hb y ⟨hy.1, hy.2.le⟩)
    x ⟨hx.1, le_rfl⟩
  rwa [Real.norm_eq_abs, sub_zero] at this

/-- First-order Taylor bound on `[0, x] ⊆ [0, 1]`. -/
theorem abs_taylor1_le_of_hasDerivAt_Icc {φ φ1 φ2 : ℝ → ℝ} {K x : ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (hφ1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ2 s| ≤ K) (hx : x ∈ Icc (0 : ℝ) 1) :
    |φ x - φ 0 - x * φ1 0| ≤ K * x ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hψ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ φ s - s * φ1 0) (φ1 s - φ1 0) s :=
    fun s hs ↦ (hφ s hs).sub (hasDerivAt_mul_const (φ1 0))
  have := abs_sub_le_of_hasDerivAt_Icc (K := K * x) hψ hx fun s hs ↦
    (abs_sub_le_of_hasDerivAt_Icc hφ1 ⟨hs.1, hs.2.trans hx.2⟩ fun y hy ↦
      hb y ⟨hy.1, hy.2.trans (hs.2.trans hx.2)⟩).trans (mul_le_mul_of_nonneg_left hs.2 hK)
  have e : φ x - φ 0 - x * φ1 0 = (φ x - x * φ1 0) - (φ 0 - 0 * φ1 0) := by ring
  rw [e]
  calc _ ≤ K * x * x := this
    _ = K * x ^ 2 := by ring

/-- Second-order Taylor bound on `[0, x] ⊆ [0, 1]`. -/
theorem abs_taylor2_le_of_hasDerivAt_Icc {φ φ1 φ2 φ3 : ℝ → ℝ} {K x : ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (hφ1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (hφ2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ2 (φ3 s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ3 s| ≤ K) (hx : x ∈ Icc (0 : ℝ) 1) :
    |φ x - φ 0 - x * φ1 0 - x ^ 2 / 2 * φ2 0| ≤ K * x ^ 3 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hsq : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2 * φ2 0) (s * φ2 0) s := fun s ↦ by
    have := ((hasDerivAt_pow 2 s).div_const 2).mul_const (φ2 0)
    convert this using 1
    push_cast
    ring
  have hψ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ φ s - s * φ1 0 - s ^ 2 / 2 * φ2 0)
      (φ1 s - φ1 0 - s * φ2 0) s :=
    fun s hs ↦ ((hφ s hs).sub (hasDerivAt_mul_const (φ1 0))).sub (hsq s)
  have := abs_sub_le_of_hasDerivAt_Icc (K := K * x ^ 2) hψ hx fun s hs ↦
    (abs_taylor1_le_of_hasDerivAt_Icc hφ1 hφ2 hb ⟨hs.1, hs.2.trans hx.2⟩).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hs.2 2) hK)
  have e : φ x - φ 0 - x * φ1 0 - x ^ 2 / 2 * φ2 0 =
      (φ x - x * φ1 0 - x ^ 2 / 2 * φ2 0) - (φ 0 - 0 * φ1 0 - 0 ^ 2 / 2 * φ2 0) := by ring
  rw [e]
  calc _ ≤ K * x ^ 2 * x := this
    _ = K * x ^ 3 := by ring

/-! ### Derivatives along lines -/

/-- The derivative along the line `s ↦ p + s e`, in coordinate partials. -/
theorem hasDerivAt_comp_line {F : E d × ℝ → ℝ} {p e : E d × ℝ} {s : ℝ}
    (hF : DifferentiableAt ℝ F (p + s • e)) :
    HasDerivAt (fun s : ℝ ↦ F (p + s • e))
      (∑ j, ecoord d j e * partialDeriv j F (p + s • e)) s := by
  have hγ : HasDerivAt (fun s : ℝ ↦ p + s • e) e s := by
    simpa using ((hasDerivAt_id s).smul_const e).const_add p
  have := hF.hasFDerivAt.comp_hasDerivAt s hγ
  convert this using 1
  · rfl
  rw [fderiv_eq_sum_partialDeriv]
  simp [mul_comm]

theorem sum_ecoord_time (τ : ℝ) (g : Fin (d + 1) → ℝ) :
    ∑ j, ecoord d j ((0 : E d), τ) * g j = τ * g (Fin.last d) := by
  simp [Fin.sum_univ_castSucc]

theorem sum_ecoord_space (h : E d) (g : Fin (d + 1) → ℝ) :
    ∑ j, ecoord d j (h, (0 : ℝ)) * g j = ∑ i : Fin d, h i * g i.castSucc := by
  simp [Fin.sum_univ_castSucc]

/-- The spatial directional derivative `∑ᵢ hᵢ ∂ᵢ G`. -/
noncomputable def spaceDir (h : E d) (G : E d × ℝ → ℝ) : E d × ℝ → ℝ :=
  fun z ↦ ∑ i : Fin d, h i * partialDeriv i.castSucc G z

section Dir

variable {O : Set (E d × ℝ)} {G : E d × ℝ → ℝ}

theorem contDiffOn_spaceDir (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O) (h : E d) :
    ContDiffOn ℝ ∞ (spaceDir h G) O :=
  ContDiffOn.sum fun _ _ ↦ contDiffOn_const.mul (contDiffOn_partialDeriv hO hG _)

theorem iterPartial_spaceDir (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O) (h : E d)
    (w : List (Fin (d + 1))) {z : E d × ℝ} (hz : z ∈ O) :
    iterPartial w (spaceDir h G) z = ∑ i : Fin d, h i * iterPartial (w ++ [i.castSucc]) G z := by
  have := iterPartial_finset_sum hO Finset.univ
    (F := fun i z ↦ h i * partialDeriv i.castSucc G z)
    (fun i _ ↦ contDiffOn_const.mul (contDiffOn_partialDeriv hO hG _)) w z hz
  refine this.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [iterPartial_const_mul hO (contDiffOn_partialDeriv hO hG _) (h i) w z hz, iterPartial_concat]

theorem hasDerivAt_space_line (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O) {p : E d × ℝ} {h : E d}
    {s : ℝ} (hs : p + s • (h, (0 : ℝ)) ∈ O) :
    HasDerivAt (fun s : ℝ ↦ G (p + s • (h, (0 : ℝ))))
      (spaceDir h G (p + s • (h, (0 : ℝ)))) s := by
  have := hasDerivAt_comp_line (differentiableAt_iterPartial hO hG [] hs)
  rwa [sum_ecoord_space] at this

theorem hasDerivAt_time_line (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O) {p : E d × ℝ} {τ : ℝ}
    {s : ℝ} (hs : p + s • ((0 : E d), τ) ∈ O) :
    HasDerivAt (fun s : ℝ ↦ G (p + s • ((0 : E d), τ)))
      (τ * partialDeriv (Fin.last d) G (p + s • ((0 : E d), τ))) s := by
  have := hasDerivAt_comp_line (differentiableAt_iterPartial hO hG [] hs)
  rwa [sum_ecoord_time] at this

end Dir

/-- `|∑ᵢ aᵢ Xᵢ| ≤ ρ ∑ᵢ |Xᵢ|` when all `|aᵢ| ≤ ρ`. -/
theorem abs_sum_mul_le_of_abs_le {n : ℕ} {a X : Fin n → ℝ} {ρ : ℝ} (ha : ∀ i, |a i| ≤ ρ) :
    |∑ i, a i * X i| ≤ ρ * ∑ i, |X i| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)

/-! ### Interior bounds on the half cylinder -/

theorem closedParCyl_subset_cCyl {x₀ : E d} {t₀ r : ℝ} (hr : 0 < r) {q : E d × ℝ}
    (hq : q ∈ cCyl x₀ t₀ (r / 2)) : closedParCyl q.1 q.2 (r / 4) ⊆ cCyl x₀ t₀ r := by
  rintro ⟨y, s⟩ ⟨hy, hs1, hs2⟩
  obtain ⟨hq1, hq2l, hq2r⟩ := hq
  rw [mem_closedBall] at hy
  rw [mem_ball] at hq1
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_ball]
    linarith [dist_triangle y q.1 x₀]
  · simp only at hs1 ⊢; nlinarith
  · simp only at hs2 ⊢; nlinarith

/-- Bernstein bounds of all orders on `cCyl x₀ t₀ (r/2)` for `|v| ≤ M` on `cCyl x₀ t₀ r`. -/
theorem IsSmoothCaloricOn.abs_iterPartial_le_of_cCyl (w : List (Fin (d + 1))) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) →
    ∀ q ∈ cCyl x₀ t₀ (r / 2), |iterPartial w v q| ≤ C * M / r ^ parOrder w := by
  obtain ⟨C, hC0, hC⟩ := IsSmoothCaloricOn.abs_iterPartial_le (d := d) w
  refine ⟨C * 4 ^ parOrder w, by positivity, fun {v O x₀ t₀ r M} hO hr hsub hv hM q hq ↦ ?_⟩
  have hs := closedParCyl_subset_cCyl hr hq
  have := hC (x₀ := q.1) (t₀ := q.2) (M := M) hO (by positivity) (hs.trans hsub) hv
    fun q' hq' ↦ hM q' (hs hq')
  simp only [Prod.mk.eta] at this
  refine this.trans (le_of_eq ?_)
  rw [div_pow, div_div_eq_mul_div]
  ring

/-! ### The slice operators at `p₀` in partials -/

theorem inner_gradₓ_eq_sum {f : E d × ℝ → ℝ} {p : E d × ℝ} (hf : DifferentiableAt ℝ f p)
    (h : E d) : inner ℝ (gradₓ f p) h = ∑ i : Fin d, h i * partialDeriv i.castSucc f p := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [partialDeriv_castSucc_eq_gradₓ hf i, RCLike.inner_apply, conj_trivial]

theorem hessₓ_apply_eq_sum {f : E d × ℝ → ℝ} {p : E d × ℝ} (hf : ContDiffAt ℝ 2 f p) (h : E d) :
    hessₓ f p ![h, h] = ∑ i : Fin d, ∑ k : Fin d,
      h i * h k * partialDeriv i.castSucc (partialDeriv k.castSucc f) p := by
  have hsum : h = ∑ i : Fin d, h i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr h]
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  have e2 : ∀ u w : E d, hessₓ f p ![u, w] =
      fderiv ℝ (fderiv ℝ (fun y ↦ f (y, p.2))) p.1 u w := fun u w ↦ by
    simp [hessₓ, iteratedFDeriv_two_apply]
  rw [e2]
  conv_lhs => rw [hsum]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← e2]
  unfold hessₓ
  rw [iteratedFDeriv_two_sliceX_single hf k i, partialDeriv_comm hf k.castSucc i.castSucc]
  ring

/-! ### Geometry of the Taylor segments -/

section Segments

variable {x₀ : E d} {t₀ ρ : ℝ} {q : E d × ℝ}

theorem abs_coord_le_of_mem_cCyl (hq : q ∈ cCyl x₀ t₀ ρ) (i : Fin d) : |(q.1 - x₀) i| ≤ ρ := by
  have h1 : ‖q.1 - x₀‖ < ρ := by rw [← dist_eq_norm]; exact hq.1
  have := PiLp.norm_apply_le (q.1 - x₀) i
  rw [Real.norm_eq_abs] at this
  linarith

theorem abs_time_le_of_mem_cCyl (hq : q ∈ cCyl x₀ t₀ ρ) : |q.2 - t₀| ≤ ρ ^ 2 := by
  obtain ⟨-, h1, h2⟩ := hq
  rw [abs_le]; constructor <;> linarith

theorem cCyl_center_mem (hρ : 0 < ρ) : (x₀, t₀) ∈ cCyl x₀ t₀ ρ :=
  ⟨mem_ball_self hρ, by simp only; nlinarith [pow_pos hρ 2], by simp only; nlinarith [pow_pos hρ 2]⟩

theorem space_line_mem (hq : q ∈ cCyl x₀ t₀ ρ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (x₀, t₀) + s • (q.1 - x₀, (0 : ℝ)) ∈ cCyl x₀ t₀ ρ := by
  have hρ : 0 < ρ := lt_of_le_of_lt dist_nonneg hq.1
  have h1 : ‖q.1 - x₀‖ < ρ := by rw [← dist_eq_norm]; exact hq.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, mem_ball, dist_self_add_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (norm_nonneg (q.1 - x₀))]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]
    linarith [pow_pos hρ 2]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]
    linarith [pow_pos hρ 2]

theorem time_line_mem (hq : q ∈ cCyl x₀ t₀ ρ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (q.1, t₀) + s • ((0 : E d), q.2 - t₀) ∈ cCyl x₀ t₀ ρ := by
  obtain ⟨h0, h1, h2⟩ := hq
  have hlt : |s * (q.2 - t₀)| < ρ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hs.1]
    calc s * |q.2 - t₀| ≤ |q.2 - t₀| := mul_le_of_le_one_left (abs_nonneg _) hs.2
      _ < ρ ^ 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  obtain ⟨hl, hr⟩ := abs_lt.1 hlt
  refine ⟨by simpa using h0, ?_, ?_⟩
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linarith
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linarith

theorem cCyl_subset_cCyl {r : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ ≤ r) : cCyl x₀ t₀ ρ ⊆ cCyl x₀ t₀ r := by
  have : ρ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hρ hρr 2
  rintro q ⟨h0, h1, h2⟩
  exact ⟨ball_subset_ball hρr h0, by linarith, by linarith⟩

end Segments

/-! ### The Taylor terms -/

section Terms

variable {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r ρ M : ℝ}
  {Cw : List (Fin (d + 1)) → ℝ} {q : E d × ℝ}

/-- The standing hypotheses of the Taylor terms: `v` smooth on `O ⊇ cCyl x₀ t₀ (r/2)` with the
Bernstein bounds `|∂^w v| ≤ Cw w · M / r^{|w|ₚ}` there, `0 < ρ ≤ r/2`, `q ∈ cCyl x₀ t₀ ρ`. -/
structure TaylorHyp (v : E d × ℝ → ℝ) (O : Set (E d × ℝ)) (x₀ : E d) (t₀ r ρ M : ℝ)
    (Cw : List (Fin (d + 1)) → ℝ) (q : E d × ℝ) : Prop where
  isOpen : IsOpen O
  smooth : ContDiffOn ℝ ∞ v O
  sub : cCyl x₀ t₀ (r / 2) ⊆ O
  bound : ∀ w, ∀ z ∈ cCyl x₀ t₀ (r / 2), |iterPartial w v z| ≤ Cw w * M / r ^ parOrder w
  hr : 0 < r
  hρ : 0 < ρ
  hρr : ρ ≤ r / 2
  hq : q ∈ cCyl x₀ t₀ ρ

namespace TaylorHyp

variable (H : TaylorHyp v O x₀ t₀ r ρ M Cw q)
include H

theorem sub_half : cCyl x₀ t₀ ρ ⊆ cCyl x₀ t₀ (r / 2) := cCyl_subset_cCyl H.hρ.le H.hρr

theorem rho_div : ρ / r ≤ 1 := by
  rw [div_le_one H.hr]; linarith [H.hρr, H.hr]

theorem pow_mul_bound (C : ℝ) (k : ℕ) : ρ ^ k * (C * M / r ^ k) = C * M * (ρ / r) ^ k := by
  have := H.hr
  rw [div_pow]; field_simp

theorem time_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (q.1, t₀) + s • ((0 : E d), q.2 - t₀) ∈ cCyl x₀ t₀ (r / 2) :=
  H.sub_half (time_line_mem H.hq hs)

theorem space_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (x₀, t₀) + s • (q.1 - x₀, (0 : ℝ)) ∈ cCyl x₀ t₀ (r / 2) :=
  H.sub_half (space_line_mem H.hq hs)

omit H in
theorem time_end1 : (q.1, t₀) + (1 : ℝ) • ((0 : E d), q.2 - t₀) = q := by
  ext <;> simp

omit H in
theorem space_end1 : (x₀, t₀) + (1 : ℝ) • (q.1 - x₀, (0 : ℝ)) = (q.1, t₀) := by
  ext <;> simp

theorem abs_time_sq : |q.2 - t₀| ^ 2 ≤ ρ ^ 4 :=
  calc |q.2 - t₀| ^ 2 ≤ (ρ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_time_le_of_mem_cCyl H.hq) 2
    _ = ρ ^ 4 := by ring

/-- `|v q - v(q₁, t₀)| ≤ C M (ρ/r)²`. -/
theorem time0 : |v q - v (q.1, t₀)| ≤ Cw [Fin.last d] * M * (ρ / r) ^ 2 := by
  have key := abs_sub_le_of_hasDerivAt_Icc
    (φ := fun s ↦ v ((q.1, t₀) + s • ((0 : E d), q.2 - t₀)))
    (φ' := fun s ↦ (q.2 - t₀) * partialDeriv (Fin.last d) v ((q.1, t₀) + s • ((0 : E d), q.2 - t₀)))
    (K := ρ ^ 2 * (Cw [Fin.last d] * M / r ^ 2))
    (fun s hs ↦ hasDerivAt_time_line H.isOpen H.smooth (H.sub (H.time_mem hs)))
    ⟨zero_le_one, le_rfl⟩ fun s hs ↦ by
      have hb := H.bound [Fin.last d] _ (H.time_mem ⟨hs.1, hs.2⟩)
      simp only [iterPartial_cons, iterPartial_nil, parOrder_cons, parOrder_nil,
        ite_true, add_zero] at hb
      rw [abs_mul]
      exact mul_le_mul (abs_time_le_of_mem_cCyl H.hq) hb (abs_nonneg _) (by positivity)
  simp only [time_end1, zero_smul, add_zero, mul_one] at key
  rw [← H.pow_mul_bound]
  exact key

/-- `|v q - v(q₁, t₀) - (q₂ - t₀) ∂ₜ v(q₁, t₀)| ≤ C M (ρ/r)⁴`. -/
theorem time1 : |v q - v (q.1, t₀) - (q.2 - t₀) * partialDeriv (Fin.last d) v (q.1, t₀)| ≤
    Cw [Fin.last d, Fin.last d] * M * (ρ / r) ^ 4 := by
  have hv1 := contDiffOn_partialDeriv H.isOpen H.smooth (Fin.last d)
  have key := abs_taylor1_le_of_hasDerivAt_Icc
    (φ := fun s ↦ v ((q.1, t₀) + s • ((0 : E d), q.2 - t₀)))
    (φ1 := fun s ↦ (q.2 - t₀) *
      partialDeriv (Fin.last d) v ((q.1, t₀) + s • ((0 : E d), q.2 - t₀)))
    (φ2 := fun s ↦ (q.2 - t₀) * ((q.2 - t₀) * partialDeriv (Fin.last d)
      (partialDeriv (Fin.last d) v) ((q.1, t₀) + s • ((0 : E d), q.2 - t₀))))
    (K := ρ ^ 4 * (Cw [Fin.last d, Fin.last d] * M / r ^ 4))
    (fun s hs ↦ hasDerivAt_time_line H.isOpen H.smooth (H.sub (H.time_mem hs)))
    (fun s hs ↦ (hasDerivAt_time_line H.isOpen hv1 (H.sub (H.time_mem hs))).const_mul _)
    (fun s hs ↦ by
      have hb := H.bound [Fin.last d, Fin.last d] _ (H.time_mem hs)
      simp only [iterPartial_cons, iterPartial_nil, parOrder_cons, parOrder_nil,
        ite_true, add_zero, Nat.reduceAdd] at hb
      calc _ = |q.2 - t₀| ^ 2 * |partialDeriv (Fin.last d) (partialDeriv (Fin.last d) v)
            ((q.1, t₀) + s • ((0 : E d), q.2 - t₀))| := by rw [abs_mul, abs_mul]; ring
        _ ≤ _ := mul_le_mul H.abs_time_sq hb (abs_nonneg _) (by positivity))
    ⟨zero_le_one, le_rfl⟩
  simp only [time_end1, zero_smul, add_zero, one_mul, one_pow, mul_one] at key
  rw [← H.pow_mul_bound]
  exact key

/-- `|(q₂ - t₀) (∂ₜ v(q₁, t₀) - ∂ₜ v p₀)| ≤ C M (ρ/r)³`. -/
theorem mixed : |(q.2 - t₀) * (partialDeriv (Fin.last d) v (q.1, t₀) -
    partialDeriv (Fin.last d) v (x₀, t₀))| ≤
      (∑ i : Fin d, Cw [i.castSucc, Fin.last d]) * M * (ρ / r) ^ 3 := by
  have hv1 := contDiffOn_partialDeriv H.isOpen H.smooth (Fin.last d)
  have key := abs_sub_le_of_hasDerivAt_Icc
    (φ := fun s ↦ partialDeriv (Fin.last d) v ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (φ' := fun s ↦ spaceDir (q.1 - x₀) (partialDeriv (Fin.last d) v)
      ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (K := ρ * ((∑ i : Fin d, Cw [i.castSucc, Fin.last d]) * M / r ^ 3))
    (fun s hs ↦ hasDerivAt_space_line H.isOpen hv1 (H.sub (H.space_mem hs)))
    ⟨zero_le_one, le_rfl⟩ fun s hs ↦ by
      refine (abs_sum_mul_le_of_abs_le (abs_coord_le_of_mem_cCyl H.hq)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ H.hρ.le
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hb := H.bound [i.castSucc, Fin.last d] _ (H.space_mem ⟨hs.1, hs.2⟩)
      simp only [iterPartial_cons, iterPartial_nil, parOrder_cons, parOrder_nil,
        Fin.castSucc_ne_last, ite_true, ite_false, add_zero, Nat.reduceAdd] at hb
      exact hb
  simp only [space_end1, zero_smul, add_zero, mul_one] at key
  rw [abs_mul]
  calc _ ≤ ρ ^ 2 * (ρ * ((∑ i : Fin d, Cw [i.castSucc, Fin.last d]) * M / r ^ 3)) :=
        mul_le_mul (abs_time_le_of_mem_cCyl H.hq) key (abs_nonneg _) (by positivity)
    _ = _ := by rw [← H.pow_mul_bound]; ring

/-- `|v(q₁, t₀) - v p₀| ≤ C M (ρ/r)`. -/
theorem space0 : |v (q.1, t₀) - v (x₀, t₀)| ≤
    (∑ i : Fin d, Cw [i.castSucc]) * M * (ρ / r) ^ 1 := by
  have key := abs_sub_le_of_hasDerivAt_Icc
    (φ := fun s ↦ v ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (φ' := fun s ↦ spaceDir (q.1 - x₀) v ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (K := ρ ^ 1 * ((∑ i : Fin d, Cw [i.castSucc]) * M / r ^ 1))
    (fun s hs ↦ hasDerivAt_space_line H.isOpen H.smooth (H.sub (H.space_mem hs)))
    ⟨zero_le_one, le_rfl⟩ fun s hs ↦ by
      refine (abs_sum_mul_le_of_abs_le (abs_coord_le_of_mem_cCyl H.hq)).trans ?_
      rw [pow_one]
      refine mul_le_mul_of_nonneg_left ?_ H.hρ.le
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hb := H.bound [i.castSucc] _ (H.space_mem ⟨hs.1, hs.2⟩)
      simp only [iterPartial_cons, iterPartial_nil, parOrder_cons, parOrder_nil,
        Fin.castSucc_ne_last, ite_false, add_zero] at hb
      simpa using hb
  simp only [space_end1, zero_smul, add_zero, mul_one] at key
  rw [← H.pow_mul_bound]
  exact key

/-- The second directional derivative along a spatial direction, in partials. -/
theorem spaceDir_spaceDir_eq {z : E d × ℝ} (hz : z ∈ O) (h : E d) :
    spaceDir h (spaceDir h v) z = ∑ i : Fin d, h i * ∑ k : Fin d,
      h k * partialDeriv i.castSucc (partialDeriv k.castSucc v) z := by
  unfold spaceDir
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := iterPartial_spaceDir H.isOpen H.smooth h [i.castSucc] hz
  simp only [iterPartial_cons, iterPartial_nil, List.singleton_append] at this
  unfold spaceDir at this
  rw [this]

/-- The third directional derivative along a spatial direction, in partials. -/
theorem spaceDir3_eq {z : E d × ℝ} (hz : z ∈ O) (h : E d) :
    spaceDir h (spaceDir h (spaceDir h v)) z = ∑ i : Fin d, h i * ∑ k : Fin d, h k *
      ∑ l : Fin d, h l * partialDeriv i.castSucc (partialDeriv k.castSucc
        (partialDeriv l.castSucc v)) z := by
  have hS := contDiffOn_spaceDir H.isOpen H.smooth h
  unfold spaceDir
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h1 := iterPartial_spaceDir H.isOpen hS h [i.castSucc] hz
  simp only [iterPartial_cons, iterPartial_nil, List.singleton_append] at h1
  unfold spaceDir at h1
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h2 := iterPartial_spaceDir H.isOpen H.smooth h [i.castSucc, k.castSucc] hz
  simp only [iterPartial_cons, iterPartial_nil, List.cons_append, List.nil_append] at h2
  unfold spaceDir at h2
  rw [h2]

/-- `|v(q₁, t₀) - v p₀ - ∑ᵢ hᵢ ∂ᵢ v p₀| ≤ C M (ρ/r)²`. -/
theorem space1 : |v (q.1, t₀) - v (x₀, t₀) -
    ∑ i : Fin d, (q.1 - x₀) i * partialDeriv i.castSucc v (x₀, t₀)| ≤
      (∑ i : Fin d, ∑ k : Fin d, Cw [i.castSucc, k.castSucc]) * M * (ρ / r) ^ 2 := by
  have hS := contDiffOn_spaceDir H.isOpen H.smooth (q.1 - x₀)
  have key := abs_taylor1_le_of_hasDerivAt_Icc
    (φ := fun s ↦ v ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (φ1 := fun s ↦ spaceDir (q.1 - x₀) v ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (φ2 := fun s ↦ spaceDir (q.1 - x₀) (spaceDir (q.1 - x₀) v)
      ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (K := ρ ^ 2 * ((∑ i : Fin d, ∑ k : Fin d, Cw [i.castSucc, k.castSucc]) * M / r ^ 2))
    (fun s hs ↦ hasDerivAt_space_line H.isOpen H.smooth (H.sub (H.space_mem hs)))
    (fun s hs ↦ hasDerivAt_space_line H.isOpen hS (H.sub (H.space_mem hs)))
    (fun s hs ↦ by
      beta_reduce
      rw [H.spaceDir_spaceDir_eq (H.sub (H.space_mem hs))]
      refine (abs_sum_mul_le_of_abs_le (abs_coord_le_of_mem_cCyl H.hq)).trans ?_
      rw [pow_two, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ H.hρ.le
      rw [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      refine (abs_sum_mul_le_of_abs_le (abs_coord_le_of_mem_cCyl H.hq)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ H.hρ.le
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_le_sum fun k _ ↦ ?_
      have hb := H.bound [i.castSucc, k.castSucc] _ (H.space_mem hs)
      simp only [iterPartial_cons, iterPartial_nil, parOrder_cons, parOrder_nil,
        Fin.castSucc_ne_last, ite_false, add_zero, Nat.reduceAdd] at hb
      exact hb)
    ⟨zero_le_one, le_rfl⟩
  simp only [space_end1, zero_smul, add_zero, one_mul, one_pow, mul_one] at key
  rw [← H.pow_mul_bound]
  unfold spaceDir at key
  exact key

/-- `|v(q₁, t₀) - v p₀ - ∑ᵢ hᵢ ∂ᵢ v p₀ - ½ ∑ᵢₖ hᵢ hₖ ∂ᵢ∂ₖ v p₀| ≤ C M (ρ/r)³`. -/
theorem space2 : |v (q.1, t₀) - v (x₀, t₀) -
    ∑ i : Fin d, (q.1 - x₀) i * partialDeriv i.castSucc v (x₀, t₀) -
    1 / 2 * ∑ i : Fin d, ∑ k : Fin d, (q.1 - x₀) i * (q.1 - x₀) k *
      partialDeriv i.castSucc (partialDeriv k.castSucc v) (x₀, t₀)| ≤
      (∑ i : Fin d, ∑ k : Fin d, ∑ l : Fin d, Cw [i.castSucc, k.castSucc, l.castSucc]) * M *
        (ρ / r) ^ 3 := by
  have hS := contDiffOn_spaceDir H.isOpen H.smooth (q.1 - x₀)
  have hSS := contDiffOn_spaceDir H.isOpen hS (q.1 - x₀)
  have key := abs_taylor2_le_of_hasDerivAt_Icc
    (φ := fun s ↦ v ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (φ1 := fun s ↦ spaceDir (q.1 - x₀) v ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (φ2 := fun s ↦ spaceDir (q.1 - x₀) (spaceDir (q.1 - x₀) v)
      ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (φ3 := fun s ↦ spaceDir (q.1 - x₀) (spaceDir (q.1 - x₀) (spaceDir (q.1 - x₀) v))
      ((x₀, t₀) + s • (q.1 - x₀, (0 : ℝ))))
    (K := ρ ^ 3 * ((∑ i : Fin d, ∑ k : Fin d, ∑ l : Fin d,
      Cw [i.castSucc, k.castSucc, l.castSucc]) * M / r ^ 3))
    (fun s hs ↦ hasDerivAt_space_line H.isOpen H.smooth (H.sub (H.space_mem hs)))
    (fun s hs ↦ hasDerivAt_space_line H.isOpen hS (H.sub (H.space_mem hs)))
    (fun s hs ↦ hasDerivAt_space_line H.isOpen hSS (H.sub (H.space_mem hs)))
    (fun s hs ↦ by
      beta_reduce
      rw [H.spaceDir3_eq (H.sub (H.space_mem hs))]
      have hc := abs_coord_le_of_mem_cCyl H.hq
      refine (abs_sum_mul_le_of_abs_le hc).trans ?_
      rw [pow_succ', mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ H.hρ.le
      rw [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      refine (abs_sum_mul_le_of_abs_le hc).trans ?_
      rw [pow_two, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ H.hρ.le
      rw [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ ↦ ?_
      refine (abs_sum_mul_le_of_abs_le hc).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ H.hρ.le
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_le_sum fun l _ ↦ ?_
      have hb := H.bound [i.castSucc, k.castSucc, l.castSucc] _ (H.space_mem hs)
      simp only [iterPartial_cons, iterPartial_nil, parOrder_cons, parOrder_nil,
        Fin.castSucc_ne_last, ite_false, add_zero, Nat.reduceAdd] at hb
      exact hb)
    ⟨zero_le_one, le_rfl⟩
  simp only [space_end1, zero_smul, add_zero, one_mul, one_pow, mul_one] at key
  rw [H.spaceDir_spaceDir_eq (H.sub (H.sub_half (cCyl_center_mem H.hρ))) (q.1 - x₀)] at key
  rw [← H.pow_mul_bound]
  unfold spaceDir at key
  convert key using 2
  simp only [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end TaylorHyp

end Terms

/-! ### Assembling the hypotheses -/

section Assemble

variable {Cw : List (Fin (d + 1)) → ℝ}

theorem taylorHyp_of
    (hCw : ∀ w : List (Fin (d + 1)), ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d}
      {t₀ r M : ℝ}, IsOpen O → 0 < r → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
      (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) →
      ∀ q ∈ cCyl x₀ t₀ (r / 2), |iterPartial w v q| ≤ Cw w * M / r ^ parOrder w)
    {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r ρ M : ℝ} {q : E d × ℝ}
    (hO : IsOpen O) (hsub : cCyl x₀ t₀ r ⊆ O) (hv : IsSmoothCaloricOn O v)
    (hM : ∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) (hρ : 0 < ρ) (hρr : ρ ≤ r / 2)
    (hq : q ∈ cCyl x₀ t₀ ρ) : TaylorHyp v O x₀ t₀ r ρ M Cw q where
  isOpen := hO
  smooth := hv.1
  sub := (cCyl_subset_cCyl (by linarith) (by linarith)).trans hsub
  bound w := hCw w hO (by linarith) hsub hv hM
  hr := by linarith
  hρ := hρ
  hρr := hρr
  hq := hq

end Assemble

theorem abs_add_three_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  linarith [abs_add_le a b, abs_add_le (a + b) c]

/-- **Caloric Taylor bound, degree 0:** `|v q - v p₀| ≤ C M (ρ/r)`. -/
theorem IsSmoothCaloricOn.taylor0_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r ρ M : ℝ},
    IsOpen O → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v → (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) →
    0 < ρ → ρ ≤ r / 2 → ∀ q ∈ cCyl x₀ t₀ ρ, |v q - v (x₀, t₀)| ≤ C * M * (ρ / r) := by
  have hB := fun w : List (Fin (d + 1)) ↦ IsSmoothCaloricOn.abs_iterPartial_le_of_cCyl w
  choose Cw hCw0 hCw using hB
  have hS : 0 ≤ ∑ i : Fin d, Cw [i.castSucc] := Finset.sum_nonneg fun i _ ↦ hCw0 _
  refine ⟨Cw [Fin.last d] + ∑ i : Fin d, Cw [i.castSucc], by linarith [hCw0 [Fin.last d]],
    fun {v O x₀ t₀ r ρ M} hO hsub hv hM hρ hρr q hq ↦ ?_⟩
  have H := taylorHyp_of hCw hO hsub hv hM hρ hρr hq
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (cCyl_center_mem H.hr))
  have ha0 : 0 ≤ ρ / r := div_nonneg hρ.le H.hr.le
  have ha : (ρ / r) ^ 2 ≤ ρ / r := by
    rw [sq]; exact mul_le_of_le_one_left ha0 H.rho_div
  have h1 := H.time0
  have h2 := H.space0
  rw [pow_one] at h2
  have h1' : Cw [Fin.last d] * M * (ρ / r) ^ 2 ≤ Cw [Fin.last d] * M * (ρ / r) :=
    mul_le_mul_of_nonneg_left ha (mul_nonneg (hCw0 _) hM0)
  calc |v q - v (x₀, t₀)| = |(v q - v (q.1, t₀)) + (v (q.1, t₀) - v (x₀, t₀))| := by ring_nf
    _ ≤ |v q - v (q.1, t₀)| + |v (q.1, t₀) - v (x₀, t₀)| := abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- **Caloric Taylor bound, degree 1:** `|v q - caloricTaylor1 v p₀ q| ≤ C M (ρ/r)²`. -/
theorem IsSmoothCaloricOn.taylor1_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r ρ M : ℝ},
    IsOpen O → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v → (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) →
    0 < ρ → ρ ≤ r / 2 → ∀ q ∈ cCyl x₀ t₀ ρ,
      |v q - caloricTaylor1 v (x₀, t₀) q| ≤ C * M * (ρ / r) ^ 2 := by
  have hB := fun w : List (Fin (d + 1)) ↦ IsSmoothCaloricOn.abs_iterPartial_le_of_cCyl w
  choose Cw hCw0 hCw using hB
  have hS : 0 ≤ ∑ i : Fin d, ∑ k : Fin d, Cw [i.castSucc, k.castSucc] :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦ hCw0 _
  refine ⟨Cw [Fin.last d] + ∑ i : Fin d, ∑ k : Fin d, Cw [i.castSucc, k.castSucc],
    by linarith [hCw0 [Fin.last d]], fun {v O x₀ t₀ r ρ M} hO hsub hv hM hρ hρr q hq ↦ ?_⟩
  have H := taylorHyp_of hCw hO hsub hv hM hρ hρr hq
  have hp₀ : (x₀, t₀) ∈ O := hsub (cCyl_center_mem H.hr)
  have hdiff : DifferentiableAt ℝ v (x₀, t₀) := differentiableAt_of_contDiffOn hO hv.1 hp₀
  have e : v q - caloricTaylor1 v (x₀, t₀) q = (v q - v (q.1, t₀)) +
      (v (q.1, t₀) - v (x₀, t₀) -
        ∑ i : Fin d, (q.1 - x₀) i * partialDeriv i.castSucc v (x₀, t₀)) := by
    simp only [caloricTaylor1, inner_gradₓ_eq_sum hdiff]
    ring
  rw [e]
  have h1 := H.time0
  have h2 := H.space1
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **Caloric Taylor bound, degree 2:** `|v q - caloricTaylor2 v p₀ q| ≤ C M (ρ/r)³`. -/
theorem IsSmoothCaloricOn.taylor2_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r ρ M : ℝ},
    IsOpen O → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v → (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) →
    0 < ρ → ρ ≤ r / 2 → ∀ q ∈ cCyl x₀ t₀ ρ,
      |v q - caloricTaylor2 v (x₀, t₀) q| ≤ C * M * (ρ / r) ^ 3 := by
  have hB := fun w : List (Fin (d + 1)) ↦ IsSmoothCaloricOn.abs_iterPartial_le_of_cCyl w
  choose Cw hCw0 hCw using hB
  have hS2 : 0 ≤ ∑ i : Fin d, Cw [i.castSucc, Fin.last d] :=
    Finset.sum_nonneg fun i _ ↦ hCw0 _
  have hS3 : 0 ≤ ∑ i : Fin d, ∑ k : Fin d, ∑ l : Fin d, Cw [i.castSucc, k.castSucc, l.castSucc] :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun l _ ↦ hCw0 _
  refine ⟨Cw [Fin.last d, Fin.last d] + ∑ i : Fin d, Cw [i.castSucc, Fin.last d] +
    ∑ i : Fin d, ∑ k : Fin d, ∑ l : Fin d, Cw [i.castSucc, k.castSucc, l.castSucc],
    by linarith [hCw0 [Fin.last d, Fin.last d]],
    fun {v O x₀ t₀ r ρ M} hO hsub hv hM hρ hρr q hq ↦ ?_⟩
  have H := taylorHyp_of hCw hO hsub hv hM hρ hρr hq
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (cCyl_center_mem H.hr))
  have hp₀ : (x₀, t₀) ∈ O := hsub (cCyl_center_mem H.hr)
  have hdiff : DifferentiableAt ℝ v (x₀, t₀) := differentiableAt_of_contDiffOn hO hv.1 hp₀
  have hC2 : ContDiffAt ℝ 2 v (x₀, t₀) :=
    (hv.1.contDiffAt (hO.mem_nhds hp₀)).of_le (WithTop.coe_le_coe.2 le_top)
  have e : v q - caloricTaylor2 v (x₀, t₀) q =
      (v q - v (q.1, t₀) - (q.2 - t₀) * partialDeriv (Fin.last d) v (q.1, t₀)) +
      (q.2 - t₀) * (partialDeriv (Fin.last d) v (q.1, t₀) -
        partialDeriv (Fin.last d) v (x₀, t₀)) +
      (v (q.1, t₀) - v (x₀, t₀) -
        ∑ i : Fin d, (q.1 - x₀) i * partialDeriv i.castSucc v (x₀, t₀) -
        1 / 2 * ∑ i : Fin d, ∑ k : Fin d, (q.1 - x₀) i * (q.1 - x₀) k *
          partialDeriv i.castSucc (partialDeriv k.castSucc v) (x₀, t₀)) := by
    simp only [caloricTaylor2, caloricTaylor1, inner_gradₓ_eq_sum hdiff,
      dₜ_eq_partialDeriv_last hdiff, hessₓ_apply_eq_sum hC2]
    ring
  rw [e]
  have ha0 : 0 ≤ ρ / r := div_nonneg hρ.le H.hr.le
  have ha : (ρ / r) ^ 4 ≤ (ρ / r) ^ 3 := pow_le_pow_of_le_one ha0 H.rho_div (by norm_num)
  have h1 := H.time1
  have h1' : Cw [Fin.last d, Fin.last d] * M * (ρ / r) ^ 4 ≤
      Cw [Fin.last d, Fin.last d] * M * (ρ / r) ^ 3 :=
    mul_le_mul_of_nonneg_left ha (mul_nonneg (hCw0 _) hM0)
  have h2 := H.mixed
  have h3 := H.space2
  calc _ ≤ _ := abs_add_three_le _ _ _
    _ ≤ _ := add_le_add (add_le_add (h1.trans h1') h2) h3
    _ = _ := by ring

/-! ### Coefficient bounds -/

theorem closedParCyl_half_subset_cCyl {x₀ : E d} {t₀ r : ℝ} (hr : 0 < r) :
    closedParCyl x₀ t₀ (r / 2) ⊆ cCyl x₀ t₀ r := by
  rintro ⟨y, s⟩ ⟨hy, hs1, hs2⟩
  refine ⟨closedBall_subset_ball (by linarith) hy, ?_, ?_⟩
  · simp only at hs1 ⊢; nlinarith
  · simp only at hs2 ⊢; nlinarith

/-- **Coefficient bound** for the gradient: `‖∇ₓ v p₀‖ ≤ C M / r`. -/
theorem IsSmoothCaloricOn.norm_gradₓ_le_of_cCyl : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) → ‖gradₓ v (x₀, t₀)‖ ≤ C * M / r := by
  obtain ⟨C, hC0, hC⟩ := IsSmoothCaloricOn.norm_gradₓ_le (d := d)
  refine ⟨2 * C, by positivity, fun {v O x₀ t₀ r M} hO hr hsub hv hM ↦ ?_⟩
  have hs := closedParCyl_half_subset_cCyl (x₀ := x₀) (t₀ := t₀) hr
  refine (hC hO (half_pos hr) (hs.trans hsub) hv fun q hq ↦ hM q (hs hq)).trans (le_of_eq ?_)
  field_simp

/-- **Coefficient bound** for the time derivative: `|∂ₜ v p₀| ≤ C M / r²`. -/
theorem IsSmoothCaloricOn.abs_dₜ_le_of_cCyl : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) → |dₜ v (x₀, t₀)| ≤ C * M / r ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := IsSmoothCaloricOn.abs_iterPartial_le_of_cCyl (d := d) [Fin.last d]
  refine ⟨C, hC0, fun {v O x₀ t₀ r M} hO hr hsub hv hM ↦ ?_⟩
  have hp₀ : (x₀, t₀) ∈ O := hsub (cCyl_center_mem hr)
  have hb := hC hO hr hsub hv hM _ (cCyl_center_mem (half_pos hr))
  rw [dₜ_eq_partialDeriv_last (differentiableAt_of_contDiffOn hO hv.1 hp₀)]
  simpa using hb

/-- **Coefficient bound** for the spatial Hessian entries: `|D²ₓ v p₀ [eᵢ, eⱼ]| ≤ C M / r²`. -/
theorem IsSmoothCaloricOn.abs_hessₓ_le_of_cCyl : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : E d × ℝ → ℝ} {O : Set (E d × ℝ)} {x₀ : E d} {t₀ r M : ℝ},
    IsOpen O → 0 < r → cCyl x₀ t₀ r ⊆ O → IsSmoothCaloricOn O v →
    (∀ q ∈ cCyl x₀ t₀ r, |v q| ≤ M) → ∀ i j : Fin d,
      |hessₓ v (x₀, t₀) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]| ≤
        C * M / r ^ 2 := by
  have hB := fun w : List (Fin (d + 1)) ↦ IsSmoothCaloricOn.abs_iterPartial_le_of_cCyl w
  choose Cw hCw0 hCw using hB
  refine ⟨∑ i : Fin d, ∑ j : Fin d, Cw [i.castSucc, j.castSucc],
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hCw0 _,
    fun {v O x₀ t₀ r M} hO hr hsub hv hM i j ↦ ?_⟩
  have hp₀ : (x₀, t₀) ∈ O := hsub (cCyl_center_mem hr)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (cCyl_center_mem hr))
  have hC2 : ContDiffAt ℝ 2 v (x₀, t₀) :=
    (hv.1.contDiffAt (hO.mem_nhds hp₀)).of_le (WithTop.coe_le_coe.2 le_top)
  have hb := hCw [i.castSucc, j.castSucc] hO hr hsub hv hM _ (cCyl_center_mem (half_pos hr))
  norm_num [Fin.castSucc_ne_last] at hb
  rw [hessₓ, iteratedFDeriv_two_sliceX_single hC2 i j]
  refine hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM0) (by positivity))
  exact (Finset.single_le_sum (f := fun j ↦ Cw [i.castSucc, j.castSucc])
    (fun j _ ↦ hCw0 _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i ↦ ∑ j : Fin d, Cw [i.castSucc, j.castSucc])
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hCw0 _) (Finset.mem_univ i))

end ParabolicBasic
