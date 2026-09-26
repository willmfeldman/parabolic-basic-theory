/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.Partials
public import ParabolicBasic.Comparison.SumClosure
public import ParabolicBasic.Viscosity.Stability
public import ParabolicBasic.Schauder.Iteration.Basic

/-!
# Difference quotients of solutions of the heat equation with source

If `φ` is a viscosity solution of `dₜφ − lapₓφ = ψ` on an open `Ω` with `ψ` continuous, `φ, ψ`
differentiable on `Ω` and `∂ⱼφ, ∂ⱼψ` continuous on `Ω`, then `∂ⱼφ` is a viscosity solution of
`dₜ(∂ⱼφ) − lapₓ(∂ⱼφ) = ∂ⱼψ` on `Ω` (`isHeatSolOn_partialDeriv`).

The proof works entirely at the viscosity level:

* the difference quotient `φₕ = h⁻¹ (φ(· + h eⱼ) − φ)` solves the equation with source `ψₕ`
  (translation invariance `comp_parAffine`, negation, positive multiples, and the sum-closure
  theorem `IsViscSubOn.add_source`, which needs continuous sources);
* `φₕ → ∂ⱼφ` and `ψₕ → ∂ⱼψ` uniformly on small balls (`tendstoUniformlyOn_diffQuot`: mean value
  inequality along the segment and uniform continuity of `∂ⱼφ` on a compact ball);
* stability with varying sources (`of_tendstoLocallyUniformlyOn`) and `of_locally`.

This is more general than a `C^{2,1}` formulation: no classical translation calculus is needed.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Operations on `IsHeatSolOn` -/

namespace IsHeatSolOn

variable {Ω O : Set (E d × ℝ)} {H H₁ H₂ u u₁ u₂ : E d × ℝ → ℝ}

theorem congr (h : IsHeatSolOn Ω H u) {H' u' : E d × ℝ → ℝ} (hu : EqOn u u' Ω)
    (hH : EqOn H H' Ω) : IsHeatSolOn Ω H' u' :=
  ⟨(h.1.of_eqOn hu).mono_source fun p hp _ ↦ by simp [hH hp],
    ((IsViscSuperOn.congr hu).1 h.2).mono_source fun p hp _ ↦ by simp [hH hp]⟩

/-- Translation invariance. -/
theorem translate (h : IsHeatSolOn Ω H u) (a : E d × ℝ) (hO : IsOpen O)
    (hOΩ : ∀ q ∈ O, q + a ∈ Ω) :
    IsHeatSolOn O (fun q ↦ H (q + a)) (fun q ↦ u (q + a)) := by
  have hpa : ∀ q : E d × ℝ, parAffine a.1 a.2 1 q = q + a := fun q ↦ by
    ext <;> simp [parAffine, add_comm]
  have hsub : O ⊆ parAffine a.1 a.2 1 ⁻¹' Ω := fun q hq ↦ by
    rw [mem_preimage, hpa]; exact hOΩ q hq
  have hfun : (u ∘ parAffine a.1 a.2 1) = fun q ↦ u (q + a) := funext fun q ↦ by simp [hpa]
  have h1 := (h.1.comp_parAffine (x₀ := a.1) (t₀ := a.2) one_pos).mono_set hO hsub
  have h2 := (h.2.comp_parAffine (x₀ := a.1) (t₀ := a.2) one_pos).mono_set hO hsub
  rw [hfun] at h1 h2
  exact ⟨h1.mono_source fun q _ z ↦ by simp [hpa], h2.mono_source fun q _ z ↦ by simp [hpa]⟩

theorem neg (h : IsHeatSolOn Ω H u) : IsHeatSolOn Ω (fun q ↦ -H q) (fun q ↦ -u q) :=
  ⟨(isViscSuperOn_neg_iff.1 h.2).mono_source fun _ _ _ ↦ le_rfl,
    (isViscSubOn_neg_iff.1 h.1).mono_source fun _ _ _ ↦ le_rfl⟩

theorem const_mul {c : ℝ} (hc : 0 < c) (h : IsHeatSolOn Ω H u) :
    IsHeatSolOn Ω (fun q ↦ c * H q) (fun q ↦ c * u q) :=
  ⟨(h.1.const_smul hc).mono_source fun _ _ _ ↦ le_of_eq (by ring),
    (h.2.const_smul hc).mono_source fun _ _ _ ↦ ge_of_eq (by ring)⟩

theorem add (hΩ : IsOpen Ω) (hH₁ : ContinuousOn H₁ Ω) (hH₂ : ContinuousOn H₂ Ω)
    (h₁ : IsHeatSolOn Ω H₁ u₁) (h₂ : IsHeatSolOn Ω H₂ u₂) :
    IsHeatSolOn Ω (fun q ↦ H₁ q + H₂ q) (fun q ↦ u₁ q + u₂ q) :=
  ⟨IsViscSubOn.add_source hΩ hH₁ hH₂ h₁.1 h₂.1, IsViscSuperOn.add_source hΩ hH₁ hH₂ h₁.2 h₂.2⟩

/-- The difference quotient `c (φ(· + a) − φ)` (`c > 0`) solves the equation with source
`c (ψ(· + a) − ψ)`. -/
theorem diffQuot {φ ψ : E d × ℝ → ℝ} (h : IsHeatSolOn Ω ψ φ) (hψ : ContinuousOn ψ Ω)
    (hO : IsOpen O) (a : E d × ℝ) {c : ℝ} (hc : 0 < c) (hOΩ : ∀ q ∈ O, q ∈ Ω ∧ q + a ∈ Ω) :
    IsHeatSolOn O (fun q ↦ c * (ψ (q + a) - ψ q)) (fun q ↦ c * (φ (q + a) - φ q)) := by
  have h1 := h.translate a hO fun q hq ↦ (hOΩ q hq).2
  have h2 := (h.mono hO fun q hq ↦ (hOΩ q hq).1).neg
  have hc1 : ContinuousOn (fun q ↦ ψ (q + a)) O :=
    hψ.comp (continuous_add_const a).continuousOn fun q hq ↦ (hOΩ q hq).2
  have hc2 : ContinuousOn (fun q ↦ -ψ q) O := (hψ.mono fun q hq ↦ (hOΩ q hq).1).neg
  exact ((h1.add hO hc1 hc2 h2).const_mul hc).congr (fun q _ ↦ by simp [sub_eq_add_neg])
    (fun q _ ↦ by simp [sub_eq_add_neg])

end IsHeatSolOn

/-! ### Uniform convergence of difference quotients -/

/-- Difference quotients along `eⱼ` with steps `hₙ = ε / (n + 2)` converge to `∂ⱼ f` uniformly on
`ball p ε`, if `f` is differentiable on `Ω ⊇ closedBall p (2ε)` and `∂ⱼ f` is continuous there. -/
theorem tendstoUniformlyOn_diffQuot {Ω : Set (E d × ℝ)} {f : E d × ℝ → ℝ} {p : E d × ℝ}
    {ε : ℝ} (hε : 0 < ε) (hK : closedBall p (2 * ε) ⊆ Ω)
    (hf : ∀ q ∈ Ω, DifferentiableAt ℝ f q) (j : Fin (d + 1))
    (hfj : ContinuousOn (partialDeriv j f) Ω) :
    TendstoUniformlyOn
      (fun (n : ℕ) q ↦ (ε / (n + 2))⁻¹ * (f (q + (ε / (n + 2)) • ebasis d j) - f q))
      (partialDeriv j f) atTop (ball p ε) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have huc := (isCompact_closedBall p (2 * ε)).uniformContinuousOn_of_continuous (hfj.mono hK)
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc (η / 2) (half_pos hη)
  obtain ⟨N, hN⟩ := exists_nat_gt (ε / δ)
  filter_upwards [eventually_ge_atTop N] with n hn q hq
  set h : ℝ := ε / (n + 2) with hh
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hh0 : 0 < h := div_pos hε hn2
  have hhε : h < ε := by
    rw [hh, div_lt_iff₀ hn2]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hn2]
    have h1 : ε / δ < n + 2 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  set e := ebasis d j
  have hqe : ∀ s ∈ Icc (0 : ℝ) h, q + s • e ∈ closedBall p (2 * ε) := fun s hs ↦ by
    rw [mem_closedBall]
    have h1 : dist (q + s • e) q = s := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_ebasis, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hs.1]
    have h2 := dist_triangle (q + s • e) q p
    have h3 := mem_ball.1 hq
    linarith [hs.2]
  have hqK : q ∈ closedBall p (2 * ε) := by simpa using hqe 0 ⟨le_rfl, hh0.le⟩
  set c := partialDeriv j f q
  set g : ℝ → ℝ := fun s ↦ f (q + s • e) - s * c with hg
  have hderiv : ∀ s ∈ Icc (0 : ℝ) h,
      HasDerivWithinAt g (partialDeriv j f (q + s • e) - c) (Icc 0 h) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ ↦ q + s • e) ((1 : ℝ) • e) s :=
      ((hasDerivAt_id s).smul_const e).const_add q
    have h2 := (hf _ (hK (hqe s hs))).hasFDerivAt.comp_hasDerivAt s h1
    rw [one_smul] at h2
    have h3 := h2.sub ((hasDerivAt_id s).mul_const c)
    simp only [id, one_mul] at h3
    exact h3.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) h, ‖partialDeriv j f (q + s • e) - c‖ ≤ η / 2 := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) h := Ico_subset_Icc_self hs
    have hd : dist (q + s • e) q < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_ebasis, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hs.1]
      linarith [hs.2]
    have := hδuc _ (hqe s hs') q hqK hd
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound h ⟨hh0.le, le_rfl⟩
  simp only [hg, zero_smul, add_zero, zero_mul, sub_zero, Real.norm_eq_abs] at hmv
  rw [Real.dist_eq]
  have e1 : c - h⁻¹ * (f (q + h • e) - f q) = -(h⁻¹ * (f (q + h • e) - h * c - f q)) := by
    field_simp
    ring
  rw [e1, abs_neg, abs_mul, abs_of_pos (inv_pos.2 hh0)]
  calc h⁻¹ * |f (q + h • e) - h * c - f q| ≤ h⁻¹ * (η / 2 * h) := by gcongr
    _ = η / 2 := by field_simp
    _ < η := half_lt_self hη

/-! ### The difference-quotient lemma -/

/-- **Difference quotients.** On an open `Ω`, if `dₜφ − lapₓφ = ψ` in the viscosity sense with `ψ`
continuous, `φ, ψ` differentiable on `Ω` and `∂ⱼφ, ∂ⱼψ` continuous on `Ω`, then
`dₜ(∂ⱼφ) − lapₓ(∂ⱼφ) = ∂ⱼψ` in the viscosity sense on `Ω`. -/
theorem isHeatSolOn_partialDeriv {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {φ ψ : E d × ℝ → ℝ}
    (hsol : IsHeatSolOn Ω ψ φ) (hψc : ContinuousOn ψ Ω)
    (hφd : ∀ q ∈ Ω, DifferentiableAt ℝ φ q) (hψd : ∀ q ∈ Ω, DifferentiableAt ℝ ψ q)
    (j : Fin (d + 1)) (hφj : ContinuousOn (partialDeriv j φ) Ω)
    (hψj : ContinuousOn (partialDeriv j ψ) Ω) :
    IsHeatSolOn Ω (partialDeriv j ψ) (partialDeriv j φ) := by
  have key : ∀ p ∈ Ω, ∃ O, IsOpen O ∧ p ∈ O ∧ O ⊆ Ω ∧
      IsHeatSolOn O (partialDeriv j ψ) (partialDeriv j φ) := by
    intro p hp
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ p hp
    set ε := r / 4 with hε_def
    have hε : 0 < ε := by positivity
    have hK : closedBall p (2 * ε) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
    have hOΩ : ball p ε ⊆ Ω :=
      ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hK)
    refine ⟨ball p ε, isOpen_ball, mem_ball_self hε, hOΩ, ?_⟩
    set e := ebasis d j
    have hmem : ∀ n : ℕ, ∀ q ∈ ball p ε, q ∈ Ω ∧ q + (ε / (n + 2)) • e ∈ Ω := by
      intro n q hq
      refine ⟨hOΩ hq, hK ?_⟩
      have hn2 : (0 : ℝ) < n + 2 := by positivity
      have hh : ε / (n + 2) ≤ ε := div_le_self hε.le (by linarith)
      rw [mem_closedBall]
      have h1 : dist (q + (ε / (n + 2)) • e) q = ε / (n + 2) := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_ebasis, mul_one,
          Real.norm_eq_abs, abs_of_pos (div_pos hε hn2)]
      have h2 := dist_triangle (q + (ε / (n + 2)) • e) q p
      have h3 := mem_ball.1 hq
      linarith
    have hsoln : ∀ n : ℕ, IsHeatSolOn (ball p ε)
        (fun q ↦ (ε / (n + 2))⁻¹ * (ψ (q + (ε / (n + 2)) • e) - ψ q))
        (fun q ↦ (ε / (n + 2))⁻¹ * (φ (q + (ε / (n + 2)) • e) - φ q)) := fun n ↦
      hsol.diffQuot hψc isOpen_ball _ (inv_pos.2 (by positivity)) (hmem n)
    have hφu := tendstoUniformlyOn_diffQuot hε hK hφd j hφj
    have hψu := tendstoUniformlyOn_diffQuot hε hK hψd j hψj
    have hF : TendstoLocallyUniformlyOn
        (fun (n : ℕ) (q : (E d × ℝ) × ℝ) ↦
          -((ε / (n + 2))⁻¹ * (ψ (q.1 + (ε / (n + 2)) • e) - ψ q.1)))
        (fun q ↦ -partialDeriv j ψ q.1) atTop (ball p ε ×ˢ univ) := by
      have := TendstoLocallyUniformlyOn.neg_real ((hψu.comp Prod.fst).mono (fun q hq ↦ hq.1 :
        ball p ε ×ˢ (univ : Set ℝ) ⊆ Prod.fst ⁻¹' ball p ε)).tendstoLocallyUniformlyOn
      exact this
    have hFc : ContinuousOn (fun q : (E d × ℝ) × ℝ ↦ -partialDeriv j ψ q.1)
        (ball p ε ×ˢ univ) :=
      ((hψj.mono hOΩ).comp continuousOn_fst fun q hq ↦ hq.1).neg
    have hc : ContinuousOn (partialDeriv j φ) (ball p ε) := hφj.mono hOΩ
    refine ⟨IsViscSubOn.of_tendstoLocallyUniformlyOn isOpen_ball
      (Fn := fun n q _ ↦ -((ε / (n + 2))⁻¹ * (ψ (q + (ε / (n + 2)) • e) - ψ q)))
      (Eventually.of_forall fun n ↦ (hsoln n).1) hφu.tendstoLocallyUniformlyOn
      hc.upperSemicontinuousOn hF hFc,
      IsViscSuperOn.of_tendstoLocallyUniformlyOn isOpen_ball
      (Fn := fun n q _ ↦ -((ε / (n + 2))⁻¹ * (ψ (q + (ε / (n + 2)) • e) - ψ q)))
      (Eventually.of_forall fun n ↦ (hsoln n).2) hφu.tendstoLocallyUniformlyOn
      hc.lowerSemicontinuousOn hF hFc⟩
  exact ⟨IsViscSubOn.of_locally hΩ fun p hp ↦ by
      obtain ⟨O, hO, hpO, hOΩ, h⟩ := key p hp
      exact ⟨O, hO, hpO, hOΩ, h.1⟩,
    IsViscSuperOn.of_locally hΩ fun p hp ↦ by
      obtain ⟨O, hO, hpO, hOΩ, h⟩ := key p hp
      exact ⟨O, hO, hpO, hOΩ, h.2⟩⟩

end ParabolicBasic
