/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Viscosity.Basic
public import ParabolicBasic.Calculus.Affine

/-!
# Invariances of viscosity subsolutions

* `IsViscSubOn.comp_parAffine`: translation and parabolic scaling `A = parAffine x₀ t₀ r`
  (`r > 0`): `u ∘ A` is a subsolution on `A ⁻¹' Ω` for the source `r² F (A q) z`;
* `IsViscSubOn.add_contDiff`: adding a function `φ` which is `C²` on the open set `Ω` shifts the
  source to `F p (z - φ p) - (dₜ φ p - lapₓ φ p)`;
* `IsViscSubOn.const_smul`: multiplying by `c > 0` changes the source to `c F p (z / c)`;

with the supersolution mirrors, derived through `isViscSuperOn_neg_iff`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Parabolic affine maps -/

/-- Translation and parabolic scaling: the source picks up the
factor `r²`. -/
theorem IsViscSubOn.comp_parAffine {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} {x₀ : E d} {t₀ r : ℝ} (hr : 0 < r) (hu : IsViscSubOn Ω F u) :
    IsViscSubOn (parAffine x₀ t₀ r ⁻¹' Ω) (fun q z ↦ r ^ 2 * F (parAffine x₀ t₀ r q) z)
      (u ∘ parAffine x₀ t₀ r) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hAB := parAffine_parAffine_inv hr0 x₀ t₀
  have hBA := parAffine_inv_parAffine hr0 x₀ t₀
  refine ⟨UpperSemicontinuousOn.comp hu.1 (continuous_parAffine x₀ t₀ r).continuousOn
    (mapsTo_preimage _ _), fun ψ hψ q hq ht ↦ ?_⟩
  set B := parAffine (-(r⁻¹ • x₀)) (-(r⁻¹ ^ 2 * t₀)) r⁻¹ with hB
  set ψ' : E d × ℝ → ℝ := ψ ∘ B with hψ'
  have hψ'c : ContDiff ℝ 2 ψ' := hψ.comp (contDiff_parAffine _ _ _)
  have hψψ' : ψ' ∘ parAffine x₀ t₀ r = ψ := by
    funext y; simp [ψ', hBA]
  have ht' : TouchesAbove ψ' u Ω (parAffine x₀ t₀ r q) := by
    refine ⟨hq, by simpa [ψ', hBA] using ht.2.1, ?_⟩
    have hBt : Tendsto B (𝓝[Ω] (parAffine x₀ t₀ r q)) (𝓝[parAffine x₀ t₀ r ⁻¹' Ω] q) := by
      have h2 := ((continuous_parAffine (-(r⁻¹ • x₀)) (-(r⁻¹ ^ 2 * t₀)) r⁻¹).continuousWithinAt
        (s := Ω) (x := parAffine x₀ t₀ r q)).tendsto_nhdsWithin
        (t := parAffine x₀ t₀ r ⁻¹' Ω) (fun y hy ↦ by
          change parAffine x₀ t₀ r (B y) ∈ Ω
          rw [hAB]; exact hy)
      rw [← hB, hBA] at h2
      exact h2
    filter_upwards [hBt.eventually ht.2.2] with y hy
    simpa [ψ', hAB] using hy
  have key := hu.2 ψ' hψ'c _ hq ht'
  have h1 := dₜ_comp_parAffine ψ' x₀ t₀ r q
  have h2 := lapₓ_comp_parAffine hψ'c x₀ t₀ r q
  rw [hψψ'] at h1 h2
  simp only [Function.comp_apply]
  rw [h1, h2]
  have : 0 ≤ r ^ 2 := by positivity
  nlinarith

/-- Translation and parabolic scaling, supersolution mirror. -/
theorem IsViscSuperOn.comp_parAffine {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} {x₀ : E d} {t₀ r : ℝ} (hr : 0 < r) (hu : IsViscSuperOn Ω F u) :
    IsViscSuperOn (parAffine x₀ t₀ r ⁻¹' Ω) (fun q z ↦ r ^ 2 * F (parAffine x₀ t₀ r q) z)
      (u ∘ parAffine x₀ t₀ r) := by
  have := (isViscSuperOn_neg_iff.1 hu).comp_parAffine (x₀ := x₀) (t₀ := t₀) hr
  rw [isViscSuperOn_neg_iff]
  convert this using 1
  · funext q z
    ring
  · rfl

/-! ### Adding a `C²` function -/

/-- Adding a function `C²` on the open set `Ω`. -/
theorem IsViscSubOn.add_contDiff {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) {φ : E d × ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ Ω)
    (hu : IsViscSubOn Ω F u) :
    IsViscSubOn Ω (fun p z ↦ F p (z - φ p) - (dₜ φ p - lapₓ φ p)) (fun p ↦ u p + φ p) := by
  refine ⟨UpperSemicontinuousOn.add hu.1 hφ.continuousOn.upperSemicontinuousOn,
    fun ψ hψ p hp ht ↦ ?_⟩
  have hχ : ContDiffOn ℝ 2 (fun q ↦ ψ q - φ q) Ω := hψ.contDiffOn.sub hφ
  have htχ : TouchesAbove (fun q ↦ ψ q - φ q) u Ω p := by
    refine ⟨hp, by simp only [ht.2.1]; ring, ?_⟩
    filter_upwards [ht.2.2] with q hq
    linarith
  have key := hu.of_contDiffOn_test hΩ hp hχ htχ
  obtain ⟨h1, h2⟩ := dₜ_sub_lapₓ_sub_of_contDiffOn hΩ hp hφ hψ.contDiffOn
  rw [h1, h2] at key
  simp only [add_sub_cancel_right]
  linarith

/-- Adding a function `C²` on the open set `Ω`, supersolution mirror. -/
theorem IsViscSuperOn.add_contDiff {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) {φ : E d × ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ Ω)
    (hu : IsViscSuperOn Ω F u) :
    IsViscSuperOn Ω (fun p z ↦ F p (z - φ p) - (dₜ φ p - lapₓ φ p)) (fun p ↦ u p + φ p) := by
  have := (isViscSuperOn_neg_iff.1 hu).add_contDiff hΩ hφ.neg
  rw [isViscSuperOn_neg_iff]
  convert this using 1
  · funext p z
    simp only [dₜ_neg, lapₓ_neg, sub_neg_eq_add]
    ring_nf
  · funext p
    simp only [Pi.neg_apply]
    ring

/-! ### Positive multiples -/

theorem UpperSemicontinuousOn.const_mul_of_pos {X : Type*} [TopologicalSpace X] {S : Set X}
    {u : X → ℝ} (hu : UpperSemicontinuousOn u S) {c : ℝ} (hc : 0 < c) :
    UpperSemicontinuousOn (fun p ↦ c * u p) S := by
  intro x hx y hy
  have hy' : u x < y / c := by rw [lt_div_iff₀ hc]; linarith
  filter_upwards [hu x hx (y / c) hy'] with z hz
  rw [lt_div_iff₀ hc] at hz
  linarith

/-- Multiplying by a positive constant. -/
theorem IsViscSubOn.const_smul {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hu : IsViscSubOn Ω F u) :
    IsViscSubOn Ω (fun p z ↦ c * F p (z / c)) (fun p ↦ c * u p) := by
  refine ⟨UpperSemicontinuousOn.const_mul_of_pos hu.1 hc, fun ψ hψ p hp ht ↦ ?_⟩
  have hc0 : c ≠ 0 := hc.ne'
  have htχ : TouchesAbove (fun q ↦ c⁻¹ * ψ q) u Ω p := by
    refine ⟨hp, by simp only [ht.2.1]; field_simp, ?_⟩
    filter_upwards [ht.2.2] with q hq
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    linarith
  have key := hu.2 _ (contDiff_const.mul hψ) p hp htχ
  rw [dₜ_const_mul, lapₓ_const_mul hψ] at key
  simp only
  rw [mul_div_cancel_left₀ _ hc0]
  have : c * (c⁻¹ * dₜ ψ p - c⁻¹ * lapₓ ψ p + F p (u p)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc.le key
  have e : c * (c⁻¹ * dₜ ψ p - c⁻¹ * lapₓ ψ p + F p (u p)) =
      dₜ ψ p - lapₓ ψ p + c * F p (u p) := by
    field_simp
  linarith

/-- Multiplying by a positive constant, supersolution mirror. -/
theorem IsViscSuperOn.const_smul {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hu : IsViscSuperOn Ω F u) :
    IsViscSuperOn Ω (fun p z ↦ c * F p (z / c)) (fun p ↦ c * u p) := by
  have := (isViscSuperOn_neg_iff.1 hu).const_smul hc
  rw [isViscSuperOn_neg_iff]
  convert this using 1
  · funext p z
    simp [neg_div]
  · funext p
    simp

end ParabolicBasic
