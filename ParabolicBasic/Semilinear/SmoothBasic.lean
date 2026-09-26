/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.Partials
public import ParabolicBasic.Defs.Classical
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# `C^{2,1}` calculus for the smoothness bootstrap

A classical `C^{2,1}` function on an open box `U × I` is jointly (strictly) differentiable, with
`Dφ(p) = (∇ₓφ(p), ∂ₜφ(p))` (`hasStrictFDerivAt_uncurry_coprod`: continuous partials along a product
decomposition), and its coordinate partials are the components of `gradₓ φ` and `dₜ φ` (the
dictionary of `ParabolicBasic.Analysis.Partials`).

No Hölder bound for `C^{2,1}` functions is needed here: the bootstrap gets `φ ∈ 𝓗⁰` from J(0)
(`locHolder_of_isHeatSolOn`), and the Hölder bounds of the first partials from J(2). No translation
calculus is needed either: difference quotients are handled at the viscosity level
(`Semilinear/SmoothDiffQuot.lean`).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Gradient

namespace ParabolicBasic

variable {d : ℕ}

/-- A `C^{2,1}` function on an open box is strictly differentiable, with derivative
`(v, s) ↦ ⟪∇ₓφ(p), v⟫ + s ∂ₜφ(p)`. -/
theorem IsC21On.hasStrictFDerivAt {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {φ : E d × ℝ → ℝ} (hφ : IsC21On U I φ) {p : E d × ℝ} (hp : p ∈ U ×ˢ I) :
    HasStrictFDerivAt φ ((InnerProductSpace.toDual ℝ (E d) (gradₓ φ p)).coprod
      (dₜ φ p • ContinuousLinearMap.id ℝ ℝ)) p := by
  have hΩ : IsOpen (U ×ˢ I) := hU.prod hI
  have hev : ∀ᶠ v in 𝓝 p, v ∈ U ×ˢ I := hΩ.mem_nhds hp
  have h := hasStrictFDerivAt_uncurry_coprod (u := p) (f := fun x t ↦ φ (x, t))
    (f₁ := fun x t ↦ InnerProductSpace.toDual ℝ (E d) (gradₓ φ (x, t)))
    (f₂ := fun x t ↦ dₜ φ (x, t) • ContinuousLinearMap.id ℝ ℝ) ?_ ?_ ?_ ?_
  · exact h
  · filter_upwards [hev] with v hv
    have hd : DifferentiableAt ℝ (fun x ↦ φ (x, v.2)) v.1 :=
      ((hφ.2.1 v.2 hv.2).differentiableOn (by norm_num) v.1 hv.1).differentiableAt
        (hU.mem_nhds hv.1)
    exact hasGradientAt_iff_hasFDerivAt.1 hd.hasGradientAt
  · filter_upwards [hev] with v hv
    have hd := (hφ.2.2.2.2.1 v hv).hasDerivAt
    convert hd.hasFDerivAt using 1
    ext
    change (dₜ φ (v.1, v.2) • ContinuousLinearMap.id ℝ ℝ) 1 = _
    simp [dₜ]
  · exact (InnerProductSpace.toDual ℝ (E d)).continuous.continuousAt.comp
      (hφ.2.2.1.continuousAt (hΩ.mem_nhds hp))
  · exact (hφ.2.2.2.2.2.continuousAt (hΩ.mem_nhds hp)).smul continuousAt_const

/-- A `C^{2,1}` function on an open box is differentiable there. -/
theorem IsC21On.differentiableAt {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {φ : E d × ℝ → ℝ} (hφ : IsC21On U I φ) {p : E d × ℝ} (hp : p ∈ U ×ˢ I) :
    DifferentiableAt ℝ φ p :=
  (hφ.hasStrictFDerivAt hU hI hp).differentiableAt

theorem IsC21On.differentiableOn {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {φ : E d × ℝ → ℝ} (hφ : IsC21On U I φ) : DifferentiableOn ℝ φ (U ×ˢ I) :=
  fun _ hp ↦ (hφ.differentiableAt hU hI hp).differentiableWithinAt

/-- The spatial coordinate partials of a `C^{2,1}` function are the components of `gradₓ φ`. -/
theorem IsC21On.partialDeriv_castSucc {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U)
    (hI : IsOpen I) {φ : E d × ℝ → ℝ} (hφ : IsC21On U I φ) (i : Fin d) :
    EqOn (fun p ↦ gradₓ φ p i) (partialDeriv i.castSucc φ) (U ×ˢ I) := fun _ hp ↦
  (partialDeriv_castSucc_eq_gradₓ (hφ.differentiableAt hU hI hp) i).symm

/-- The time partial of a `C^{2,1}` function is `dₜ φ`. -/
theorem IsC21On.partialDeriv_last {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U)
    (hI : IsOpen I) {φ : E d × ℝ → ℝ} (hφ : IsC21On U I φ) :
    EqOn (dₜ φ) (partialDeriv (Fin.last d) φ) (U ×ˢ I) := fun _ hp ↦
  dₜ_eq_partialDeriv_last (hφ.differentiableAt hU hI hp)

/-- The components of the spatial gradient of a `C^{2,1}` function are continuous. -/
theorem IsC21On.continuousOn_gradₓ_apply {U : Set (E d)} {I : Set ℝ} {φ : E d × ℝ → ℝ}
    (hφ : IsC21On U I φ) (i : Fin d) : ContinuousOn (fun p ↦ gradₓ φ p i) (U ×ˢ I) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hφ.2.2.1

end ParabolicBasic
