/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Calculus.Slice
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Extremum tests for slices

* `iteratedFDeriv_two_nonneg_of_isLocalMin'`, `laplacian_nonneg_of_isLocalMin'`: at a local
  minimum of a function `C²` at the point, the second derivative in every direction and the
  Laplacian are nonnegative (reduced to the global statement by a smooth bump);
* `deriv_nonpos_of_isLocalMinOn_Iic`: the one-sided first-derivative test;
* `lapₓ_le_of_touchesAbove`, `gradₓ_eq_of_touchesAbove`: slice form in space;
* `dₜ_le_of_isLocalMinOn_Iic`, `dₜ_eq_of_isLocalMin`: slice form in time.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Second-order conditions at a minimum -/

section SecondOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- At a local minimum of a globally `C²` function `f`, the second derivative in every direction
is nonnegative. -/
theorem iteratedFDeriv_two_nonneg_of_isLocalMin {f : F → ℝ} {x : F} (hf : ContDiff ℝ 2 f)
    (hmin : IsLocalMin f x) (v : F) : 0 ≤ iteratedFDeriv ℝ 2 f x ![v, v] := by
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  set g : ℝ → ℝ := fun s ↦ f (x + s • v) with hg
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ x + s • v) v s := fun s ↦ by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hd1 : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hdg : ∀ s, HasDerivAt g (fderiv ℝ f (x + s • v) v) s := fun s ↦
    (hd1 _).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hderiv : deriv g = fun s ↦ fderiv ℝ f (x + s • v) v := funext fun s ↦ (hdg s).deriv
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hd2 : HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • v) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have h1 : HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • v)) (fderiv ℝ (fderiv ℝ f) x v) 0 := by
      have := ((hf'.differentiable one_ne_zero) (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) (hline 0)
      simpa [Function.comp_def] using this
    simpa using h1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hdd : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ f) x v v := by rw [hderiv]; exact hd2.deriv
  by_contra hneg
  rw [not_le] at hneg
  have hgmin : IsLocalMin g 0 := by
    refine IsLocalMin.comp_continuous (by simpa using hmin) ?_
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hg0 : deriv g 0 = 0 := hgmin.deriv_eq_zero
  have hgmax : IsLocalMax g 0 :=
    isLocalMax_of_deriv_deriv_neg (by rw [hdd]; exact hneg) hg0
      (hdg 0).differentiableAt.continuousAt
  -- `g` is locally constant at `0`, so its second derivative vanishes there.
  have hconst : g =ᶠ[𝓝 0] fun _ ↦ g 0 := by
    filter_upwards [hgmin, hgmax] with s h1 h2 using le_antisymm h2 h1
  have hdconst : deriv g =ᶠ[𝓝 0] fun _ ↦ 0 := by
    filter_upwards [hconst.eventuallyEq_nhds] with s hs
    rw [hs.deriv_eq]; simp
  have : deriv (deriv g) 0 = 0 := by rw [hdconst.deriv_eq]; simp
  linarith

/-- At a local minimum of a function `C²` at the point, the second derivative in every direction
is nonnegative. -/
theorem iteratedFDeriv_two_nonneg_of_isLocalMin' {f : F → ℝ} {x : F} [FiniteDimensional ℝ F]
    (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) (v : F) :
    0 ≤ iteratedFDeriv ℝ 2 f x ![v, v] := by
  obtain ⟨φ, hφ, hφf⟩ := ContDiffAt.exists_contDiff_eventuallyEq (n := 2) hf
  have hφmin : IsLocalMin φ x := by
    filter_upwards [hmin, hφf] with y hy hy'
    rw [hy', hφf.eq_of_nhds]
    exact hy
  rw [← (hφf.iteratedFDeriv ℝ 2).eq_of_nhds]
  exact iteratedFDeriv_two_nonneg_of_isLocalMin hφ hφmin v

/-- At a local minimum of a globally `C²` function on a finite-dimensional real inner product
space, the Laplacian is nonnegative. -/
theorem laplacian_nonneg_of_isLocalMin [FiniteDimensional ℝ F] {f : F → ℝ} {x : F}
    (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x) : 0 ≤ Δ f x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact Finset.sum_nonneg fun i _ ↦ iteratedFDeriv_two_nonneg_of_isLocalMin hf hmin _

/-- At a local minimum of a function `C²` at the point, the Laplacian is nonnegative. -/
theorem laplacian_nonneg_of_isLocalMin' [FiniteDimensional ℝ F] {f : F → ℝ} {x : F}
    (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) : 0 ≤ Δ f x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact Finset.sum_nonneg fun i _ ↦ iteratedFDeriv_two_nonneg_of_isLocalMin' hf hmin _

/-- At a local maximum of a function `C²` at the point, the Laplacian is nonpositive. -/
theorem laplacian_nonpos_of_isLocalMax' [FiniteDimensional ℝ F] {f : F → ℝ} {x : F}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) : Δ f x ≤ 0 := by
  have h := laplacian_nonneg_of_isLocalMin' hf.neg hmax.neg
  have := congrFun (laplacian_neg (f := f)) x
  simp only [Pi.neg_apply] at this
  rw [show (fun y ↦ -f y) = -f from rfl, this] at h
  linarith

end SecondOrder

/-! ### The one-sided first-derivative test -/

/-- If `h` is differentiable at `s` and `h(s) ≤ h(s')` for `s' ≤ s` near
`s`, then `h'(s) ≤ 0`. -/
theorem deriv_nonpos_of_isLocalMinOn_Iic {h : ℝ → ℝ} {s : ℝ} (hd : DifferentiableAt ℝ h s)
    (hmin : IsLocalMinOn h (Iic s) s) : deriv h s ≤ 0 := by
  have hmem : (-1 : ℝ) ∈ posTangentConeAt (Iic s) s := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [segment_symm, segment_eq_Icc (by linarith)]
    exact Icc_subset_Iic_self
  have := hmin.hasFDerivWithinAt_nonneg hd.hasDerivAt.hasFDerivAt.hasFDerivWithinAt hmem
  simpa using this

/-! ### Slice forms -/

section SpaceTime

variable {φ ψ u : E d × ℝ → ℝ} {p : E d × ℝ}

/-- If the spatial slice `y ↦ φ (y, p.2)` has a local minimum at `p.1`, then `Δₓφ(p) ≥ 0`
(with the slice `C²` at the point). -/
theorem lapₓ_nonneg_of_isLocalMin (hφ : ContDiffAt ℝ 2 (fun y ↦ φ (y, p.2)) p.1)
    (hmin : IsLocalMin (fun y ↦ φ (y, p.2)) p.1) : 0 ≤ lapₓ φ p :=
  laplacian_nonneg_of_isLocalMin' hφ hmin

/-- If the spatial slice `y ↦ φ (y, p.2)` has a local minimum at `p.1`, then `∇ₓφ(p) = 0`. -/
theorem gradₓ_eq_zero_of_isLocalMin (hmin : IsLocalMin (fun y ↦ φ (y, p.2)) p.1) :
    gradₓ φ p = 0 := by
  simp [gradₓ, gradient, hmin.fderiv_eq_zero]

/-- If `u ≤ ψ` on the spatial slice near `p.1` with equality at `p`, and both slices are `C²` at
`p.1`, then `Δₓu(p) ≤ Δₓψ(p)`. -/
theorem lapₓ_le_of_touchesAbove (hψ : ContDiffAt ℝ 2 (fun y ↦ ψ (y, p.2)) p.1)
    (hu : ContDiffAt ℝ 2 (fun y ↦ u (y, p.2)) p.1) (heq : u p = ψ p)
    (hle : ∀ᶠ y in 𝓝 p.1, u (y, p.2) ≤ ψ (y, p.2)) : lapₓ u p ≤ lapₓ ψ p := by
  have hmin : IsLocalMin (fun y ↦ ψ (y, p.2) - u (y, p.2)) p.1 := by
    filter_upwards [hle] with y hy
    simp only [Prod.mk.eta, heq, sub_self]
    linarith
  have h := laplacian_nonneg_of_isLocalMin' (hψ.sub hu) hmin
  have hsub := hψ.laplacian_sub hu
  simp only [lapₓ] at *
  change 0 ≤ Δ ((fun y ↦ ψ (y, p.2)) - fun y ↦ u (y, p.2)) p.1 at h
  rw [hsub] at h
  linarith

/-- If `u ≤ ψ` on the spatial slice near `p.1` with equality at `p`, and both slices are
differentiable at `p.1`, then `∇ₓu(p) = ∇ₓψ(p)`. -/
theorem gradₓ_eq_of_touchesAbove (hψ : DifferentiableAt ℝ (fun y ↦ ψ (y, p.2)) p.1)
    (hu : DifferentiableAt ℝ (fun y ↦ u (y, p.2)) p.1) (heq : u p = ψ p)
    (hle : ∀ᶠ y in 𝓝 p.1, u (y, p.2) ≤ ψ (y, p.2)) : gradₓ u p = gradₓ ψ p := by
  have hmin : IsLocalMin (fun y ↦ ψ (y, p.2) - u (y, p.2)) p.1 := by
    filter_upwards [hle] with y hy
    simp only [Prod.mk.eta, heq, sub_self]
    linarith
  have h0 := hmin.fderiv_eq_zero
  rw [fderiv_fun_sub hψ hu, sub_eq_zero] at h0
  simp only [gradₓ, gradient, h0]

/-- **One-sided time test.** If the time slices of `ψ` and `u` are differentiable at
`p.2` and `ψ - u` has a local minimum at `p.2` among earlier times, then `∂ₜψ(p) ≤ ∂ₜu(p)`. -/
theorem dₜ_le_of_isLocalMinOn_Iic (hψ : DifferentiableAt ℝ (fun s ↦ ψ (p.1, s)) p.2)
    (hu : DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2)
    (hmin : IsLocalMinOn (fun s ↦ ψ (p.1, s) - u (p.1, s)) (Iic p.2) p.2) :
    dₜ ψ p ≤ dₜ u p := by
  have h := deriv_nonpos_of_isLocalMinOn_Iic (hψ.fun_sub hu) hmin
  rw [deriv_fun_sub hψ hu] at h
  simp only [dₜ]
  linarith

/-- **Two-sided time test.** If the time slices of `ψ` and `u` are differentiable at
`p.2` and `ψ - u` has a local minimum at `p.2`, then `∂ₜψ(p) = ∂ₜu(p)`. -/
theorem dₜ_eq_of_isLocalMin (hψ : DifferentiableAt ℝ (fun s ↦ ψ (p.1, s)) p.2)
    (hu : DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2)
    (hmin : IsLocalMin (fun s ↦ ψ (p.1, s) - u (p.1, s)) p.2) : dₜ ψ p = dₜ u p := by
  have h := hmin.deriv_eq_zero
  rw [deriv_fun_sub hψ hu, sub_eq_zero] at h
  exact h

/-- If `s ↦ φ (p.1, s)` has a minimum at `p.2` among earlier times, then `∂ₜφ(p) ≤ 0`
(with the slice differentiable at `p.2`). -/
theorem dₜ_nonpos_of_isLocalMinOn_Iic (hφ : DifferentiableAt ℝ (fun s ↦ φ (p.1, s)) p.2)
    (hmin : IsLocalMinOn (fun s ↦ φ (p.1, s)) (Iic p.2) p.2) : dₜ φ p ≤ 0 :=
  deriv_nonpos_of_isLocalMinOn_Iic hφ hmin

end SpaceTime

end ParabolicBasic
