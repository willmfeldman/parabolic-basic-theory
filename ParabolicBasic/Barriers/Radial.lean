/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Radial calculus: gradient and Laplacian of `f (ψ x)` and of `f ‖x - z‖`

On a finite-dimensional real inner product space `F`:

* `laplacian_comp_real`: the chain rule for the Laplacian,
  `Δ (f ∘ ψ) = f''(ψ) ‖∇ψ‖² + f'(ψ) Δψ` for `f : ℝ → ℝ` and `ψ : F → ℝ` of class `C²`;
  `gradient_comp_real`: `∇ (f ∘ ψ) = f'(ψ) ∇ψ`;
* `laplacian_norm_sub_sq`, `gradient_norm_sub_sq`: `Δ ‖x - z‖² = 2 dim F`, `∇ ‖x - z‖² = 2 (x - z)`;
* `laplacian_norm_sub`, `gradient_norm_sub`: for `x ≠ z`, `Δ ‖x - z‖ = (dim F - 1) / ‖x - z‖` and
  `∇ ‖x - z‖ = (x - z) / ‖x - z‖`;
* `laplacian_radial`, `gradient_radial`, `norm_gradient_radial`: for `x ≠ z` and `r = ‖x - z‖`,
  `Δ f(‖x - z‖) = f''(r) + (dim F - 1) f'(r) / r` and `|∇ f(‖x - z‖)| = |f'(r)|`;
* `laplacian_inv_norm_sub_sq_pow`: the Laplacian of the lateral-barrier profile
  `(‖x - z‖²)⁻¹ ^ m`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian ContDiff RealInnerProductSpace

namespace ParabolicBasic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Chain rule -/

section Chain

variable {f : ℝ → ℝ} {ψ : F → ℝ} {x : F}

/-- The Laplacian as the trace of the second derivative `fderiv (fderiv ψ)` along an
orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv (ψ : F → ℝ) (x : F) :
    Δ ψ x = ∑ i, fderiv ℝ (fderiv ℝ ψ) x (stdOrthonormalBasis ℝ F i)
      (stdOrthonormalBasis ℝ F i) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_two_apply]

theorem sum_fderiv_sq_eq_norm_gradient_sq (ψ : F → ℝ) (x : F) :
    ∑ i, fderiv ℝ ψ x (stdOrthonormalBasis ℝ F i) * fderiv ℝ ψ x (stdOrthonormalBasis ℝ F i) =
      ‖∇ ψ x‖ ^ 2 := by
  have h : ∀ v : F, fderiv ℝ ψ x v = ⟪∇ ψ x, v⟫ := fun v ↦ by
    simp [gradient, toDual_symm_apply]
  simp_rw [h]
  conv_lhs => enter [2, i, 2]; rw [real_inner_comm]
  rw [(stdOrthonormalBasis ℝ F).sum_inner_mul_inner, real_inner_self_eq_norm_sq]

/-- **Gradient chain rule** `∇ (f ∘ ψ) = f'(ψ) ∇ψ`. -/
theorem gradient_comp_real (hf : DifferentiableAt ℝ f (ψ x)) (hψ : DifferentiableAt ℝ ψ x) :
    ∇ (fun y ↦ f (ψ y)) x = deriv f (ψ x) • ∇ ψ x := by
  have H : HasFDerivAt (fun y ↦ f (ψ y)) (deriv f (ψ x) • fderiv ℝ ψ x) x :=
    hf.hasDerivAt.comp_hasFDerivAt x hψ.hasFDerivAt
  simp only [gradient, H.fderiv, map_smul]

/-- **Laplacian chain rule** `Δ (f ∘ ψ) = f''(ψ) ‖∇ψ‖² + f'(ψ) Δψ`. -/
theorem laplacian_comp_real (hf : ContDiffAt ℝ 2 f (ψ x)) (hψ : ContDiffAt ℝ 2 ψ x) :
    Δ (fun y ↦ f (ψ y)) x =
      deriv (deriv f) (ψ x) * ‖∇ ψ x‖ ^ 2 + deriv f (ψ x) * Δ ψ x := by
  have hψ' : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 ψ y := hψ.eventually (by simp)
  have hf' : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (ψ y) :=
    hψ.continuousAt.eventually (hf.eventually (by simp))
  have hD : fderiv ℝ (fun y ↦ f (ψ y)) =ᶠ[𝓝 x] fun y ↦ deriv f (ψ y) • fderiv ℝ ψ y := by
    filter_upwards [hψ', hf'] with y h1 h2
    exact ((h2.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y
      (h1.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hdf : HasDerivAt (deriv f) (deriv (deriv f) (ψ x)) (ψ x) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) (ψ x) := hf.fderiv_right (by norm_num)
    have h2 : DifferentiableAt ℝ (fun s ↦ fderiv ℝ f s 1) (ψ x) :=
      (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
    exact h2.hasDerivAt
  have hdψ : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
    (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have hprod := (hdf.comp_hasFDerivAt x hψd).smul hdψ
  have hDD : fderiv ℝ (fderiv ℝ fun y ↦ f (ψ y)) x = _ := hD.fderiv_eq.trans hprod.fderiv
  rw [laplacian_eq_sum_fderiv_fderiv, laplacian_eq_sum_fderiv_fderiv, hDD,
    ← sum_fderiv_sq_eq_norm_gradient_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  ring

end Chain

/-! ### The squared distance and the distance -/

section Distance

variable (z : F)

omit [FiniteDimensional ℝ F] in
theorem hasFDerivAt_norm_sub_sq (y : F) :
    HasFDerivAt (fun y : F ↦ ‖y - z‖ ^ 2) (((2 : ℝ) • innerSL ℝ (E := F)) (y - z)) y := by
  refine ((hasFDerivAt_id y).sub_const z).norm_sq.congr_fderiv ?_
  ext v
  simp

omit [FiniteDimensional ℝ F] in
theorem fderiv_norm_sub_sq :
    fderiv ℝ (fun y : F ↦ ‖y - z‖ ^ 2) = fun y ↦ ((2 : ℝ) • innerSL ℝ (E := F)) (y - z) :=
  funext fun y ↦ (hasFDerivAt_norm_sub_sq z y).fderiv

/-- `∇ ‖x - z‖² = 2 (x - z)`. -/
theorem gradient_norm_sub_sq (x : F) : ∇ (fun y : F ↦ ‖y - z‖ ^ 2) x = (2 : ℝ) • (x - z) := by
  refine HasGradientAt.gradient (hasGradientAt_iff_hasFDerivAt.2 ?_)
  convert hasFDerivAt_norm_sub_sq z x using 1
  ext v
  simp [toDual_apply_apply]

/-- `Δ ‖x - z‖² = 2 dim F`. -/
theorem laplacian_norm_sub_sq (x : F) :
    Δ (fun y : F ↦ ‖y - z‖ ^ 2) x = 2 * Module.finrank ℝ F := by
  have H : HasFDerivAt (fun y : F ↦ ((2 : ℝ) • innerSL ℝ (E := F)) (y - z))
      ((2 : ℝ) • innerSL ℝ (E := F)) x := by
    have := ((2 : ℝ) • innerSL ℝ (E := F)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
    rwa [ContinuousLinearMap.comp_id] at this
  rw [laplacian_eq_sum_fderiv_fderiv, fderiv_norm_sub_sq, H.fderiv]
  -- restate to normalize the instance path of the codomain `F →L[ℝ] ℝ`
  change ∑ i, (((2 : ℝ) • innerSL ℝ (E := F)) (stdOrthonormalBasis ℝ F i))
      (stdOrthonormalBasis ℝ F i) = _
  simp
  ring

variable {z}

omit [FiniteDimensional ℝ F] in
theorem contDiffAt_norm_sub {n : WithTop ℕ∞} {x : F} (hx : x ≠ z) :
    ContDiffAt ℝ n (fun y : F ↦ ‖y - z‖) x :=
  (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)

/-- `∇ ‖x - z‖ = (x - z) / ‖x - z‖` for `x ≠ z`. -/
theorem gradient_norm_sub {x : F} (hx : x ≠ z) :
    ∇ (fun y : F ↦ ‖y - z‖) x = ‖x - z‖⁻¹ • (x - z) := by
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hfun : (fun y : F ↦ ‖y - z‖) = fun y ↦ √(‖y - z‖ ^ 2) :=
    funext fun y ↦ (Real.sqrt_sq (norm_nonneg _)).symm
  have hs : ‖x - z‖ ^ 2 ≠ 0 := by positivity
  rw [hfun, gradient_comp_real (f := fun s ↦ √s) (ψ := fun y ↦ ‖y - z‖ ^ 2)
    (Real.hasDerivAt_sqrt hs).differentiableAt
    ((hasFDerivAt_norm_sub_sq z x).differentiableAt), (Real.hasDerivAt_sqrt hs).deriv,
    gradient_norm_sub_sq, Real.sqrt_sq (norm_nonneg _), smul_smul]
  congr 1
  field_simp

theorem norm_gradient_norm_sub {x : F} (hx : x ≠ z) : ‖∇ (fun y : F ↦ ‖y - z‖) x‖ = 1 := by
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  rw [gradient_norm_sub hx, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']

/-- `Δ ‖x - z‖ = (dim F - 1) / ‖x - z‖` for `x ≠ z`. -/
theorem laplacian_norm_sub {x : F} (hx : x ≠ z) :
    Δ (fun y : F ↦ ‖y - z‖) x = ((Module.finrank ℝ F : ℝ) - 1) / ‖x - z‖ := by
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hsq : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ 2) ‖x - z‖ := contDiffAt_id.pow 2
  have H := laplacian_comp_real (f := fun s : ℝ ↦ s ^ 2) (ψ := fun y : F ↦ ‖y - z‖) hsq
    (contDiffAt_norm_sub (n := 2) hx)
  have hd1 : deriv (fun s : ℝ ↦ s ^ 2) = fun s ↦ 2 * s := funext fun s ↦ by simp
  have hd2 : deriv (fun s : ℝ ↦ 2 * s) = fun _ ↦ 2 := funext fun s ↦
    ((hasDerivAt_id' s).const_mul (2 : ℝ)).deriv.trans (mul_one 2)
  rw [hd1, hd2, norm_gradient_norm_sub hx, laplacian_norm_sub_sq] at H
  field_simp
  linarith

end Distance

/-! ### Radial functions -/

section Radial

variable {f : ℝ → ℝ} {x z : F}

/-- **Radial gradient.** `∇ f(‖x - z‖) = f'(r) (x - z) / r`, `r = ‖x - z‖ > 0`. -/
theorem gradient_radial (hf : DifferentiableAt ℝ f ‖x - z‖) (hx : x ≠ z) :
    ∇ (fun y : F ↦ f ‖y - z‖) x = deriv f ‖x - z‖ • ‖x - z‖⁻¹ • (x - z) := by
  rw [gradient_comp_real (ψ := fun y : F ↦ ‖y - z‖) hf
    ((contDiffAt_norm_sub (n := 1) hx).differentiableAt one_ne_zero), gradient_norm_sub hx]

theorem norm_gradient_radial (hf : DifferentiableAt ℝ f ‖x - z‖) (hx : x ≠ z) :
    ‖∇ (fun y : F ↦ f ‖y - z‖) x‖ = |deriv f ‖x - z‖| := by
  rw [gradient_comp_real (ψ := fun y : F ↦ ‖y - z‖) hf
    ((contDiffAt_norm_sub (n := 1) hx).differentiableAt one_ne_zero), norm_smul,
    norm_gradient_norm_sub hx, mul_one, Real.norm_eq_abs]

/-- **Radial Laplacian.** `Δ f(‖x - z‖) = f''(r) + (dim F - 1) f'(r) / r`, `r = ‖x - z‖ > 0`. -/
theorem laplacian_radial (hf : ContDiffAt ℝ 2 f ‖x - z‖) (hx : x ≠ z) :
    Δ (fun y : F ↦ f ‖y - z‖) x =
      deriv (deriv f) ‖x - z‖ +
        ((Module.finrank ℝ F : ℝ) - 1) * deriv f ‖x - z‖ / ‖x - z‖ := by
  rw [laplacian_comp_real (ψ := fun y : F ↦ ‖y - z‖) hf (contDiffAt_norm_sub hx),
    norm_gradient_norm_sub hx,
    laplacian_norm_sub hx]
  ring

end Radial

/-! ### Affine reparametrizations and linear combinations -/

section Affine

theorem deriv_comp_mul_add (f : ℝ → ℝ) (a b : ℝ) :
    deriv (fun r ↦ f (a * r + b)) = fun r ↦ a * deriv f (a * r + b) := by
  funext r
  have := deriv_comp_mul_left (f := fun u ↦ f (u + b)) (c := a) (x := r)
  simp only [smul_eq_mul, deriv_comp_add_const] at this
  exact this

theorem deriv_deriv_comp_mul_add (f : ℝ → ℝ) (a b : ℝ) :
    deriv (deriv fun r ↦ f (a * r + b)) = fun r ↦ a ^ 2 * deriv (deriv f) (a * r + b) := by
  rw [deriv_comp_mul_add]
  funext r
  rw [deriv_const_mul_field', deriv_comp_mul_add]
  ring

theorem contDiffAt_comp_mul_add {n : WithTop ℕ∞} {f : ℝ → ℝ} {a b r : ℝ}
    (hf : ContDiffAt ℝ n f (a * r + b)) : ContDiffAt ℝ n (fun r ↦ f (a * r + b)) r :=
  hf.comp r ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)

/-- `Δ (a g + c) = a Δ g`. -/
theorem laplacian_const_mul_add_const {g : F → ℝ} {x : F} (hg : ContDiffAt ℝ 2 g x) (a c : ℝ) :
    Δ (fun y ↦ a * g y + c) x = a * Δ g x := by
  have H := laplacian_comp_real (f := fun s ↦ a * s + c) (ψ := g)
    (contDiffAt_comp_mul_add (f := id) contDiffAt_id) hg
  have h1 := deriv_comp_mul_add id a c
  have h2 := deriv_deriv_comp_mul_add id a c
  simp only [id] at h1 h2
  rw [H, h2, h1]
  simp

/-- `∇ (a g + c) = a ∇ g`. -/
theorem gradient_const_mul_add_const {g : F → ℝ} {x : F} (hg : DifferentiableAt ℝ g x)
    (a c : ℝ) : ∇ (fun y ↦ a * g y + c) x = a • ∇ g x := by
  have H := gradient_comp_real (f := fun s ↦ a * s + c) (ψ := g)
    ((contDiffAt_comp_mul_add (n := 1) (f := id) contDiffAt_id).differentiableAt one_ne_zero) hg
  have h1 := deriv_comp_mul_add id a c
  simp only [id] at h1
  rw [H, h1]
  simp

end Affine

/-! ### Inverse powers of the squared distance -/

section InvPow

variable {z x : F}

omit [FiniteDimensional ℝ F] in
theorem contDiff_norm_sub_sq (z : F) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y : F ↦ ‖y - z‖ ^ 2) :=
  (contDiff_id.sub contDiff_const).norm_sq ℝ

theorem norm_gradient_norm_sub_sq_sq (x : F) :
    ‖∇ (fun y : F ↦ ‖y - z‖ ^ 2) x‖ ^ 2 = 4 * ‖x - z‖ ^ 2 := by
  rw [gradient_norm_sub_sq, norm_smul, mul_pow]
  norm_num

theorem inv_pow_eq_zpow (s : ℝ) (m : ℕ) : (s⁻¹) ^ m = s ^ (-(m : ℤ)) := by
  rw [zpow_neg, zpow_natCast, inv_pow]

omit [FiniteDimensional ℝ F] in
/-- The profile `(‖x - z‖²)⁻ᵐ` is `C^∞` away from `z`. -/
theorem contDiffAt_inv_norm_sub_sq_pow {n : WithTop ℕ∞} (m : ℕ) (hx : x ≠ z) :
    ContDiffAt ℝ n (fun y : F ↦ ((‖y - z‖ ^ 2)⁻¹) ^ m) x := by
  have hs0 : ‖x - z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hx))
  exact ((contDiffAt_inv ℝ hs0).comp x (contDiff_norm_sub_sq z).contDiffAt).pow m

/-- **Laplacian of an inverse power of the squared distance.** For `x ≠ z`,
`Δ (‖x - z‖²)⁻ᵐ = 2m (2m + 2 - dim F) (‖x - z‖²)^{-(m+1)}`. (With `m = d = dim F` the coefficient
is `2d (d + 2)`: this is the lateral barrier profile `‖x - y‖^{-k}`, `k = 2d`, of
`isSepBarrier_lateral`.) -/
theorem laplacian_inv_norm_sub_sq_pow (m : ℕ) (hx : x ≠ z) :
    Δ (fun y : F ↦ ((‖y - z‖ ^ 2)⁻¹) ^ m) x =
      2 * m * (2 * m + 2 - Module.finrank ℝ F) * ((‖x - z‖ ^ 2)⁻¹) ^ (m + 1) := by
  have hs0 : ‖x - z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hx))
  have hf : ContDiffAt ℝ 2 (fun t : ℝ ↦ t ^ (-(m : ℤ))) (‖x - z‖ ^ 2) := by
    have : (fun t : ℝ ↦ t ^ (-(m : ℤ))) = fun t ↦ (t⁻¹) ^ m :=
      funext fun t ↦ (inv_pow_eq_zpow t m).symm
    rw [this]
    exact (contDiffAt_inv ℝ hs0).pow m
  have H := laplacian_comp_real (f := fun t : ℝ ↦ t ^ (-(m : ℤ)))
    (ψ := fun y : F ↦ ‖y - z‖ ^ 2) (x := x) hf (contDiff_norm_sub_sq z).contDiffAt
  beta_reduce at H
  have h1 : (fun y : F ↦ ((‖y - z‖ ^ 2)⁻¹) ^ m) = fun y ↦ (‖y - z‖ ^ 2) ^ (-(m : ℤ)) :=
    funext fun y ↦ inv_pow_eq_zpow _ m
  rw [h1, H, deriv_zpow', deriv_const_mul_field', deriv_zpow', norm_gradient_norm_sub_sq_sq,
    laplacian_norm_sub_sq]
  set s := ‖x - z‖ ^ 2 with hs
  have e1 : s ^ (-(m : ℤ) - 1) = (s⁻¹) ^ (m + 1) := by
    rw [inv_pow_eq_zpow]; push_cast; ring_nf
  have e2 : s ^ (-(m : ℤ) - 1 - 1) * s = (s⁻¹) ^ (m + 1) := by
    rw [show -(m : ℤ) - 1 - 1 = -((m + 2 : ℕ) : ℤ) by push_cast; ring, ← inv_pow_eq_zpow,
      pow_succ, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have e3 : (s⁻¹) ^ (m + 2) * s = (s⁻¹) ^ (m + 1) := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  calc _ = ((-(m : ℤ) : ℤ) : ℝ) * (((-(m : ℤ) - 1 : ℤ) : ℝ) * 4) * (s ^ (-(m : ℤ) - 1 - 1) * s)
        + ((-(m : ℤ) : ℤ) : ℝ) * (2 * Module.finrank ℝ F) * s ^ (-(m : ℤ) - 1) := by ring
    _ = _ := by rw [e1, e2]; push_cast; ring

end InvPow

end ParabolicBasic
