/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Transport.Equiv

/-!
# Calculus bridge: `dₜ`, `lapₓ` as entries of the Fréchet jet on `Point (d + 1)`

For `ψ : E d × ℝ → ℝ` and `ψ♯ = toPointFun ψ = ψ ∘ e⁻¹`:

* `ψ` is `Cⁿ` iff `ψ♯` is;
* `dₜ ψ p = Dψ♯(e p)[ε_t]`;
* `lapₓ ψ p = ∑_{i<d} D²ψ♯(e p)[ε_{castSucc i}, ε_{castSucc i}]`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-- `ψ` is `Cⁿ` iff `ψ♯ = ψ ∘ e⁻¹` is. -/
theorem contDiff_toPointFun_iff {n : WithTop ℕ∞} {ψ : E d × ℝ → ℝ} :
    ContDiff ℝ n (toPointFun ψ) ↔ ContDiff ℝ n ψ :=
  (spaceTimeEquiv d).symm.contDiff_comp_iff

/-- `ψ♯ ∘ e = ψ`. -/
theorem toPointFun_comp_spaceTimeEquiv (ψ : E d × ℝ → ℝ) :
    toPointFun ψ ∘ spaceTimeEquiv d = ψ := by
  funext p; simp only [Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **Time derivative**: `dₜ ψ p = Dψ♯(e p)[ε_t]`. -/
theorem dₜ_eq_fderiv_toPointFun {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (p : E d × ℝ) :
    dₜ ψ p = fderiv ℝ (toPointFun ψ) (spaceTimeEquiv d p)
      (ViscositySolns.coordinateVector (Fin.last d)) := by
  have hφ : ContDiff ℝ 1 (toPointFun ψ) := contDiff_toPointFun_iff.2 hψ
  have hγ : HasDerivAt (fun s : ℝ ↦ spaceTimeEquiv d (p.1, s)) (spaceTimeEquiv d (0, 1)) p.2 :=
    (spaceTimeEquiv d).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have h := ((hφ.differentiable one_ne_zero) (spaceTimeEquiv d p)).hasFDerivAt.comp_hasDerivAt
    p.2 (by simpa only [Prod.mk.eta] using hγ)
  have hfun : (fun s ↦ ψ (p.1, s)) = toPointFun ψ ∘ fun s ↦ spaceTimeEquiv d (p.1, s) := by
    funext s
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [← spaceTimeEquiv_time]
  unfold dₜ
  rw [hfun, h.deriv]

/-- **Spatial Laplacian**:
`lapₓ ψ p = ∑_{i<d} D²ψ♯(e p)[ε_{castSucc i}, ε_{castSucc i}]`. The slice `y ↦ ψ (y, t)` is
`ψ♯ ∘ (· + e (0, t)) ∘ L` with `L y = e (y, 0)`, and `L bᵢ = ε_{castSucc i}`. -/
theorem lapₓ_eq_sum_fderiv_fderiv_toPointFun {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (p : E d × ℝ) :
    lapₓ ψ p = ∑ i : Fin d, fderiv ℝ (fderiv ℝ (toPointFun ψ)) (spaceTimeEquiv d p)
      (ViscositySolns.coordinateVector i.castSucc)
      (ViscositySolns.coordinateVector i.castSucc) := by
  set φ := toPointFun ψ with hφdef
  have hφ : ContDiff ℝ 2 φ := contDiff_toPointFun_iff.2 hψ
  set L : E d →L[ℝ] ViscositySolns.Point (d + 1) :=
    (spaceTimeEquiv d : E d × ℝ →L[ℝ] _).comp (ContinuousLinearMap.inl ℝ (E d) ℝ) with hL
  set c : ViscositySolns.Point (d + 1) := spaceTimeEquiv d (0, p.2) with hc
  have hLc : ∀ y, L y + c = spaceTimeEquiv d (y, p.2) := by
    intro y
    simp only [hL, hc, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearEquiv.coe_coe, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hslice : (fun y ↦ ψ (y, p.2)) = (fun w ↦ φ (w + c)) ∘ L := by
    funext y
    simp only [Function.comp_apply, hLc, hφdef,
      ContinuousLinearEquiv.symm_apply_apply]
  have hh : ContDiff ℝ 2 (fun w ↦ φ (w + c)) := hφ.comp (contDiff_id.add contDiff_const)
  unfold lapₓ
  rw [hslice, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [L.iteratedFDeriv_comp_right hh _ le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right,
    iteratedFDeriv_two_apply]
  have hb : L (EuclideanSpace.basisFun (Fin d) ℝ i) =
      ViscositySolns.coordinateVector i.castSucc := by
    rw [EuclideanSpace.basisFun_apply, ← spaceTimeEquiv_space_basis]
    rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hb, hLc]

end ParabolicBasic
