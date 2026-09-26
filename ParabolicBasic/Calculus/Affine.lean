/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The parabolic affine map

The parabolic affine map `parAffine x₀ t₀ r : q ↦ (x₀ + r q.1, t₀ + r² q.2)` (translation and
parabolic scaling), its inverse, and the chain rules:

* `dₜ_comp_parAffine`: `dₜ (ψ ∘ A) q = r² dₜ ψ (A q)` (no regularity needed);
* `lapₓ_comp_parAffine`: `lapₓ (ψ ∘ A) q = r² lapₓ ψ (A q)` for `C²` `ψ`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-- The parabolic affine map `q ↦ (x₀ + r q.1, t₀ + r² q.2)` (translation and parabolic scaling). -/
def parAffine (x₀ : E d) (t₀ r : ℝ) (q : E d × ℝ) : E d × ℝ := (x₀ + r • q.1, t₀ + r ^ 2 * q.2)

@[simp] theorem parAffine_fst (x₀ : E d) (t₀ r : ℝ) (q : E d × ℝ) :
    (parAffine x₀ t₀ r q).1 = x₀ + r • q.1 := rfl

@[simp] theorem parAffine_snd (x₀ : E d) (t₀ r : ℝ) (q : E d × ℝ) :
    (parAffine x₀ t₀ r q).2 = t₀ + r ^ 2 * q.2 := rfl

theorem contDiff_parAffine {n : WithTop ℕ∞} (x₀ : E d) (t₀ r : ℝ) :
    ContDiff ℝ n (parAffine x₀ t₀ r) :=
  (contDiff_const.add (contDiff_fst.const_smul r)).prodMk
    (contDiff_const.add (contDiff_const.mul contDiff_snd))

theorem continuous_parAffine (x₀ : E d) (t₀ r : ℝ) : Continuous (parAffine x₀ t₀ r) :=
  (contDiff_parAffine (n := 0) x₀ t₀ r).continuous

/-- The inverse of `parAffine x₀ t₀ r` (for `r ≠ 0`) is again a parabolic affine map. -/
theorem parAffine_parAffine_inv {r : ℝ} (hr : r ≠ 0) (x₀ : E d) (t₀ : ℝ) (q : E d × ℝ) :
    parAffine x₀ t₀ r (parAffine (-(r⁻¹ • x₀)) (-(r⁻¹ ^ 2 * t₀)) r⁻¹ q) = q := by
  obtain ⟨x, t⟩ := q
  simp only [parAffine, Prod.mk.injEq, smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hr, one_smul]
  refine ⟨by abel, ?_⟩
  field_simp
  ring

theorem parAffine_inv_parAffine {r : ℝ} (hr : r ≠ 0) (x₀ : E d) (t₀ : ℝ) (q : E d × ℝ) :
    parAffine (-(r⁻¹ • x₀)) (-(r⁻¹ ^ 2 * t₀)) r⁻¹ (parAffine x₀ t₀ r q) = q := by
  obtain ⟨x, t⟩ := q
  simp only [parAffine, Prod.mk.injEq, smul_add, smul_smul, inv_mul_cancel₀ hr, one_smul]
  refine ⟨by abel, ?_⟩
  field_simp
  ring

/-- **Chain rule**, time part: `dₜ (ψ ∘ A) q = r² dₜ ψ (A q)`. No regularity needed. -/
theorem dₜ_comp_parAffine (ψ : E d × ℝ → ℝ) (x₀ : E d) (t₀ r : ℝ) (q : E d × ℝ) :
    dₜ (ψ ∘ parAffine x₀ t₀ r) q = r ^ 2 * dₜ ψ (parAffine x₀ t₀ r q) := by
  simp only [dₜ, Function.comp_def, parAffine]
  have := deriv_comp_mul_left (r ^ 2) (fun s ↦ ψ (x₀ + r • q.1, t₀ + s)) q.2
  simp only [smul_eq_mul] at this
  rw [this, deriv_comp_const_add (f := fun s ↦ ψ (x₀ + r • q.1, s))]

/-- Laplacian of a composition with `y ↦ x₀ + r • y`. -/
theorem laplacian_comp_const_add_smul {g : E d → ℝ} (hg : ContDiff ℝ 2 g) (x₀ : E d) (r : ℝ)
    (y : E d) : Δ (fun y ↦ g (x₀ + r • y)) y = r ^ 2 * Δ g (x₀ + r • y) := by
  set L : E d →L[ℝ] E d := r • ContinuousLinearMap.id ℝ (E d)
  have hh : ContDiff ℝ 2 (fun z ↦ g (x₀ + z)) := hg.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun y ↦ g (x₀ + r • y)) = (fun z ↦ g (x₀ + z)) ∘ L := by
    funext y; simp [L]
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right L hh y le_rfl,
    iteratedFDeriv_comp_add_left]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hL : (fun j ↦ L (![(stdOrthonormalBasis ℝ (E d)) i, (stdOrthonormalBasis ℝ (E d)) i] j)) =
      fun j ↦ (fun _ ↦ r) j • ![(stdOrthonormalBasis ℝ (E d)) i,
        (stdOrthonormalBasis ℝ (E d)) i] j := by
    funext j; simp [L]
  rw [hL, ContinuousMultilinearMap.map_smul_univ]
  simp [L, sq]

/-- **Chain rule**, space part: `lapₓ (ψ ∘ A) q = r² lapₓ ψ (A q)` for `C²` `ψ`. -/
theorem lapₓ_comp_parAffine {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (x₀ : E d) (t₀ r : ℝ)
    (q : E d × ℝ) :
    lapₓ (ψ ∘ parAffine x₀ t₀ r) q = r ^ 2 * lapₓ ψ (parAffine x₀ t₀ r q) := by
  simp only [lapₓ, Function.comp_def, parAffine]
  exact laplacian_comp_const_add_smul (hψ.comp (contDiff_id.prodMk contDiff_const)) x₀ r q.1

end ParabolicBasic
