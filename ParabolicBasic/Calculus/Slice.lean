/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Slice calculus and locality

For a space-time function `φ : E d × ℝ → ℝ`:

* `exists_contDiff_eventuallyEq`: a function `Cⁿ` on an open set `N ∋ p` agrees near `p` with a
  global `Cⁿ` function (product with a smooth bump), for any `n : ℕ∞`, with a version for any
  space with smooth bumps (`exists_contDiff_eventuallyEq_of_contDiffOn`) and a pointwise version
  (`ContDiffAt.exists_contDiff_eventuallyEq`);
* `dₜ_congr_nhds`, `lapₓ_congr_nhds`, `gradₓ_congr_nhds`: the operators depend only on the germ;
* formulas in terms of Fréchet derivatives (`dₜ_eq_fderiv`, `gradₓ_eq_fderiv`,
  `lapₓ_eq_iteratedFDeriv`) and continuity (`continuous_dₜ`, `continuous_gradₓ`,
  `continuous_lapₓ`);
* linearity (`dₜ_add`, `dₜ_sub`, `dₜ_const_mul`, `dₜ_add_const`, `dₜ_neg`, and the same for
  `lapₓ`, `gradₓ`), and its local form for functions `C²` near the point
  (`dₜ_sub_lapₓ_add_mul_add_of_contDiffOn`, `dₜ_sub_lapₓ_sub_of_contDiffOn`).
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Smooth extension from a neighbourhood -/

section Extension

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [HasContDiffBump X]

/-- A function `Cⁿ` on an open set `N ∋ p` of a normed space with smooth bumps agrees near `p`
with a global `Cⁿ` function (its product with a smooth bump supported in `N`). -/
theorem exists_contDiff_eventuallyEq_of_contDiffOn {n : ℕ∞} {ψ : X → ℝ} {N : Set X}
    (hN : IsOpen N) {p : X} (hp : p ∈ N) (hψ : ContDiffOn ℝ n ψ N) :
    ∃ φ : X → ℝ, ContDiff ℝ n φ ∧ φ =ᶠ[𝓝 p] ψ := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hN p hp
  let χ : ContDiffBump p := ⟨R / 4, R / 2, by positivity, by linarith⟩
  refine ⟨fun q ↦ χ q * ψ q, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun q ↦ ?_
    by_cases hq : q ∈ N
    · exact χ.contDiff.contDiffAt.mul (hψ.contDiffAt (hN.mem_nhds hq))
    · have hqs : q ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        intro hq'
        exact hq (hball (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hq') (by
          change R / 2 < R; linarith))))
      have h0 : (fun q ↦ χ q * ψ q) =ᶠ[𝓝 q] fun _ ↦ 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hqs)] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  · filter_upwards [χ.eventuallyEq_one] with q hq
    simp [hq]

/-- A function `Cⁿ` at a point (`n` finite) agrees near that point with a global `Cⁿ` function. -/
theorem ContDiffAt.exists_contDiff_eventuallyEq {n : ℕ} {ψ : X → ℝ} {p : X}
    (hψ : ContDiffAt ℝ n ψ p) : ∃ φ : X → ℝ, ContDiff ℝ n φ ∧ φ =ᶠ[𝓝 p] ψ := by
  obtain ⟨u, hu, hψu⟩ := hψ.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨N, hNu, hN, hpN⟩ := mem_nhds_iff.1 hu
  exact exists_contDiff_eventuallyEq_of_contDiffOn (n := n) hN hpN (hψu.mono hNu)

end Extension

/-- A function `Cⁿ` on an open neighbourhood `N` of `p` agrees near `p` with a global `Cⁿ`
function (for any `n : ℕ∞`). -/
theorem exists_contDiff_eventuallyEq {n : ℕ∞} {ψ : E d × ℝ → ℝ} {N : Set (E d × ℝ)}
    (hN : IsOpen N) {p : E d × ℝ} (hp : p ∈ N) (hψ : ContDiffOn ℝ n ψ N) :
    ∃ φ : E d × ℝ → ℝ, ContDiff ℝ n φ ∧ φ =ᶠ[𝓝 p] ψ :=
  exists_contDiff_eventuallyEq_of_contDiffOn hN hp hψ

/-! ### Locality of the space-time operators -/

section Congr

variable {φ ψ : E d × ℝ → ℝ} {p : E d × ℝ}

theorem tendsto_sliceT (p : E d × ℝ) :
    Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝 p.2) (𝓝 p) := by
  simpa using ((continuous_const.prodMk continuous_id).tendsto p.2 :
    Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝 p.2) (𝓝 (p.1, p.2)))

theorem tendsto_sliceX (p : E d × ℝ) :
    Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 p) := by
  simpa using ((continuous_id.prodMk continuous_const).tendsto p.1 :
    Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 (p.1, p.2)))

theorem eventuallyEq_sliceT (h : φ =ᶠ[𝓝 p] ψ) :
    (fun s : ℝ ↦ φ (p.1, s)) =ᶠ[𝓝 p.2] fun s ↦ ψ (p.1, s) :=
  h.comp_tendsto (tendsto_sliceT p)

theorem eventuallyEq_sliceX (h : φ =ᶠ[𝓝 p] ψ) :
    (fun y : E d ↦ φ (y, p.2)) =ᶠ[𝓝 p.1] fun y ↦ ψ (y, p.2) :=
  h.comp_tendsto (tendsto_sliceX p)

/-- `dₜ` depends only on the germ. -/
theorem dₜ_congr_nhds (h : φ =ᶠ[𝓝 p] ψ) : dₜ φ p = dₜ ψ p :=
  (eventuallyEq_sliceT h).deriv_eq

/-- `lapₓ` depends only on the germ. -/
theorem lapₓ_congr_nhds (h : φ =ᶠ[𝓝 p] ψ) : lapₓ φ p = lapₓ ψ p :=
  (InnerProductSpace.laplacian_congr_nhds (eventuallyEq_sliceX h)).eq_of_nhds

/-- `gradₓ` depends only on the germ. -/
theorem gradₓ_congr_nhds (h : φ =ᶠ[𝓝 p] ψ) : gradₓ φ p = gradₓ ψ p := by
  simp only [gradₓ, gradient, (eventuallyEq_sliceX h).fderiv_eq]

end Congr

/-! ### Derivatives of slices -/

section Slices

variable {φ h : E d × ℝ → ℝ}

theorem contDiff_sliceX {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (t : ℝ) :
    ContDiff ℝ n (fun y : E d ↦ φ (y, t)) :=
  hφ.comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_sliceT {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (x : E d) :
    ContDiff ℝ n (fun s : ℝ ↦ φ (x, s)) :=
  hφ.comp (contDiff_const.prodMk contDiff_id)

/-- The spatial slice of a function `Cⁿ` at `p` is `Cⁿ` at `p.1`. -/
theorem contDiffAt_sliceX {n : WithTop ℕ∞} {p : E d × ℝ} (hφ : ContDiffAt ℝ n φ p) :
    ContDiffAt ℝ n (fun y : E d ↦ φ (y, p.2)) p.1 :=
  hφ.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)

/-- The time slice of a function differentiable at `p` is differentiable at `p.2`. -/
theorem differentiableAt_sliceT {p : E d × ℝ} (hφ : DifferentiableAt ℝ φ p) :
    DifferentiableAt ℝ (fun s : ℝ ↦ φ (p.1, s)) p.2 :=
  hφ.comp p.2 ((differentiableAt_const _).prodMk differentiableAt_id)

theorem hasFDerivAt_sliceX (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    HasFDerivAt (fun y : E d ↦ φ (y, q.2))
      ((fderiv ℝ φ q).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) q.1 :=
  (hφ q).hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left q.1 q.2)

theorem hasDerivAt_sliceT (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    HasDerivAt (fun s : ℝ ↦ φ (q.1, s)) (fderiv ℝ φ q (0, 1)) q.2 := by
  have h1 : HasDerivAt (fun s : ℝ ↦ (q.1, s)) ((0 : E d), (1 : ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact (hφ q).hasFDerivAt.comp_hasDerivAt q.2 h1

theorem dₜ_eq_fderiv (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    dₜ φ q = fderiv ℝ φ q (0, 1) :=
  (hasDerivAt_sliceT hφ q).deriv

theorem gradₓ_eq_fderiv (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    gradₓ φ q = (toDual ℝ (E d)).symm
      ((fderiv ℝ φ q).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) := by
  simp only [gradₓ, gradient, (hasFDerivAt_sliceX hφ q).fderiv]

theorem lapₓ_eq_iteratedFDeriv (hφ : ContDiff ℝ 2 φ) (q : E d × ℝ) :
    lapₓ φ q = ∑ i, iteratedFDeriv ℝ 2 φ q
      ![((stdOrthonormalBasis ℝ (E d)) i, 0), ((stdOrthonormalBasis ℝ (E d)) i, 0)] := by
  have hslice : (fun y : E d ↦ φ (y, q.2)) =
      (fun z : E d × ℝ ↦ φ (z + (0, q.2))) ∘ ContinuousLinearMap.inl ℝ (E d) ℝ := by
    funext y; simp
  have hshift : ContDiff ℝ 2 (fun z : E d × ℝ ↦ φ (z + (0, q.2))) :=
    hφ.comp (contDiff_id.add contDiff_const)
  simp only [lapₓ, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hslice, ContinuousLinearMap.iteratedFDeriv_comp_right _ hshift _ le_rfl,
    iteratedFDeriv_comp_add_right']
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  · simp
  · ext j <;> fin_cases j <;> simp

/-! ### Continuity -/

/-- `dₜ φ` is continuous for `C¹` `φ`. -/
theorem continuous_dₜ (hφ : ContDiff ℝ 1 φ) : Continuous (dₜ φ) := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have : dₜ φ = fun q ↦ fderiv ℝ φ q (0, 1) := funext (dₜ_eq_fderiv hd)
  rw [this]
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_gradₓ (hφ : ContDiff ℝ 1 φ) : Continuous (gradₓ φ) := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have : gradₓ φ = fun q ↦ (toDual ℝ (E d)).symm
      ((fderiv ℝ φ q).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) := funext (gradₓ_eq_fderiv hd)
  rw [this]
  exact (toDual ℝ (E d)).symm.continuous.comp
    ((hφ.continuous_fderiv one_ne_zero).clm_comp continuous_const)

/-- `lapₓ φ` is continuous for `C²` `φ`. -/
theorem continuous_lapₓ (hφ : ContDiff ℝ 2 φ) : Continuous (lapₓ φ) := by
  have : lapₓ φ = fun q ↦ ∑ i, iteratedFDeriv ℝ 2 φ q
      ![((stdOrthonormalBasis ℝ (E d)) i, 0), ((stdOrthonormalBasis ℝ (E d)) i, 0)] :=
    funext (lapₓ_eq_iteratedFDeriv hφ)
  rw [this]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (continuous_eval_const _).comp (hφ.continuous_iteratedFDeriv le_rfl)

/-! ### Linearity -/

theorem dₜ_add (hφ : Differentiable ℝ φ) (hh : Differentiable ℝ h) (q : E d × ℝ) :
    dₜ (fun q ↦ φ q + h q) q = dₜ φ q + dₜ h q :=
  ((hasDerivAt_sliceT hφ q).add (hasDerivAt_sliceT hh q)).deriv.trans
    (by rw [dₜ_eq_fderiv hφ, dₜ_eq_fderiv hh])

theorem dₜ_sub (hφ : Differentiable ℝ φ) (hh : Differentiable ℝ h) (q : E d × ℝ) :
    dₜ (fun q ↦ φ q - h q) q = dₜ φ q - dₜ h q :=
  ((hasDerivAt_sliceT hφ q).sub (hasDerivAt_sliceT hh q)).deriv.trans
    (by rw [dₜ_eq_fderiv hφ, dₜ_eq_fderiv hh])

/-- `dₜ (a h) = a dₜ h`, with no regularity. -/
theorem dₜ_const_mul (h : E d × ℝ → ℝ) (a : ℝ) (q : E d × ℝ) :
    dₜ (fun q ↦ a * h q) q = a * dₜ h q := by
  simp only [dₜ]
  exact deriv_const_mul_field a

/-- Adding a constant does not change `dₜ` (no regularity needed). -/
theorem dₜ_add_const (h : E d × ℝ → ℝ) (b : ℝ) (q : E d × ℝ) :
    dₜ (fun q ↦ h q + b) q = dₜ h q := by
  simp [dₜ]

/-- `dₜ (-h) = -dₜ h`, with no regularity. -/
theorem dₜ_neg (h : E d × ℝ → ℝ) (q : E d × ℝ) :
    dₜ (fun q ↦ -h q) q = -dₜ h q := by
  simp only [dₜ]
  exact deriv.neg

theorem gradₓ_add (hφ : Differentiable ℝ φ) (hh : Differentiable ℝ h) (q : E d × ℝ) :
    gradₓ (fun q ↦ φ q + h q) q = gradₓ φ q + gradₓ h q := by
  have H : HasFDerivAt (fun y : E d ↦ φ (y, q.2) + h (y, q.2)) _ q.1 :=
    (hasFDerivAt_sliceX hφ q).add (hasFDerivAt_sliceX hh q)
  simp only [gradₓ, gradient]
  rw [H.fderiv, (hasFDerivAt_sliceX hφ q).fderiv, (hasFDerivAt_sliceX hh q).fderiv, map_add]

theorem gradₓ_const_mul (hh : Differentiable ℝ h) (a : ℝ) (q : E d × ℝ) :
    gradₓ (fun q ↦ a * h q) q = a • gradₓ h q := by
  have H : HasFDerivAt (fun y : E d ↦ a * h (y, q.2)) _ q.1 :=
    (hasFDerivAt_sliceX hh q).const_mul a
  simp only [gradₓ, gradient]
  rw [H.fderiv, (hasFDerivAt_sliceX hh q).fderiv]
  simp

theorem gradₓ_add_const (h : E d × ℝ → ℝ) (b : ℝ) (q : E d × ℝ) :
    gradₓ (fun q ↦ h q + b) q = gradₓ h q := by
  simp [gradₓ, gradient]

theorem lapₓ_add (hφ : ContDiff ℝ 2 φ) (hh : ContDiff ℝ 2 h) (q : E d × ℝ) :
    lapₓ (fun q ↦ φ q + h q) q = lapₓ φ q + lapₓ h q :=
  (contDiff_sliceX hφ q.2).contDiffAt.laplacian_add (contDiff_sliceX hh q.2).contDiffAt

theorem lapₓ_sub (hφ : ContDiff ℝ 2 φ) (hh : ContDiff ℝ 2 h) (q : E d × ℝ) :
    lapₓ (fun q ↦ φ q - h q) q = lapₓ φ q - lapₓ h q :=
  (contDiff_sliceX hφ q.2).contDiffAt.laplacian_sub (contDiff_sliceX hh q.2).contDiffAt

theorem lapₓ_const_mul (hh : ContDiff ℝ 2 h) (a : ℝ) (q : E d × ℝ) :
    lapₓ (fun q ↦ a * h q) q = a * lapₓ h q := by
  exact laplacian_smul (𝕜 := ℝ) (x := q.1) a (contDiff_sliceX hh q.2).contDiffAt

/-- Adding a constant does not change `lapₓ` (no regularity needed). -/
theorem lapₓ_add_const (h : E d × ℝ → ℝ) (b : ℝ) (q : E d × ℝ) :
    lapₓ (fun q ↦ h q + b) q = lapₓ h q := by
  have hf : fderiv ℝ (fun y : E d ↦ h (y, q.2) + b) = fderiv ℝ (fun y : E d ↦ h (y, q.2)) :=
    funext fun y ↦ fderiv_add_const b
  simp only [lapₓ, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply, hf]

/-- `lapₓ (-h) = -lapₓ h`, with no regularity. -/
theorem lapₓ_neg (h : E d × ℝ → ℝ) (q : E d × ℝ) :
    lapₓ (fun q ↦ -h q) q = -lapₓ h q := by
  simp only [lapₓ]
  exact congrFun (laplacian_neg (f := fun y : E d ↦ h (y, q.2))) q.1

/-- Heat operator of a perturbation `φ + (a h + b)`. -/
theorem dₜ_sub_lapₓ_add_mul_add (hφ : ContDiff ℝ 2 φ) (hh : ContDiff ℝ 2 h) (a b : ℝ)
    (q : E d × ℝ) :
    dₜ (fun q ↦ φ q + (a * h q + b)) q - lapₓ (fun q ↦ φ q + (a * h q + b)) q =
      (dₜ φ q - lapₓ φ q) + a * (dₜ h q - lapₓ h q) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hk : ContDiff ℝ 2 (fun q ↦ a * h q + b) := (contDiff_const.mul hh).add contDiff_const
  rw [dₜ_add hφd (hk.differentiable two_ne_zero), lapₓ_add hφ hk,
    dₜ_add_const (fun q ↦ a * h q), lapₓ_add_const (fun q ↦ a * h q), dₜ_const_mul,
    lapₓ_const_mul hh]
  ring

end Slices

/-! ### Local linearity -/

section Local

variable {N : Set (E d × ℝ)} {ψ h : E d × ℝ → ℝ} {p : E d × ℝ}

/-- Heat operator of a perturbation `ψ + (a h + c)` of functions which are `C²` near `p`. -/
theorem dₜ_sub_lapₓ_add_mul_add_of_contDiffOn (hN : IsOpen N) (hpN : p ∈ N)
    (hψ : ContDiffOn ℝ 2 ψ N) (hh : ContDiffOn ℝ 2 h N) (a c : ℝ) :
    dₜ (fun q ↦ ψ q + (a * h q + c)) p - lapₓ (fun q ↦ ψ q + (a * h q + c)) p =
      (dₜ ψ p - lapₓ ψ p) + a * (dₜ h p - lapₓ h p) := by
  obtain ⟨φ, hφ, hφψ⟩ := exists_contDiff_eventuallyEq (n := 2) hN hpN hψ
  obtain ⟨k, hk, hkh⟩ := exists_contDiff_eventuallyEq (n := 2) hN hpN hh
  have hsum : (fun q ↦ φ q + (a * k q + c)) =ᶠ[𝓝 p] fun q ↦ ψ q + (a * h q + c) := by
    filter_upwards [hφψ, hkh] with q h1 h2
    rw [h1, h2]
  rw [← dₜ_congr_nhds hsum, ← lapₓ_congr_nhds hsum, dₜ_sub_lapₓ_add_mul_add hφ hk,
    dₜ_congr_nhds hφψ, lapₓ_congr_nhds hφψ, dₜ_congr_nhds hkh, lapₓ_congr_nhds hkh]

/-- `dₜ` and `lapₓ` of a difference of two functions `C²` near `p`. -/
theorem dₜ_sub_lapₓ_sub_of_contDiffOn (hN : IsOpen N) (hpN : p ∈ N)
    (hh : ContDiffOn ℝ 2 h N) (hψ : ContDiffOn ℝ 2 ψ N) :
    dₜ (fun q ↦ ψ q - h q) p = dₜ ψ p - dₜ h p ∧
      lapₓ (fun q ↦ ψ q - h q) p = lapₓ ψ p - lapₓ h p := by
  obtain ⟨φ, hφ, hφh⟩ := exists_contDiff_eventuallyEq (n := 2) hN hpN hh
  obtain ⟨ψ', hψ', hψψ'⟩ := exists_contDiff_eventuallyEq (n := 2) hN hpN hψ
  have hsub : (fun q ↦ ψ' q - φ q) =ᶠ[𝓝 p] fun q ↦ ψ q - h q := by
    filter_upwards [hφh, hψψ'] with q h1 h2
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · rw [← dₜ_congr_nhds hsub, dₜ_sub (hψ'.differentiable two_ne_zero)
      (hφ.differentiable two_ne_zero), dₜ_congr_nhds hφh, dₜ_congr_nhds hψψ']
  · rw [← lapₓ_congr_nhds hsub, lapₓ_sub hψ' hφ, lapₓ_congr_nhds hφh, lapₓ_congr_nhds hψψ']

end Local

end ParabolicBasic
