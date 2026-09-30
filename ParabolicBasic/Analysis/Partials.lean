/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import ParabolicBasic.Calculus.Slice
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Coordinate partial derivatives on space-time

Space-time `E d × ℝ` gets the coordinate basis `ebasis d : Fin (d + 1) → E d × ℝ`:
`ebasis d i.castSucc = (single i 1, 0)` (space) and `ebasis d (Fin.last d) = (0, 1)` (time),
with coordinate functionals `ecoord d`.

* `partialDeriv j f z := fderiv ℝ f z (ebasis d j)` (junk value `0` where `f` is not
  differentiable);
* `iterPartial w f` for a word `w = [j₁, …, jₖ]` is `∂_{j₁} (∂_{j₂} ( ⋯ (∂_{jₖ} f)))`
  (a right fold, so `iterPartial (j :: w) f = partialDeriv j (iterPartial w f)`);
* `HasPartialsOn k f s`: every `iterPartial w f` with `|w| ≤ k` is continuous on `s`, and
  Fréchet-differentiable at every point of `s` when `|w| < k`.

The dictionary: `dₜ`, `gradₓ`, `lapₓ`, the spatial Hessian in terms of
partials (local versions, for functions differentiable / `C²` near the point only), slices of
`ContDiffOn` functions, the formula `∂^w f z = D^k f z [e_{w₁}, …, e_{wₖ}]`, and the norm
comparisons between `‖D^k f z‖` and the `k`-th order partials. The global-`ContDiff` versions of
the slice formulas are in `ParabolicBasic.Calculus.Slice`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### The coordinate basis -/

/-- The coordinate basis of space-time: `ebasis d i.castSucc = (single i 1, 0)` for `i : Fin d`
(space directions) and `ebasis d (Fin.last d) = (0, 1)` (time direction). -/
noncomputable def ebasis (d : ℕ) : Fin (d + 1) → E d × ℝ :=
  Fin.lastCases ((0 : E d), (1 : ℝ)) fun i ↦ (EuclideanSpace.single i (1 : ℝ), (0 : ℝ))

/-- The coordinate functionals dual to `ebasis`: `ecoord d i.castSucc z = z.1 i`,
`ecoord d (Fin.last d) z = z.2`. -/
noncomputable def ecoord (d : ℕ) : Fin (d + 1) → StrongDual ℝ (E d × ℝ) :=
  Fin.lastCases (ContinuousLinearMap.snd ℝ (E d) ℝ)
    fun i ↦ (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (E d) ℝ)

@[simp] theorem ebasis_last : ebasis d (Fin.last d) = ((0 : E d), (1 : ℝ)) := by
  simp [ebasis]

@[simp] theorem ebasis_castSucc (i : Fin d) :
    ebasis d i.castSucc = (EuclideanSpace.single i (1 : ℝ), (0 : ℝ)) := by
  simp [ebasis]

@[simp] theorem ecoord_last (z : E d × ℝ) : ecoord d (Fin.last d) z = z.2 := by
  simp [ecoord]

@[simp] theorem ecoord_castSucc (i : Fin d) (z : E d × ℝ) : ecoord d i.castSucc z = z.1 i := by
  simp [ecoord]

/-- `ecoord` is dual to `ebasis`. -/
theorem ecoord_ebasis (i j : Fin (d + 1)) :
    ecoord d i (ebasis d j) = if i = j then 1 else 0 := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [PiLp.single_apply, eq_comm]

/-- Every vector is the sum of its coordinates times the basis vectors. -/
theorem sum_ecoord_smul_ebasis (v : E d × ℝ) : ∑ j, ecoord d j v • ebasis d j = v := by
  rw [Fin.sum_univ_castSucc]
  ext i
  · simp only [ecoord_castSucc, ebasis_castSucc, ecoord_last, ebasis_last, Prod.fst_add,
      Prod.fst_sum, Prod.smul_fst, smul_zero, add_zero]
    simp [WithLp.ofLp_sum, Pi.single_apply]
  · simp [Prod.snd_sum]

/-- A continuous linear functional is determined by its values on `ebasis`. -/
theorem clm_eq_sum_ecoord (L : StrongDual ℝ (E d × ℝ)) :
    L = ∑ j, L (ebasis d j) • ecoord d j := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  conv_lhs => rw [← sum_ecoord_smul_ebasis v]
  simp [map_sum, mul_comm]

/-- The coordinates are bounded by the (sup) norm. -/
theorem abs_ecoord_le (j : Fin (d + 1)) (v : E d × ℝ) : |ecoord d j v| ≤ ‖v‖ := by
  induction j using Fin.lastCases with
  | last => simpa [Real.norm_eq_abs] using norm_snd_le v
  | cast i => simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v.1 i).trans (norm_fst_le v)

/-- The basis vectors are unit vectors (for the sup norm on `E d × ℝ`). -/
theorem norm_ebasis (j : Fin (d + 1)) : ‖ebasis d j‖ = 1 := by
  induction j using Fin.lastCases with
  | last => simp [Prod.norm_def]
  | cast i => simp [Prod.norm_def]

/-! ### Partials and iterated partials -/

/-- The coordinate partial derivative `∂ⱼf(z) := Df(z)[eⱼ]` (junk value `0` where `f` is not
differentiable). -/
noncomputable def partialDeriv (j : Fin (d + 1)) (f : E d × ℝ → ℝ) : E d × ℝ → ℝ :=
  fun z ↦ fderiv ℝ f z (ebasis d j)

/-- The iterated partial along a word `w = [j₁, …, jₖ]`: `∂_{j₁} (∂_{j₂} ( ⋯ (∂_{jₖ} f)))`. -/
noncomputable def iterPartial (w : List (Fin (d + 1))) (f : E d × ℝ → ℝ) : E d × ℝ → ℝ :=
  w.foldr partialDeriv f

/-- `HasPartialsOn k f s`: for every word `w` with `|w| ≤ k`, the iterated partial `∂^w f` is
continuous on `s`, and if `|w| < k` it is (Fréchet) differentiable at every point of `s`. On open
`s` this is equivalent to `ContDiffOn ℝ k f s` (`contDiffOn_iff_hasPartialsOn`). -/
def HasPartialsOn (k : ℕ) (f : E d × ℝ → ℝ) (s : Set (E d × ℝ)) : Prop :=
  ∀ w : List (Fin (d + 1)), w.length ≤ k →
    ContinuousOn (iterPartial w f) s ∧
      (w.length < k → ∀ z ∈ s, DifferentiableAt ℝ (iterPartial w f) z)

@[simp] theorem iterPartial_nil (f : E d × ℝ → ℝ) : iterPartial [] f = f := rfl

@[simp] theorem iterPartial_cons (j : Fin (d + 1)) (w : List (Fin (d + 1))) (f : E d × ℝ → ℝ) :
    iterPartial (j :: w) f = partialDeriv j (iterPartial w f) := rfl

theorem iterPartial_append (w w' : List (Fin (d + 1))) (f : E d × ℝ → ℝ) :
    iterPartial (w ++ w') f = iterPartial w (iterPartial w' f) := by
  simp [iterPartial, List.foldr_append]

/-- Peeling off the innermost derivative: `∂^{w·j} f = ∂^w (∂ⱼ f)`. -/
theorem iterPartial_concat (w : List (Fin (d + 1))) (j : Fin (d + 1)) (f : E d × ℝ → ℝ) :
    iterPartial (w ++ [j]) f = iterPartial w (partialDeriv j f) := by
  rw [iterPartial_append]; rfl

@[simp] theorem iterPartial_singleton (j : Fin (d + 1)) (f : E d × ℝ → ℝ) :
    iterPartial [j] f = partialDeriv j f := rfl

/-- The Fréchet derivative in coordinates: `Df(z) = ∑ⱼ ∂ⱼf(z) eⱼ*` (for every `z`; both sides
are `0` where `f` is not differentiable). -/
theorem fderiv_eq_sum_partialDeriv (f : E d × ℝ → ℝ) (z : E d × ℝ) :
    fderiv ℝ f z = ∑ j, partialDeriv j f z • ecoord d j :=
  clm_eq_sum_ecoord _

/-! ### The dictionary with the slice operators -/

section Dictionary

variable {f : E d × ℝ → ℝ} {p z : E d × ℝ} {s : Set (E d × ℝ)}

/-- The time derivative is the last coordinate partial. -/
theorem dₜ_eq_partialDeriv_last (hf : DifferentiableAt ℝ f p) :
    dₜ f p = partialDeriv (Fin.last d) f p := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (p.1, t)) ((0 : E d), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 : HasDerivAt (fun t : ℝ ↦ f (p.1, t)) (fderiv ℝ f p ((0 : E d), (1 : ℝ))) p.2 :=
    hf.hasFDerivAt.comp_hasDerivAt p.2 h1
  rw [dₜ, h2.deriv]
  simp [partialDeriv]

/-- The spatial partials are the components of the spatial gradient (`f` only differentiable
at `p`). -/
theorem partialDeriv_castSucc_eq_gradₓ (hf : DifferentiableAt ℝ f p) (i : Fin d) :
    partialDeriv i.castSucc f p = gradₓ f p i := by
  have h1 : HasFDerivAt (fun y : E d ↦ f (y, p.2))
      ((fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) p.1 :=
    hf.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)
  have h2 := toDual_symm_apply (𝕜 := ℝ) (E := E d) (x := EuclideanSpace.single i (1 : ℝ))
    (y := (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ))
  rw [real_inner_comm, EuclideanSpace.inner_single_left] at h2
  simp only [map_one, one_mul] at h2
  simp [gradₓ, gradient, h1.fderiv, h2, partialDeriv]

/-- The spatial gradient in coordinates (`f` only differentiable at `p`). -/
theorem gradₓ_eq_sum_partialDeriv (hf : DifferentiableAt ℝ f p) :
    gradₓ f p = ∑ i : Fin d, partialDeriv i.castSucc f p • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  simp [partialDeriv_castSucc_eq_gradₓ hf, WithLp.ofLp_sum, Pi.single_apply]

/-- The `k`-th spatial derivative of the slice through `p` is the restriction of the joint `k`-th
derivative to spatial directions (`f` `Cᵏ` at `p`). -/
theorem iteratedFDeriv_sliceX_eq {k : ℕ} (hf : ContDiffAt ℝ k f p) :
    iteratedFDeriv ℝ k (fun y ↦ f (y, p.2)) p.1 =
      (iteratedFDeriv ℝ k f p).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.inl ℝ (E d) ℝ := by
  obtain ⟨φ, hφ, hφf⟩ := ContDiffAt.exists_contDiff_eventuallyEq hf
  have hsl : (fun y : E d ↦ φ (y, p.2)) =ᶠ[𝓝 p.1] fun y ↦ f (y, p.2) := eventuallyEq_sliceX hφf
  rw [← (hsl.iteratedFDeriv ℝ k).eq_of_nhds, ← (hφf.iteratedFDeriv ℝ k).eq_of_nhds]
  have hslice : (fun y : E d ↦ φ (y, p.2)) =
      (fun z : E d × ℝ ↦ φ (z + (0, p.2))) ∘ ContinuousLinearMap.inl ℝ (E d) ℝ := by
    funext y; simp
  have hshift : ContDiff ℝ k (fun z : E d × ℝ ↦ φ (z + (0, p.2))) :=
    hφ.comp (contDiff_id.add contDiff_const)
  rw [hslice, ContinuousLinearMap.iteratedFDeriv_comp_right _ hshift _ le_rfl,
    iteratedFDeriv_comp_add_right']
  simp

/-- The second spatial derivative of the slice through `p` is the restriction of the joint second
derivative (`f` `C²` at `p`). -/
theorem iteratedFDeriv_two_sliceX_apply (hf : ContDiffAt ℝ 2 f p) (u v : E d) :
    iteratedFDeriv ℝ 2 (fun y ↦ f (y, p.2)) p.1 ![u, v] =
      iteratedFDeriv ℝ 2 f p ![(u, 0), (v, 0)] := by
  rw [iteratedFDeriv_sliceX_eq (k := 2) hf, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext j <;> fin_cases j <;> simp

/-- Second partials as second derivatives: `D²f(z)[eᵢ, eⱼ] = ∂ᵢ∂ⱼf(z)` (`f` `C²` at `z`). -/
theorem partialDeriv_partialDeriv_eq_iteratedFDeriv (hf : ContDiffAt ℝ 2 f z)
    (i j : Fin (d + 1)) :
    partialDeriv i (partialDeriv j f) z = iteratedFDeriv ℝ 2 f z ![ebasis d i, ebasis d j] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fun y ↦ fderiv ℝ f y (ebasis d j)) z (ebasis d i) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- Second partials commute for `C²` functions. -/
theorem partialDeriv_comm (hf : ContDiffAt ℝ 2 f z) (i j : Fin (d + 1)) :
    partialDeriv i (partialDeriv j f) z = partialDeriv j (partialDeriv i f) z := by
  rw [partialDeriv_partialDeriv_eq_iteratedFDeriv hf,
    partialDeriv_partialDeriv_eq_iteratedFDeriv hf, iteratedFDeriv_two_apply,
    iteratedFDeriv_two_apply]
  exact hf.isSymmSndFDerivAt (by simp) _ _

/-- The spatial Hessian in coordinates:
`D²(f(·, p₂))(p₁)[bᵢ, bⱼ] = ∂ᵢ∂ⱼf(p)` (`f` `C²` at `p`). -/
theorem iteratedFDeriv_two_sliceX_single (hf : ContDiffAt ℝ 2 f p) (i j : Fin d) :
    iteratedFDeriv ℝ 2 (fun y ↦ f (y, p.2)) p.1
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)] =
      partialDeriv i.castSucc (partialDeriv j.castSucc f) p := by
  rw [iteratedFDeriv_two_sliceX_apply hf, partialDeriv_partialDeriv_eq_iteratedFDeriv hf]
  simp

/-- The spatial Laplacian is the sum of the pure second spatial partials (`f` `C²` at `p`). -/
theorem lapₓ_eq_sum_partialDeriv_of_contDiffAt (hf : ContDiffAt ℝ 2 f p) :
    lapₓ f p = ∑ i : Fin d, partialDeriv i.castSucc (partialDeriv i.castSucc f) p := by
  simp only [lapₓ, laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun _ ℝ),
    EuclideanSpace.basisFun_apply]
  exact Finset.sum_congr rfl fun i _ ↦ iteratedFDeriv_two_sliceX_single hf i i

/-- The spatial Laplacian is the sum of the pure second spatial partials (`f` `C²` on an open
set containing `p`). -/
theorem lapₓ_eq_sum_partialDeriv (hs : IsOpen s) (hf : ContDiffOn ℝ 2 f s) (hp : p ∈ s) :
    lapₓ f p = ∑ i : Fin d, partialDeriv i.castSucc (partialDeriv i.castSucc f) p :=
  lapₓ_eq_sum_partialDeriv_of_contDiffAt (hf.contDiffAt (hs.mem_nhds hp))

/-- Spatial slices of `Cⁿ` functions are `Cⁿ`. -/
theorem contDiffOn_sliceX {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) (t : ℝ) :
    ContDiffOn ℝ n (fun y : E d ↦ f (y, t)) {y | (y, t) ∈ s} :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) fun _ hy ↦ hy

/-- Time slices of `Cⁿ` functions are `Cⁿ`. -/
theorem contDiffOn_sliceT {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) (x : E d) :
    ContDiffOn ℝ n (fun t : ℝ ↦ f (x, t)) {t | (x, t) ∈ s} :=
  hf.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ ht ↦ ht

/-- The spatial `k`-th derivative of the slices is jointly continuous on an open set where `f` is
`Cᵏ` (the continuity field of `IsSemilinearSolOn` for `k = 2`). -/
theorem continuousOn_iteratedFDeriv_sliceX {k : ℕ} (hs : IsOpen s) (hf : ContDiffOn ℝ k f s) :
    ContinuousOn (fun p : E d × ℝ ↦ iteratedFDeriv ℝ k (fun y ↦ f (y, p.2)) p.1) s := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k f) s :=
    (hf.continuousOn_iteratedFDerivWithin le_rfl hs.uniqueDiffOn).congr
      fun x hx ↦ (iteratedFDerivWithin_of_isOpen k hs hx).symm
  refine ((ContinuousMultilinearMap.compContinuousLinearMapL
    fun _ ↦ ContinuousLinearMap.inl ℝ (E d) ℝ).continuous.comp_continuousOn hc).congr
      fun p hp ↦ ?_
  simp [iteratedFDeriv_sliceX_eq (hf.contDiffAt (hs.mem_nhds hp))]

end Dictionary

/-! ### Partials as values of the iterated derivative; norm comparisons -/

section Norms

variable {f : E d × ℝ → ℝ} {z : E d × ℝ} {s : Set (E d × ℝ)}

/-- For `f` `Cᵏ` on an open set,
`∂^w f(z) = D^k f(z)[e_{w₁}, …, e_{wₖ}]` (with the outermost derivative first). -/
theorem iterPartial_ofFn_eq_iteratedFDeriv {k : ℕ} (hs : IsOpen s) (hf : ContDiffOn ℝ k f s)
    (hz : z ∈ s) (m : Fin k → Fin (d + 1)) :
    iterPartial (List.ofFn m) f z = iteratedFDeriv ℝ k f z (fun i ↦ ebasis d (m i)) := by
  induction k generalizing z with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
    have hf' : ContDiffOn ℝ (k + 1) f s := by exact_mod_cast hf
    have hk : ContDiffOn ℝ k f s := hf'.of_le (by simp)
    have heq : iterPartial (List.ofFn (Fin.tail m)) f =ᶠ[𝓝 z]
        fun y ↦ iteratedFDeriv ℝ k f y (fun i ↦ ebasis d (Fin.tail m i)) :=
      Filter.eventually_of_mem (hs.mem_nhds hz) fun y hy ↦ ih hk hy (Fin.tail m)
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z :=
      (hf.contDiffAt (hs.mem_nhds hz)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self k)
    rw [List.ofFn_succ, iterPartial_cons]
    change fderiv ℝ (iterPartial (List.ofFn (Fin.tail m)) f) z (ebasis d (m 0)) = _
    rw [heq.fderiv_eq, fderiv_continuousMultilinear_apply_const hdiff,
      iteratedFDeriv_succ_apply_left]
    rfl

/-- `|∂^w f(z)| ≤ ‖D^k f(z)‖` for `|w| = k`. -/
theorem abs_iterPartial_le_norm_iteratedFDeriv {k : ℕ} (hs : IsOpen s) (hf : ContDiffOn ℝ k f s)
    (hz : z ∈ s) (w : List (Fin (d + 1))) (hw : w.length = k) :
    |iterPartial w f z| ≤ ‖iteratedFDeriv ℝ k f z‖ := by
  subst hw
  rw [← List.ofFn_get w, iterPartial_ofFn_eq_iteratedFDeriv hs hf hz, List.length_ofFn]
  simpa [norm_ebasis, Real.norm_eq_abs] using
    (iteratedFDeriv ℝ w.length f z).le_opNorm fun i ↦ ebasis d (w.get i)

/-- `‖D^k f(z)‖ ≤ ∑_{|w| = k} |∂^w f(z)|`. -/
theorem norm_iteratedFDeriv_le_partials {k : ℕ} (hs : IsOpen s) (hf : ContDiffOn ℝ k f s)
    (hz : z ∈ s) :
    ‖iteratedFDeriv ℝ k f z‖ ≤ ∑ m : Fin k → Fin (d + 1), |iterPartial (List.ofFn m) f z| := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) fun v ↦ ?_
  have hv : v = fun i ↦ ∑ j, ecoord d j (v i) • ebasis d j :=
    funext fun i ↦ (sum_ecoord_smul_ebasis (v i)).symm
  conv_lhs => rw [hv, ContinuousMultilinearMap.map_sum]
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [ContinuousMultilinearMap.map_smul_univ, norm_smul, norm_prod,
    ← iterPartial_ofFn_eq_iteratedFDeriv hs hf hz, Real.norm_eq_abs, mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    fun i _ ↦ ?_) (abs_nonneg _)
  simpa [Real.norm_eq_abs] using abs_ecoord_le (m i) (v i)

/-- `‖D^k f(z)‖ ≤ (d+1)^k max_{|w| = k} |∂^w f(z)|`. -/
theorem norm_iteratedFDeriv_le_of_forall_abs_iterPartial_le {k : ℕ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ k f s) (hz : z ∈ s) {M : ℝ}
    (hM : ∀ w : List (Fin (d + 1)), w.length = k → |iterPartial w f z| ≤ M) :
    ‖iteratedFDeriv ℝ k f z‖ ≤ (d + 1) ^ k * M := by
  refine (norm_iteratedFDeriv_le_partials hs hf hz).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ M fun m _ ↦ hM _ (List.length_ofFn)).trans ?_
  simp [nsmul_eq_mul]

end Norms

end ParabolicBasic
