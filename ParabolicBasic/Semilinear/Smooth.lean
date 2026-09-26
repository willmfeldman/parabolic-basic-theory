/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Semilinear.SmoothBasic
public import ParabolicBasic.Semilinear.SmoothHolderCk
public import ParabolicBasic.Semilinear.SmoothDiffQuot
public import ParabolicBasic.Schauder.Iteration.Interior
public import ParabolicBasic.Classical.ToViscosity

/-!
# `C^∞` interior regularity for smooth nonlinearities

Fix `α = 1/2`, `Ω = U × I`.

* `holderCk_one_of_isHeatSolOn` (the case `m = 0` of the bootstrap): a continuous viscosity
  solution of `dₜφ − lapₓφ = ψ` with `ψ ∈ 𝓗⁰` is in `𝓗¹` (J(0) for `φ ∈ 𝓗⁰`; J(2) for `C^{2,1}`
  and Hölder `dₜφ`, `∇ₓφ`; the dictionary `∂_{ι(i)} φ = (∇ₓφ)ᵢ`, `∂_d φ = dₜφ`).
* `holderCk_succ_of_isHeatSolOn`: `ψ ∈ 𝓗ᵐ ⇒ φ ∈ 𝓗^{m+1}`, by induction
  with the difference-quotient lemma `isHeatSolOn_partialDeriv` (time derivatives are gained by
  *time* difference quotients; the equation is never differentiated).
* `IsSemilinearSolOn.contDiffOn`: a classical solution of `∂ₜu = Δₓu − f(x, u)`
  with `f` jointly `C^∞` is `C^∞` (`ContDiffOn ℝ ∞`, never `⊤`). The source `−f(x, u)` is
  frozen directly (classical ⇒ viscosity with the frozen zero-order term), and
  `u ∈ 𝓗ᵐ ⇒ −f(x, u) ∈ 𝓗ᵐ ⇒ u ∈ 𝓗^{m+1}` (`HolderCk.comp_contDiff`).

No heat kernel is used. For `d = 0` only the time direction exists; the proof is uniform.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- The case `m = 0` of the linear bootstrap, with the `C^{2,1}` information of J(2). -/
theorem holderCk_one_of_isHeatSolOn {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {φ ψ : E d × ℝ → ℝ}
    (hφ : ContinuousOn φ (U ×ˢ I)) (hsol : IsHeatSolOn (U ×ˢ I) ψ φ)
    (hψ : HolderCk α 0 ψ (U ×ˢ I)) :
    IsC21On U I φ ∧ (∀ p ∈ U ×ˢ I, dₜ φ p - lapₓ φ p = ψ p) ∧ HolderCk α 1 φ (U ×ˢ I) := by
  have hΩ : IsOpen (U ×ˢ I) := hU.prod hI
  obtain ⟨hC21, heq, hdt, hgrad, -⟩ := schauder_interior hU hI hα hφ hsol hψ.1 hψ.2
  refine ⟨hC21, heq, ⟨hφ, locHolder_of_isHeatSolOn hΩ hφ hsol hψ.1 hα⟩,
    hC21.differentiableOn hU hI, fun j ↦ ?_⟩
  induction j using Fin.lastCases with
  | last =>
    exact HolderCk.congr hΩ (m := 0) ⟨hC21.2.2.2.2.2, hdt⟩ (hC21.partialDeriv_last hU hI)
  | cast i =>
    exact HolderCk.congr hΩ (m := 0) ⟨hC21.continuousOn_gradₓ_apply i, hgrad i⟩
      (hC21.partialDeriv_castSucc hU hI i)

/-- **Linear bootstrap.** If `φ` is continuous on `U × I`, solves `dₜφ − lapₓφ = ψ` in the
viscosity sense, and `ψ ∈ 𝓗ᵐ`, then `φ ∈ 𝓗^{m+1}`. -/
theorem holderCk_succ_of_isHeatSolOn {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) (m : ℕ) {φ ψ : E d × ℝ → ℝ}
    (hφ : ContinuousOn φ (U ×ˢ I)) (hsol : IsHeatSolOn (U ×ˢ I) ψ φ)
    (hψ : HolderCk α m ψ (U ×ˢ I)) : HolderCk α (m + 1) φ (U ×ˢ I) := by
  have hΩ : IsOpen (U ×ˢ I) := hU.prod hI
  induction m generalizing φ ψ with
  | zero => exact (holderCk_one_of_isHeatSolOn hU hI hα hφ hsol hψ).2.2
  | succ m ih =>
    have h1 := (holderCk_one_of_isHeatSolOn hU hI hα hφ hsol hψ.zero).2.2
    refine ⟨h1.1, h1.2.1, fun j ↦ ih (h1.2.2 j).continuousOn ?_ (hψ.2.2 j)⟩
    exact isHeatSolOn_partialDeriv hΩ hsol hψ.continuousOn
      (fun q hq ↦ h1.differentiableAt hΩ hq) (fun q hq ↦ hψ.differentiableAt hΩ hq) j
      (h1.2.2 j).continuousOn (hψ.2.2 j).continuousOn

/-- **Interior smoothness** (used for `semilinear_contDiffOn_of_contDiff`). If `U`, `I` are open,
`(x, z) ↦ f x z` is `C^∞`, and `u` is a classical solution of `∂ₜu = Δₓu − f(x, u)` on `U × I`, then
`u` is `C^∞` on `U × I` (`ContDiffOn ℝ ∞`, not `⊤`). -/
theorem IsSemilinearSolOn.contDiffOn {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {f : E d → ℝ → ℝ} (hf : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ f q.1 q.2)) {u : E d × ℝ → ℝ}
    (hu : IsSemilinearSolOn U f I u) : ContDiffOn ℝ ∞ u (U ×ˢ I) := by
  obtain ⟨hC21, heq⟩ := isSemilinearSolOn_iff.1 hu
  have hΩ : IsOpen (U ×ˢ I) := hU.prod hI
  have hα : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by norm_num
  have hG : ContDiff ℝ ∞ (fun q : (E d × ℝ) × ℝ ↦ -f q.1.1 q.2) :=
    (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)).neg
  have hsol : IsHeatSolOn (U ×ˢ I) (fun p ↦ -f p.1 (u p)) u :=
    ⟨hC21.isViscSubOn hU hI fun p hp ↦ by simp only [neg_neg]; linarith [heq p hp],
      hC21.isViscSuperOn hU hI fun p hp ↦ by simp only [neg_neg]; linarith [heq p hp]⟩
  have hHc : ContinuousOn (fun p ↦ -f p.1 (u p)) (U ×ˢ I) :=
    hG.continuous.comp_continuousOn (continuousOn_id.prodMk hC21.1)
  have hall : ∀ m, HolderCk (1 / 2) m u (U ×ˢ I) := by
    intro m
    induction m with
    | zero => exact ⟨hC21.1, locHolder_of_isHeatSolOn hΩ hC21.1 hsol hHc hα⟩
    | succ m ih =>
      exact holderCk_succ_of_isHeatSolOn hU hI hα m hC21.1 hsol
        (ih.comp_contDiff hΩ ⟨hα.1, hα.2.le⟩ hG)
  exact contDiffOn_infty_of_forall_holderCk hΩ hall

end ParabolicBasic
