/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Semilinear.ExistenceBasic
public import ParabolicBasic.Schauder.Iteration.Interior
public import ParabolicBasic.Comparison.SemilinearHyp

/-!
# Semilinear existence: interior regularity

A continuous viscosity solution of `dₜu = lapₓu − f(x, u)` with `f` Hölder in `x` (uniformly in `z`)
and Lipschitz in `z` is a classical `C^{2,1}` solution: freeze the nonlinearity
(`IsViscSolOn.isHeatSolOn_freeze`), J(0) (`locHolder_of_isHeatSolOn`) makes `u` locally
`1/2`-Hölder, hence the frozen source is locally Hölder (`LocHolderOnPar.semilinear_rhs`), and J(2)
(`schauder_interior`) gives `C^{2,1}` and the equation.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- Continuous viscosity solutions of the semilinear equation are classical `C^{2,1}` solutions. -/
theorem isSemilinearSolOn_of_isViscSolOn {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U)
    (hI : IsOpen I) {f : E d → ℝ → ℝ}
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ z, |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    {u : E d × ℝ → ℝ} (hu : ContinuousOn u (U ×ˢ I))
    (hsol : IsViscSolOn (U ×ˢ I) (fun p z ↦ f p.1 z) u) :
    IsSemilinearSolOn U f I u := by
  have hfx' := hfx
  obtain ⟨K, β, hβ, hβ1, hK⟩ := hfx
  obtain ⟨L, hL⟩ := hfz
  have hΩ : IsOpen (U ×ˢ I) := hU.prod hI
  set H : E d × ℝ → ℝ := fun p ↦ -f p.1 (u p) with hH_def
  have hheat : IsHeatSolOn (U ×ˢ I) H u := hsol.isHeatSolOn_freeze
  -- `H` is continuous: `f` agrees on `U × ℝ` with a jointly continuous extension
  have hHc : ContinuousOn H (U ×ˢ I) := by
    obtain ⟨g, hgf, -, -, hgc⟩ := exists_holderLip_extension hfx' ⟨L, hL⟩
    have : ContinuousOn (fun p : E d × ℝ ↦ -g p.1 (u p)) (U ×ˢ I) :=
      (hgc.comp_continuousOn (continuousOn_fst.prodMk hu)).neg
    exact this.congr fun p hp ↦ by simp only [hH_def, hgf p.1 hp.1]
  have hu12 : LocHolderOnPar (1 / 2) u (U ×ˢ I) :=
    locHolder_of_isHeatSolOn hΩ hu hheat hHc ⟨by norm_num, by norm_num⟩
  have hHα : LocHolderOnPar (min (1 / 2) β) H (U ×ˢ I) :=
    LocHolderOnPar.semilinear_rhs ⟨by norm_num, by norm_num⟩ ⟨hβ, hβ1⟩ hK hL hu12
  have hγ : 0 < min (1 / 2 : ℝ) β ∧ min (1 / 2 : ℝ) β < 1 :=
    ⟨lt_min (by norm_num) hβ, (min_le_left _ _).trans_lt (by norm_num)⟩
  obtain ⟨hC21, heq, -⟩ := schauder_interior hU hI hγ hu hheat hHc hHα
  refine isSemilinearSolOn_iff.2 ⟨hC21, fun p hp ↦ ?_⟩
  have := heq p hp
  simp only [hH_def] at this
  linarith

end ParabolicBasic
