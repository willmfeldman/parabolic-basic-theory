/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Holder
public import ParabolicBasic.Schauder.Iteration.Basic
public import ParabolicBasic.Comparison.Parabolic

/-!
# Semilinear existence: basic helpers

* `IsViscSolOn.isHeatSolOn_freeze`: freezing the nonlinearity turns a viscosity
  solution of `dₜu − lapₓu + F p (u p) = 0` into a viscosity solution of the heat equation with
  source `H p = −F p (u p)`;
* `LocHolderOnPar.semilinear_rhs`: the frozen source is locally Hölder;
* `closure_prod_Ico_subset`: `closure U × [0, b)` lies in the open cylinder
  together with its parabolic boundary.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- Freeze the nonlinearity: a viscosity solution of `dₜu − lapₓu + F p (u p) = 0` solves the
linear equation `dₜu − lapₓu = −F p (u p)` (`IsHeatSolOn`). -/
theorem IsViscSolOn.isHeatSolOn_freeze {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (h : IsViscSolOn Ω F u) : IsHeatSolOn Ω (fun p ↦ -F p (u p)) u :=
  ⟨⟨h.1.1, fun ψ hψ p hp ht ↦ by simpa only [neg_neg] using h.1.2 ψ hψ p hp ht⟩,
    ⟨h.2.1, fun ψ hψ p hp ht ↦ by simpa only [neg_neg] using h.2.2 ψ hψ p hp ht⟩⟩

/-- Hölder of the frozen source: a short corollary of `LocHolderOnPar.comp_holder`. -/
theorem LocHolderOnPar.semilinear_rhs {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} {α K β L : ℝ} (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1)
    (hfx : ∀ x ∈ U, ∀ y ∈ U, ∀ z, |f x z - f y z| ≤ K * dist x y ^ β)
    (hfz : ∀ x ∈ U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hu : LocHolderOnPar α u (U ×ˢ I)) :
    LocHolderOnPar (min α β) (fun p ↦ -f p.1 (u p)) (U ×ˢ I) :=
  (hu.comp_holder hα.1 hβ.1 (fun _ hp ↦ hp.1) hfx hfz).neg

/-- **Cylinder geometry.** For open `U`, `closure U × [0, b) ⊆ U × (0, b) ∪ parBdry U 0 b`. -/
theorem closure_prod_Ico_subset {U : Set (E d)} (hU : IsOpen U) (b : ℝ) :
    closure U ×ˢ Ico 0 b ⊆ U ×ˢ Ioo 0 b ∪ parBdry U 0 b := by
  intro p hp
  by_cases h : p ∈ U ×ˢ Ioo 0 b
  · exact Or.inl h
  · exact Or.inr (mem_parBdry_of_notMem hU hp h)

end ParabolicBasic
