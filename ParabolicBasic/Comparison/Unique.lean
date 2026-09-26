/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Comparison.Continuous
public import ParabolicBasic.Classical.ToViscosity
public import ParabolicBasic.Defs.Classical

/-!
# Uniqueness for the semilinear Cauchy–Dirichlet problem

The proof of `semilinear_unique` (`ParabolicBasic.MainTheorems`). Classical solutions are
viscosity solutions (`IsC21On.isViscSubOn`); on each finite cylinder `U × (0, T)` comparison
(`comparison_continuous`) applies in both directions. "Gluing over `T`" is the choice `T = t + 1`
for each point `(x, t)`.

No `C²` boundary, no Lipschitz `g` and no bound on `f` are used.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- Restricting the time interval of a classical solution. -/
theorem IsSemilinearSolOn.mono_time {U : Set (E d)} {f : E d → ℝ → ℝ} {I J : Set ℝ}
    {u : E d × ℝ → ℝ} (hu : IsSemilinearSolOn U f I u) (hJI : J ⊆ I) :
    IsSemilinearSolOn U f J u := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hu
  have hs : U ×ˢ J ⊆ U ×ˢ I := prod_mono le_rfl hJI
  exact ⟨h₁.mono hs, fun t ht ↦ h₂ t (hJI ht), h₃.mono hs, h₄.mono hs, fun p hp ↦ h₅ p (hs hp),
    h₆.mono hs, fun p hp ↦ h₇ p (hs hp)⟩

/-- A classical solution on `U × (0, ∞)` is a viscosity solution of
`dₜu − lapₓu + f(x, u) = 0` on every `U × (0, T)`. -/
theorem IsSemilinearSolOn.isViscSolOn_Ioo {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsSemilinearSolOn U f (Ioi 0) u) (T : ℝ) :
    IsViscSubOn (U ×ˢ Ioo 0 T) (fun p z ↦ f p.1 z) u ∧
      IsViscSuperOn (U ×ˢ Ioo 0 T) (fun p z ↦ f p.1 z) u := by
  obtain ⟨hC, heq⟩ := isSemilinearSolOn_iff.1 hu
  have hsub : U ×ˢ Ioo 0 T ⊆ U ×ˢ Ioi 0 := prod_mono le_rfl Ioo_subset_Ioi_self
  have ho : IsOpen (U ×ˢ Ioo (0 : ℝ) T) := hU.prod isOpen_Ioo
  refine ⟨(IsC21On.isViscSubOn hU isOpen_Ioi hC fun p hp ↦ ?_).mono_set ho hsub,
    (IsC21On.isViscSuperOn hU isOpen_Ioi hC fun p hp ↦ ?_).mono_set ho hsub⟩
  · rw [heq p hp]; simp
  · rw [heq p hp]; simp

/-- Uniqueness for the semilinear Cauchy–Dirichlet problem: the proof body of
`semilinear_unique`. -/
theorem semilinear_unique_aux {U : Set (E d)} {f : E d → ℝ → ℝ} {g : E d → ℝ}
    {u v : E d × ℝ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hu : IsSemilinearSolution U f g u) (hv : IsSemilinearSolution U f g v) :
    ∀ p ∈ closure U ×ˢ Ici (0 : ℝ), u p = v p := by
  intro p hp
  obtain ⟨huc, husol, hui, hul⟩ := hu
  obtain ⟨hvc, hvsol, hvi, hvl⟩ := hv
  set T : ℝ := p.2 + 1 with hT
  have hT0 : 0 < T := by have : (0 : ℝ) ≤ p.2 := hp.2; linarith
  have hsub : closure U ×ˢ Icc 0 T ⊆ closure U ×ˢ Ici 0 := prod_mono le_rfl Icc_subset_Ici_self
  have hpT : p ∈ closure U ×ˢ Icc 0 T := ⟨hp.1, hp.2, by linarith⟩
  obtain ⟨husub, husup⟩ := husol.isViscSolOn_Ioo hU T
  obtain ⟨hvsub, hvsup⟩ := hvsol.isViscSolOn_Ioo hU T
  have hbd : ∀ q ∈ parBdry U 0 T, u q = v q := by
    rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
    · rw [mem_singleton_iff] at ht
      simp only at ht hx ⊢
      rw [ht, hui x hx, hvi x hx]
    · simp only at ht hx ⊢
      rw [hul x hx t ht.1, hvl x hx t ht.1]
  have h1 := comparison_continuous hU hUb hT0 hfx hfz (huc.mono hsub) (hvc.mono hsub) husub hvsup
    (fun q hq ↦ (hbd q hq).le)
  have h2 := comparison_continuous hU hUb hT0 hfx hfz (hvc.mono hsub) (huc.mono hsub) hvsub husup
    (fun q hq ↦ (hbd q hq).ge)
  exact le_antisymm (h1 p hpT) (h2 p hpT)

end ParabolicBasic
