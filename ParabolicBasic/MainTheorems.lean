/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Parabolic
public import ParabolicBasic.Defs.Viscosity
public import ParabolicBasic.Defs.Classical
public import ParabolicBasic.Defs.Semilinear
public import ParabolicBasic.Dirichlet.Ball
public import ParabolicBasic.Comparison.Continuous
public import ParabolicBasic.Comparison.Unique
public import ParabolicBasic.Classical.ToViscosity
public import ParabolicBasic.Semilinear.ExistenceGlue
public import ParabolicBasic.Semilinear.ExistenceRegularity
public import ParabolicBasic.Semilinear.InitialGradient
public import ParabolicBasic.Semilinear.Smooth

/-!
# Main theorems

The headline results of the library, for the heat operator `∂ₜ - Δₓ` and the semilinear equation
`∂ₜu = Δₓu - f(x, u)` on `ℝᵈ × ℝ`:

* `caloric_dirichlet_ball`: the heat Dirichlet problem on a ball cylinder;
* `semilinear_comparison`: comparison for viscosity sub- and supersolutions;
* `isSemilinearViscSubOn_of_solOn`, `isSemilinearViscSuperOn_of_solOn`: classical solutions are
  viscosity solutions;
* `semilinear_unique`, `semilinear_exists`: uniqueness and existence for the semilinear
  Cauchy–Dirichlet problem on a bounded `C²` domain;
* `semilinear_contDiffOn_of_contDiff`: interior `C^∞` regularity for smooth `f`;
* `semilinear_continuousOn_gradₓ_of_contDiff`: continuity of `∇ₓu` up to `t = 0`.

The hypotheses on `f` are: Hölder in `x` uniformly in `z` (`hfx`), Lipschitz in `z` uniformly in `x`
(`hfz`) and, for existence, bounded (`hfb`), all on the closure of the domain. This is less general
than "continuous in `x` uniformly in `z`" [CIL, §3, §8], so no statement is stronger than the
literature.

## References

* [CIL] M. G. Crandall, H. Ishii, P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. AMS 27 (1992).
* [Lieberman] G. M. Lieberman, *Second Order Parabolic Differential Equations*, World Scientific
  (1996).
* [LSU] O. A. Ladyzhenskaya, V. A. Solonnikov, N. N. Ural'tseva, *Linear and Quasi-linear Equations
  of Parabolic Type*, AMS (1968).
-/

@[expose] public section

open Set Metric Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-- **Caloric Dirichlet problem on a ball cylinder.** Let `x₀ ∈ ℝᵈ`, `ρ > 0`, `a < b`, and let `g`
be continuous on the parabolic boundary `∂ₚ(B_ρ(x₀) × (a, b]) = (closedBall x₀ ρ × {a}) ∪
(sphere x₀ ρ × [a, b])`. Then there is `h`, continuous on `closedBall x₀ ρ × [a, b]` and `C^∞`
on the open cylinder `B_ρ(x₀) × (a, b)`, with `∂ₜh = Δₓh` there and `h = g` on the parabolic
boundary.

* Smoothness is `ContDiffOn ℝ ∞` (`C^∞`), **not** `⊤`: in this Mathlib `⊤` means analytic, and
  caloric functions need not be analytic in time.
* Only open-cylinder smoothness is stated; the solution constructed in `Dirichlet.Ball` is in fact
  smooth across `t = b`.
* No `d ≥ 1` hypothesis: for `d = 0` the lateral boundary is empty.

Proof: Perron's method for the heat equation with exterior-sphere barriers, and interior
regularity of viscosity caloric functions. -/
theorem caloric_dirichlet_ball (x₀ : E d) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (hab : a < b)
    {g : E d × ℝ → ℝ} (hg : ContinuousOn g (parBdry (ball x₀ ρ) a b)) :
    ∃ h : E d × ℝ → ℝ, ContinuousOn h (closedBall x₀ ρ ×ˢ Icc a b) ∧
      ContDiffOn ℝ ∞ h (ball x₀ ρ ×ˢ Ioo a b) ∧
      (∀ p ∈ ball x₀ ρ ×ˢ Ioo a b, dₜ h p = lapₓ h p) ∧
      EqOn h g (parBdry (ball x₀ ρ) a b) := by
  obtain ⟨h, hc, hcal, heq⟩ := caloric_dirichlet_ball_ext x₀ hρ hab hg
  have hsub : ball x₀ ρ ×ˢ Ioo a b ⊆ ball x₀ ρ ×ˢ Ioo a (b + 1) :=
    prod_mono subset_rfl (Ioo_subset_Ioo_right (by linarith))
  exact ⟨h, hc, hcal.1.mono hsub, fun p hp ↦ hcal.2 p (hsub hp), heq⟩

/-- **Comparison for the semilinear equation** `∂ₜu = Δₓu - f(x, u)`. Let `V ⊆ ℝᵈ` be bounded and
open, `a < b`, and let `f` be Hölder in `x` on `V̄` uniformly in `z` (`hfx`) and Lipschitz in `z`
uniformly in `x ∈ V̄` (`hfz`). If `u` is a continuous viscosity subsolution and `v` a continuous
viscosity supersolution in `V × (a, b]` (past-touching test functions), both continuous on
`V̄ × [a, b]`, and `u ≤ v` on the parabolic boundary `(V̄ × {a}) ∪ (∂V × [a, b])`, then `u ≤ v` on
`V̄ × [a, b]`. [CIL, Thm 8.2] -/
theorem semilinear_comparison {V : Set (E d)} {a b : ℝ} {f : E d → ℝ → ℝ} {u v : E d × ℝ → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hab : a < b)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure V, ∀ y ∈ closure V, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure V, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hu : ContinuousOn u (closure V ×ˢ Icc a b)) (hv : ContinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsSemilinearViscSubOn V f (Ioc a b) u)
    (hsuper : IsSemilinearViscSuperOn V f (Ioc a b) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Icc a b, u p ≤ v p := by
  exact comparison_continuous hV hVb hab hfx hfz hu hv (hsub.isViscSubOn hV)
    (hsuper.isViscSuperOn hV) hbdry

/-- **Classical solutions are viscosity subsolutions.** If `U` is open, every `t ∈ I` has a left
neighbourhood `(t - δ, t] ⊆ I`, and `u` is a classical `C^{2,1}` solution of
`∂ₜu = Δₓu - f(x, u)` in `U × I`, then `u` is a viscosity subsolution in the past-touching
sense. [CIL, §8] -/
theorem isSemilinearViscSubOn_of_solOn {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSubOn U f I u :=
  hu.isSemilinearViscSubOn hU hI

/-- **Classical solutions are viscosity supersolutions.** Same hypotheses as
`isSemilinearViscSubOn_of_solOn`; then `u` is a viscosity supersolution in the past-touching
sense. -/
theorem isSemilinearViscSuperOn_of_solOn {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSuperOn U f I u :=
  hu.isSemilinearViscSuperOn hU hI

/-- **Uniqueness for the semilinear Cauchy–Dirichlet problem.** Let `U` be open and bounded, and `f`
Hölder in `x` on `Ū` uniformly in `z` (`hfx`) and Lipschitz in `z` (`hfz`). Two solutions with the
same data `g` agree on `Ū × [0, ∞)`. No boundary regularity and no Lipschitz bound on `g` are
needed. -/
theorem semilinear_unique {U : Set (E d)} {f : E d → ℝ → ℝ} {g : E d → ℝ} {u v : E d × ℝ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hu : IsSemilinearSolution U f g u) (hv : IsSemilinearSolution U f g v) :
    ∀ p ∈ closure U ×ˢ Ici (0 : ℝ), u p = v p := by
  exact semilinear_unique_aux hU hUb hfx hfz hu hv

/-- **Existence for the semilinear Cauchy–Dirichlet problem.** Let `U` be open and bounded with `C²`
boundary, `f` Hölder in `x` on `Ū` uniformly in `z` (`hfx`), Lipschitz in `z` (`hfz`) and bounded
(`hfb`), and `g` Lipschitz on `Ū`. Then the problem `∂ₜu = Δₓu - f(x, u)` in `U × (0, ∞)`, `u = g`
on `(Ū × {0}) ∪ (∂U × [0, ∞))` has a solution `u ∈ C(Ū × [0, ∞)) ∩ C^{2,1}(U × (0, ∞))`.

Proof: Perron's method with barriers gives a viscosity solution; interior Schauder estimates upgrade
it to a classical one. [Lieberman, Ch. IX; Ladyzhenskaya–Solonnikov–Ural'tseva, Ch. V] -/
theorem semilinear_exists {U : Set (E d)} {f : E d → ℝ → ℝ} {g : E d → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hC2 : HasC2Boundary U)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hfb : ∃ M : ℝ, ∀ x ∈ closure U, ∀ z, |f x z| ≤ M)
    (hg : ∃ L, LipschitzOnWith L g (closure U)) :
    ∃ u : E d × ℝ → ℝ, IsSemilinearSolution U f g u := by
  obtain ⟨Lg, hLg⟩ := hg
  have hf : SemilinearHyp f (closure U) := ⟨hfx, hfz, hfb⟩
  obtain ⟨u, hc, hvisc, h0, hlat⟩ :=
    exists_viscSolution_semilinear_Ioi hU hUb hC2 hf hLg.continuousOn
  have hfxU : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α := by
    obtain ⟨K, α, hα, hα1, h⟩ := hfx
    exact ⟨K, α, hα, hα1, fun x hx y hy z ↦ h x (subset_closure hx) y (subset_closure hy) z⟩
  have hfzU : ∃ L : ℝ, ∀ x ∈ U, ∀ z w, |f x z - f x w| ≤ L * |z - w| := by
    obtain ⟨L, h⟩ := hfz
    exact ⟨L, fun x hx ↦ h x (subset_closure hx)⟩
  exact ⟨u, hc, isSemilinearSolOn_of_isViscSolOn hU isOpen_Ioi hfxU hfzU
    (hc.mono (prod_mono subset_closure Ioi_subset_Ici_self)) hvisc, h0, hlat⟩

/-- **Interior smoothness.** If `U ⊆ ℝᵈ` and `I ⊆ ℝ` are open, `(x, z) ↦ f x z` is `C^∞`, and `u` is
a classical `C^{2,1}` solution of `∂ₜu = Δₓu - f(x, u)` in `U × I`, then `u` is `C^∞` in `U × I`
(`ContDiffOn ℝ ∞`, not the analytic `⊤`). Proof: a difference-quotient bootstrap on interior
Schauder estimates. -/
theorem semilinear_contDiffOn_of_contDiff {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (hf : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ f q.1 q.2)) (hu : IsSemilinearSolOn U f I u) :
    ContDiffOn ℝ ∞ u (U ×ˢ I) := by
  exact hu.contDiffOn hU hI hf

/-- **Gradient continuity up to the initial time.** If `U` is open, `(x, z) ↦ f x z` is continuous,
the data `g` are `C²`, and `u` solves the semilinear Cauchy–Dirichlet problem with data `g`, then
the spatial gradient `∇ₓu` is continuous on `U × [0, ∞)`, i.e. up to `t = 0` in the interior of
`U`. -/
theorem semilinear_continuousOn_gradₓ_of_contDiff {U : Set (E d)} {f : E d → ℝ → ℝ}
    {g : E d → ℝ} {u : E d × ℝ → ℝ} (hU : IsOpen U)
    (hf : Continuous (fun q : E d × ℝ ↦ f q.1 q.2)) (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) :
    ContinuousOn (gradₓ u) (U ×ˢ Ici 0) := by
  exact hu.continuousOn_gradₓ hU hf hg

end ParabolicBasic
