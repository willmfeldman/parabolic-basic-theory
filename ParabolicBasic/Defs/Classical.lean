/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting

/-!
# Classical `C^{2,1}` and semilinear solutions

* `IsC21On U I u`: `u` is classical `C^{2,1}` on `U × I` — the first six conjuncts of
  `IsSemilinearSolOn`.
* `IsSemilinearSolOn U f I u`: classical solution of `∂ₜu = Δₓu - f(x, u)` on `U × I`.
* `IsSemilinearSolution U f g u`: solution of the Cauchy–Dirichlet problem on `U × (0, ∞)` with
  time-independent data `g`.
* `isSemilinearSolOn_iff`: `IsSemilinearSolOn U f I u ↔ IsC21On U I u ∧ (equation)`.

The time derivative is two-sided (`deriv`), so for `I = (a, b]` a solution is defined and
differentiable across `t = b`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- `u` is classical `C^{2,1}` on `U × I`: `u`, `∇ₓu`, `D²ₓu`, `∂ₜu` exist and are continuous on
`U × I` (the time derivative is two-sided). These are the first six conjuncts of
`IsSemilinearSolOn`. -/
def IsC21On (U : Set (E d)) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧
    (∀ t ∈ I, ContDiffOn ℝ 2 (fun x ↦ u (x, t)) U) ∧
    ContinuousOn (gradₓ u) (U ×ˢ I) ∧
    ContinuousOn (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1) (U ×ˢ I) ∧
    (∀ p ∈ U ×ˢ I, DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2) ∧
    ContinuousOn (dₜ u) (U ×ˢ I)

/-- `u` is a classical (`C^{2,1}`) solution of `∂ₜu = Δₓu - f(x, u)` in `U × I`:
`u`, `∇ₓu`, `D²ₓu`, `∂ₜu` exist and are continuous on `U × I`, and the equation holds pointwise. -/
def IsSemilinearSolOn (U : Set (E d)) (f : E d → ℝ → ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧
    (∀ t ∈ I, ContDiffOn ℝ 2 (fun x ↦ u (x, t)) U) ∧
    ContinuousOn (gradₓ u) (U ×ˢ I) ∧
    ContinuousOn (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1) (U ×ˢ I) ∧
    (∀ p ∈ U ×ˢ I, DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2) ∧
    ContinuousOn (dₜ u) (U ×ˢ I) ∧
    ∀ p ∈ U ×ˢ I, dₜ u p = lapₓ u p - f p.1 (u p)

/-- `u` solves the semilinear Cauchy–Dirichlet problem `∂ₜu = Δₓu - f(x, u)` in
`U_∞ = U × (0, ∞)` with time-independent data `g`: `u ∈ C(Ū × [0, ∞))`, `u` is a classical
`C^{2,1}` solution in `U_∞`, and `u = g` on `∂_P U_∞ = (Ū × {0}) ∪ (∂U × [0, ∞))`. -/
def IsSemilinearSolution (U : Set (E d)) (f : E d → ℝ → ℝ) (g : E d → ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (closure U ×ˢ Ici 0) ∧ IsSemilinearSolOn U f (Ioi 0) u ∧
    (∀ x ∈ closure U, u (x, 0) = g x) ∧ ∀ x ∈ frontier U, ∀ t : ℝ, 0 ≤ t → u (x, t) = g x

/-- A classical semilinear solution is a `C^{2,1}` function satisfying the equation pointwise. -/
theorem isSemilinearSolOn_iff {U : Set (E d)} {f : E d → ℝ → ℝ} {I : Set ℝ}
    {u : E d × ℝ → ℝ} :
    IsSemilinearSolOn U f I u ↔
      IsC21On U I u ∧ ∀ p ∈ U ×ˢ I, dₜ u p = lapₓ u p - f p.1 (u p) :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ ↦ ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩,
    fun ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩

end ParabolicBasic
