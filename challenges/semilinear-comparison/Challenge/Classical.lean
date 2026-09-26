import Challenge.Setting

/-!
# Challenge vocabulary: classical `C^{2,1}` and semilinear solutions

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Setting`).
Restates definitions of the library file `ParabolicBasic/Defs/Classical.lean`. The time
derivative is the two-sided `deriv`.
-/

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

end ParabolicBasic
