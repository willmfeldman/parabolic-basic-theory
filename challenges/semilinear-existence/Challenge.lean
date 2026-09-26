import Challenge.Classical

/-!
# Challenge: existence for the semilinear Cauchy–Dirichlet problem

Trusted statement surface for the existence theorem for
`∂ₜu = Δₓu - f(x, u)` in `U × (0, ∞)`, `u = g` on the parabolic boundary
`(Ū × {0}) ∪ (∂U × [0, ∞))`, on a bounded open `U ⊆ ℝᵈ` with `C²` boundary
[Lieberman, *Second Order Parabolic Differential Equations*, Ch. IX;
Ladyzhenskaya–Solonnikov–Ural'tseva, *Linear and Quasi-linear Equations of Parabolic Type*,
Ch. V]. The solution is continuous on `Ū × [0, ∞)` and classical `C^{2,1}` in `U × (0, ∞)`.

All project vocabulary is restated inline in `Challenge/Setting.lean` and
`Challenge/Classical.lean`, which import `Mathlib` only.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Existence for the semilinear Cauchy–Dirichlet problem.** Let `U ⊆ ℝᵈ` be open and
bounded with `C²` boundary (`HasC2Boundary`: `U = {ρ < 0}` for a global `C²` function `ρ` with
`∇ρ ≠ 0` on `∂U`). Let `f : ℝᵈ → ℝ → ℝ` be, on `Ū`, Hölder in `x` uniformly in `z`
(`hfx`, some exponent `α ∈ (0, 1]`), Lipschitz in `z` uniformly in `x` (`hfz`), and bounded
(`hfb`), and let `g` be Lipschitz on `Ū`. Then there is `u` with:

* `u` continuous on `Ū × [0, ∞)`;
* `u` classical `C^{2,1}` in `U × (0, ∞)`: `u`, `∇ₓu`, `D²ₓu` (as `iteratedFDeriv ℝ 2` of the
  time slice) and the two-sided `∂ₜu` exist and are continuous there, and
  `∂ₜu = Δₓu - f(x, u)` pointwise;
* `u (x, 0) = g x` for `x ∈ Ū`, and `u (x, t) = g x` for `x ∈ ∂U`, `t ≥ 0`.

This is the variant proved: the hypotheses on `f` (Hölder in `x`) are stronger than mere
continuity in `x`, and the data `g` are time-independent and Lipschitz, so the corner
compatibility condition holds automatically. The global defining-function encoding of the `C²`
boundary is equivalent to the usual local-graph definition for bounded `U` (a bounded `C²`
domain has such a `ρ`, and conversely `∇ρ ≠ 0` gives local `C²` graphs by the implicit function
theorem, with `U` on one side).

Degenerate cases: `U = ∅` satisfies every hypothesis and makes the conclusion trivial. For
`d = 0`, `U = ℝ⁰` is allowed (`∂U = ∅`, take `ρ = -1`) and the statement is existence for the
ODE `u' = -f(0, u)`, `u(0) = g(0)`. For nonempty `U` with `d ≥ 1` it is the full
PDE statement. -/
theorem challenge_semilinear_exists {U : Set (E d)} {f : E d → ℝ → ℝ} {g : E d → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hC2 : HasC2Boundary U)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hfb : ∃ M : ℝ, ∀ x ∈ closure U, ∀ z, |f x z| ≤ M)
    (hg : ∃ L, LipschitzOnWith L g (closure U)) :
    ∃ u : E d × ℝ → ℝ, IsSemilinearSolution U f g u := by
  sorry

end ParabolicBasic
