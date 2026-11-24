module

-- challenge-prep: split vocabulary (aux proofs are shared only within a file, so the vocabulary
-- follows the library's files)
-- One module per restated library file. Lean reuses an auxiliary `_proof_k` constant only within a
-- file, so merging the files would rename the auxiliary proofs that the library mints per module and
-- the values would no longer match (`scripts/check-challenge-definitions.lean`).
public import Vocabulary.Parabolic
public import Vocabulary.Classical
public import Vocabulary.Viscosity
public import Vocabulary.Holder

@[expose] public section

/-!
# Challenge: the main results of the library

The single comparator workspace for the library's main results. Each section below is one group
of statements, unchanged from the library's earlier per-result workspaces. The project vocabulary
is restated, token for token, in `Vocabulary/*.lean` (one Mathlib-only module per restated library
file: `Setting`, `Touching`, `Parabolic`, `Classical`, `Viscosity`, `Holder`). The files follow the
library's file boundaries, which the comparator needs (see the README).
-/

section CaloricDirichletBall

/-!
# Challenge: the Dirichlet problem for the heat equation on a ball cylinder

Trusted statement surface for the caloric Dirichlet problem on the cylinder
`B_ρ(x₀) × (a, b]` in `ℝᵈ × ℝ` [Lieberman, *Second Order Parabolic Differential Equations*,
Ch. III]. For continuous data `g` on the parabolic boundary
`(B̄_ρ(x₀) × {a}) ∪ (∂B_ρ(x₀) × [a, b])` there is `h`, continuous on the closed cylinder
`B̄_ρ(x₀) × [a, b]`, `C^∞` in the open cylinder `B_ρ(x₀) × (a, b)` and solving the heat equation
`∂ₜh = Δₓh` there classically, with `h = g` on the parabolic boundary.

The statement uses Mathlib vocabulary only: `EuclideanSpace ℝ (Fin d)`, `Metric.ball`,
`Metric.closedBall`, `Metric.sphere`, `ContinuousOn`, `ContDiffOn`, `deriv` and Mathlib's
Laplacian `Δ` (`InnerProductSpace.laplacian`). No project definition is used.
-/

open Set Metric
open scoped ContDiff Laplacian

namespace ParabolicBasic

/-- **Caloric Dirichlet problem on a ball cylinder.** Let `x₀ ∈ ℝᵈ`, `ρ > 0`, `a < b`, and let
`g` be continuous on the parabolic boundary `(B̄_ρ(x₀) × {a}) ∪ (∂B_ρ(x₀) × [a, b])`. Then there is
`h : ℝᵈ × ℝ → ℝ` such that

* `h` is continuous on `B̄_ρ(x₀) × [a, b]`;
* `h` is `C^∞` on `B_ρ(x₀) × (a, b)` (`ContDiffOn ℝ ∞`; in this Mathlib `ω` would mean analytic,
  which is not claimed);
* `∂ₜh(x, t) = Δₓh(x, t)` for `x ∈ B_ρ(x₀)`, `t ∈ (a, b)`, where `∂ₜ` is the derivative of the time
  slice `s ↦ h (x, s)` and `Δₓ` is the Laplacian of the space slice `y ↦ h (y, t)`;
* `h = g` on the initial face `B̄_ρ(x₀) × {a}` and on the lateral face `∂B_ρ(x₀) × [a, b]`.

All `d` are allowed. For `d = 0` the space `ℝ⁰` is a point, the sphere is empty, and the statement
reduces to the initial-value problem for an ODE `h' = 0`. -/
theorem challenge_caloric_dirichlet_ball {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d)) {ρ : ℝ}
    (hρ : 0 < ρ) {a b : ℝ} (hab : a < b) {g : EuclideanSpace ℝ (Fin d) × ℝ → ℝ}
    (hg : ContinuousOn g (closedBall x₀ ρ ×ˢ {a} ∪ sphere x₀ ρ ×ˢ Icc a b)) :
    ∃ h : EuclideanSpace ℝ (Fin d) × ℝ → ℝ,
      ContinuousOn h (closedBall x₀ ρ ×ˢ Icc a b) ∧
      ContDiffOn ℝ ∞ h (ball x₀ ρ ×ˢ Ioo a b) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t ∈ Ioo a b,
        deriv (fun s ↦ h (x, s)) t = Δ (fun y ↦ h (y, t)) x) ∧
      (∀ x ∈ closedBall x₀ ρ, h (x, a) = g (x, a)) ∧
      (∀ x ∈ sphere x₀ ρ, ∀ t ∈ Icc a b, h (x, t) = g (x, t)) := by
  sorry

end ParabolicBasic

end CaloricDirichletBall

section SemilinearComparison

/-!
# Challenge: comparison and uniqueness for the semilinear heat equation

Trusted statement surface for the comparison principle for the semilinear equation
`∂ₜu = Δₓu - f(x, u)` [Crandall–Ishii–Lions, *User's guide to viscosity solutions*, Thm 8.2] and
its corollary, uniqueness for the Cauchy–Dirichlet problem. The project vocabulary is restated
inline, token for token, in `Vocabulary/Setting.lean` (the space `E d` and the operators `gradₓ`,
`lapₓ`, `dₜ`), `Vocabulary/Parabolic.lean` (`parBdry`), `Vocabulary/Touching.lean`,
`Vocabulary/Classical.lean` (`IsC21On`, `IsSemilinearSolOn`, `IsSemilinearSolution`) and
`Vocabulary/Viscosity.lean` (`IsSemilinearViscSubOn`, `IsSemilinearViscSuperOn`), which together
import `Mathlib` only. The files follow the library's file boundaries, which Comparator needs
(see the README).

The hypotheses on `f` are spelled out: Hölder continuity in `x` uniformly in `z` (`hfx`) and
Lipschitz continuity in `z` uniformly in `x` (`hfz`), on the closure of the domain. This is less
general than the "continuous in `x` uniformly in `z`" condition of [CIL, §3, §8].

The last statement, `challenge_parBdry_ball_nonempty`, is a sanity check on `parBdry`, not a
headline result: it computes the parabolic boundary of a ball cylinder.
-/

open Set Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- **Comparison for the semilinear equation** `∂ₜu = Δₓu - f(x, u)`. Let `V ⊆ ℝᵈ` be bounded and
open, `a < b`, and let `f` be Hölder in `x` on `V̄` uniformly in `z` (`hfx`) and Lipschitz in `z`
uniformly in `x ∈ V̄` (`hfz`). Let `u`, `v` be continuous on `V̄ × [a, b]`, with `u` a viscosity
subsolution and `v` a viscosity supersolution in `V × (a, b]`. If `u ≤ v` on the parabolic boundary
`(V̄ × {a}) ∪ (∂V × [a, b])`, then `u ≤ v` on `V̄ × [a, b]`.

The viscosity notions are the past-touching ones (`IsSemilinearViscSubOn`,
`IsSemilinearViscSuperOn`): global `C²` test functions touching relative to the parabolic past
`(V × (a, b]) ∩ {s ≤ t}`, so the top face `t = b` is included. This notion implies the standard
two-sided one on the open cylinder. -/
theorem challenge_semilinear_comparison {V : Set (E d)} {a b : ℝ} {f : E d → ℝ → ℝ}
    {u v : E d × ℝ → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hab : a < b)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure V, ∀ y ∈ closure V, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure V, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hu : ContinuousOn u (closure V ×ˢ Icc a b)) (hv : ContinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsSemilinearViscSubOn V f (Ioc a b) u)
    (hsuper : IsSemilinearViscSuperOn V f (Ioc a b) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Icc a b, u p ≤ v p := by
  sorry

/-- **Uniqueness for the semilinear Cauchy–Dirichlet problem.** Let `U ⊆ ℝᵈ` be open and bounded,
and let `f` be Hölder in `x` on `Ū` uniformly in `z` (`hfx`) and Lipschitz in `z` uniformly in
`x ∈ Ū` (`hfz`). If `u` and `v` both solve `∂ₜu = Δₓu - f(x, u)` classically in `U × (0, ∞)`, are
continuous on `Ū × [0, ∞)`, and equal the same time-independent data `g` on
`(Ū × {0}) ∪ (∂U × [0, ∞))` (`IsSemilinearSolution`), then `u = v` on `Ū × [0, ∞)`. No boundary
regularity of `U` and no regularity of `g` is assumed.

This is a corollary of the comparison principle (a classical solution is a viscosity solution,
then comparison on each `U × (0, T]` in both directions), so it adds little coverage beyond
`challenge_semilinear_comparison`. -/
theorem challenge_semilinear_unique {U : Set (E d)} {f : E d → ℝ → ℝ} {g : E d → ℝ}
    {u v : E d × ℝ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hu : IsSemilinearSolution U f g u) (hv : IsSemilinearSolution U f g v) :
    ∀ p ∈ closure U ×ˢ Ici (0 : ℝ), u p = v p := by
  sorry

/-- **Parabolic boundary of a ball cylinder (a non-vacuity check, not a headline result).** In
`ℝᵈ × ℝ`, the parabolic boundary of `B₁(0) × (0, 1]` is the classical set
`(B̄₁(0) × {0}) ∪ (∂B₁(0) × [0, 1])`, and it is nonempty, so the boundary hypotheses of the
theorems above constrain something. (For `d = 0` the sphere is empty and only the initial face
remains.) -/
theorem challenge_parBdry_ball_nonempty :
    parBdry (ball (0 : E d) 1) 0 1 = closedBall 0 1 ×ˢ {0} ∪ sphere 0 1 ×ˢ Icc 0 1 ∧
      (parBdry (ball (0 : E d) 1) 0 1).Nonempty := by
  sorry

end ParabolicBasic

end SemilinearComparison

section ClassicalViscosity

/-!
# Challenge: classical solutions of the semilinear heat equation are viscosity solutions

Trusted statement surface for the consistency of the viscosity notion with classical solutions
[Crandall–Ishii–Lions, *User's guide to viscosity solutions*, §8]: a classical `C^{2,1}` solution
of `∂ₜu = Δₓu - f(x, u)` in `U × I` is a viscosity sub- and supersolution in the past-touching
sense. The project vocabulary is restated inline, token for token, in `Vocabulary/Setting.lean`
(the space `E d` and the operators `gradₓ`, `lapₓ`, `dₜ`), `Vocabulary/Touching.lean`,
`Vocabulary/Classical.lean` (`IsC21On`, `IsSemilinearSolOn`) and `Vocabulary/Viscosity.lean`
(`IsViscSubOn`, `IsViscSuperOn`, `IsSemilinearViscSubOn`, `IsSemilinearViscSuperOn`), which together
import `Mathlib` only. The files follow the library's file boundaries, which Comparator needs (see
the README).

The content is the second-order test at a touching point: the spatial slice of `ψ - u` has a local
extremum, so the gradients agree and the Laplacians are ordered; and the time slice is only
touched on the past side `s ≤ t`, so only a one-sided inequality between the time derivatives is
available, which has the right sign.

The last three statements are sanity checks on these definitions, not headline results:
`challenge_time_not_viscSub` and `challenge_time_viscSuper` pin the sign convention of the standard
viscosity notion on `u(x, t) = t`, and `challenge_caloric_quadratic_solOn` shows that
`IsSemilinearSolOn` holds for an explicit nonconstant function.
-/

open Set Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- **Classical solutions are viscosity subsolutions.** Let `U ⊆ ℝᵈ` be open, let every `t ∈ I`
have a left neighbourhood `(t - δ, t] ⊆ I`, and let `u` be a classical `C^{2,1}` solution of
`∂ₜu = Δₓu - f(x, u)` in `U × I` (`IsSemilinearSolOn`). Then `u` is a viscosity subsolution in the
past-touching sense: whenever a global `C²` function `ψ` touches `u` from above at `p ∈ U × I`
relative to `(U × I) ∩ {s ≤ p.2}`, `∂ₜψ(p) - Δₓψ(p) ≤ -f(p.1, u p)`.

No regularity of `f` is needed. The condition on `I` holds for open intervals and for intervals
`(a, b]`; for `I = ∅` the statement is vacuous. -/
theorem challenge_classical_viscSub {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSubOn U f I u := by
  sorry

/-- **Classical solutions are viscosity supersolutions.** Under the hypotheses of
`challenge_classical_viscSub`, `u` is a viscosity supersolution in the past-touching sense:
whenever a global `C²` function `ψ` touches `u` from below at `p ∈ U × I` relative to
`(U × I) ∩ {s ≤ p.2}`, `-f(p.1, u p) ≤ ∂ₜψ(p) - Δₓψ(p)`. -/
theorem challenge_classical_viscSuper {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSuperOn U f I u := by
  sorry

/-- **Sign convention (negative test; a sign-convention check, not a headline result).** The function
`u(x, t) = t` is not a viscosity subsolution of the heat equation `∂ₜu - Δₓu = 0` on the cylinder
`B₁(0) × (0, 1)` in `ℝᵈ × ℝ`, for any `d`: `u` touches itself from above, and `∂ₜu - Δₓu = 1 > 0`.
This pins the sign convention `dₜu - lapₓu + F ≤ 0` for subsolutions and shows `IsViscSubOn` is not
trivially true. -/
theorem challenge_time_not_viscSub :
    ¬ IsViscSubOn (ball (0 : E d) 1 ×ˢ Ioo 0 1) (fun _ _ ↦ 0) (fun p ↦ p.2) := by
  sorry

/-- **Supersolution model case (a non-vacuity check, not a headline result).** The function
`u(x, t) = t` is a viscosity supersolution of the heat equation `∂ₜu - Δₓu = 0` on the cylinder
`B₁(0) × (0, 1)` in `ℝᵈ × ℝ`, for any `d`, so `IsViscSuperOn` is satisfiable by a function that is
not a solution. -/
theorem challenge_time_viscSuper :
    IsViscSuperOn (ball (0 : E d) 1 ×ˢ Ioo 0 1) (fun _ _ ↦ 0) (fun p ↦ p.2) := by
  sorry

/-- **Non-vacuity of classical solutions (a non-vacuity check, not a headline result).** The function
`u(x, t) = ‖x‖² + 2d·t` is a classical `C^{2,1}` solution of the heat equation `∂ₜu = Δₓu` on
`ℝᵈ × ℝ` (`IsSemilinearSolOn` with `U = ℝᵈ`, `I = ℝ` and `f = 0`): `∂ₜu = 2d = Δₓu`. So the
hypothesis of the theorems above is satisfiable by a nonconstant function for `d ≥ 1` (for `d = 1` it
is `x² + 2t`; for `d = 0` it is the zero function). -/
theorem challenge_caloric_quadratic_solOn :
    IsSemilinearSolOn univ (fun _ _ ↦ 0) univ (fun p : E d × ℝ ↦ ‖p.1‖ ^ 2 + 2 * d * p.2) := by
  sorry

end ParabolicBasic

end ClassicalViscosity

section SemilinearExistence

/-!
# Challenge: existence for the semilinear Cauchy–Dirichlet problem

Trusted statement surface for the existence theorem for
`∂ₜu = Δₓu - f(x, u)` in `U × (0, ∞)`, `u = g` on the parabolic boundary
`(Ū × {0}) ∪ (∂U × [0, ∞))`, on a bounded open `U ⊆ ℝᵈ` with `C²` boundary
[Lieberman, *Second Order Parabolic Differential Equations*, Ch. IX;
Ladyzhenskaya–Solonnikov–Ural'tseva, *Linear and Quasi-linear Equations of Parabolic Type*,
Ch. V]. The solution is continuous on `Ū × [0, ∞)` and classical `C^{2,1}` in `U × (0, ∞)`.

All project vocabulary is restated inline in `Vocabulary/Setting.lean` and
`Vocabulary/Classical.lean`, which import `Mathlib` only.
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

end SemilinearExistence

section SemilinearRegularity

/-!
# Challenge: regularity for the semilinear heat equation

Trusted statement surface for two regularity results for `∂ₜu = Δₓu - f(x, u)`:

* `challenge_semilinear_smooth`: interior `C^∞` regularity of classical `C^{2,1}` solutions
  when `f` is `C^∞` (Schauder bootstrap);
* `challenge_semilinear_gradient_continuous`: for a solution of the Cauchy–Dirichlet problem
  with `C²` data, continuity of the spatial gradient up to the initial time `t = 0` in the
  interior of the domain (barrier argument).

All project vocabulary is restated inline in `Vocabulary/Setting.lean` and
`Vocabulary/Classical.lean`, which import `Mathlib` only. The conclusions are stated with
Mathlib's `ContDiffOn` and `ContinuousOn`; `gradₓ u (x, t)` is Mathlib's `gradient` of the
time slice `y ↦ u (y, t)`.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Interior smoothness.** Let `U ⊆ ℝᵈ` and `I ⊆ ℝ` be open, let `(x, z) ↦ f x z` be `C^∞`
on `ℝᵈ × ℝ`, and let `u` be a classical `C^{2,1}` solution of `∂ₜu = Δₓu - f(x, u)` in `U × I`
(`u`, `∇ₓu`, `D²ₓu` and the two-sided `∂ₜu` exist and are continuous there, and the equation
holds pointwise). Then `u` is `C^∞` jointly in space and time on `U × I`.

Smoothness is `ContDiffOn ℝ ∞` (`C^∞`), not `ContDiffOn ℝ ω` (analytic): solutions need not be
analytic in time. The hypothesis is a *classical* solution; the theorem does not start from a
viscosity solution. Degenerate cases: if `U` or `I` is empty the conclusion is trivial. -/
theorem challenge_semilinear_smooth {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (hf : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ f q.1 q.2)) (hu : IsSemilinearSolOn U f I u) :
    ContDiffOn ℝ ∞ u (U ×ˢ I) := by
  sorry

/-- **Gradient continuity up to the initial time.** Let `U ⊆ ℝᵈ` be open, `(x, z) ↦ f x z`
continuous, and `g` a `C²` function on `ℝᵈ`. If `u` solves the semilinear Cauchy–Dirichlet
problem `∂ₜu = Δₓu - f(x, u)` in `U × (0, ∞)` with `u` continuous on `Ū × [0, ∞)` and `u = g`
on `(Ū × {0}) ∪ (∂U × [0, ∞))`, then the spatial gradient `∇ₓu` is continuous on `U × [0, ∞)`.

At `t = 0` the value is `∇ₓu (x, 0) = ∇g x` (the time-zero slice of `u` agrees with `g` on the
open set `U`), so the statement says that `∇ₓu (x, t) → ∇g x₀` as `(x, t) → (x₀, 0)` with
`x₀ ∈ U`: gradient continuity up to `t = 0` in the interior, not up to the lateral boundary.
No boundedness of `U` or regularity of `∂U` is assumed. Degenerate case: `U = ∅` makes the
conclusion trivial. -/
theorem challenge_semilinear_gradient_continuous {U : Set (E d)} {f : E d → ℝ → ℝ}
    {g : E d → ℝ} {u : E d × ℝ → ℝ} (hU : IsOpen U)
    (hf : Continuous (fun q : E d × ℝ ↦ f q.1 q.2)) (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) :
    ContinuousOn (gradₓ u) (U ×ˢ Ici 0) := by
  sorry

end ParabolicBasic

end SemilinearRegularity

section CaloricSmooth

/-!
# Challenge: viscosity solutions of the heat equation are smooth

Trusted statement surface for interior regularity of viscosity caloric functions: a continuous
viscosity solution of the heat equation `∂ₜu = Δₓu` on an open set `O ⊆ ℝᵈ × ℝ` is `C^∞` on `O`
and satisfies the equation classically. The library proves this by mollification, Bernstein-type
interior derivative estimates for smooth caloric functions, and stability of viscosity solutions
under local uniform limits.

All project vocabulary is restated inline in `Vocabulary/Setting.lean` and
`Vocabulary/Viscosity.lean`, which import `Mathlib` only. The conclusion is stated with Mathlib's
`ContDiffOn` and the slice derivatives `dₜ`, `lapₓ`, not through the library's
`IsSmoothCaloricOn`.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Viscosity caloric functions are smooth.** Let `O ⊆ ℝᵈ × ℝ` be open and `u` continuous on
`O`. Suppose `u` is a viscosity subsolution and a viscosity supersolution of `∂ₜu - Δₓu = 0` on
`O` in the standard sense (zero-order term `F = 0`): whenever a global `C²` function `ψ` touches
`u` from above (resp. below) at `p ∈ O`, `∂ₜψ p - Δₓψ p ≤ 0` (resp. `≥ 0`). Then `u` is `C^∞` on
`O` jointly in space and time, and `∂ₜu = Δₓu` at every point of `O`, with `∂ₜ` the two-sided
time derivative and `Δₓ` Mathlib's Laplacian of the time slice.

Smoothness is `ContDiffOn ℝ ∞` (`C^∞`), not `ContDiffOn ℝ ω` (analytic): caloric functions need
not be analytic in time. The continuity hypothesis `hu` is implied by `hsub` and `hsuper` (upper
and lower semicontinuity), and is kept as in the library. Valid for all `d`, including `d = 0`,
where the statement is about `u' = 0` in one time variable. Degenerate case: `O = ∅` makes the
conclusion trivial. -/
theorem challenge_caloric_smooth {O : Set (E d × ℝ)} (hO : IsOpen O) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u O) (hsub : IsViscSubOn O (fun _ _ ↦ 0) u)
    (hsuper : IsViscSuperOn O (fun _ _ ↦ 0) u) :
    ContDiffOn ℝ ∞ u O ∧ ∀ p ∈ O, dₜ u p = lapₓ u p := by
  sorry

end ParabolicBasic

end CaloricSmooth

section SchauderInterior

/-!
# Challenge: interior Schauder regularity for the heat equation

Trusted statement surface for the interior Schauder theorem for `∂ₜu - Δₓu = H`: a continuous
viscosity solution in `U × I`, with `H` locally parabolically `α`-Hölder, is classical
`C^{2,1}`, and `∂ₜu`, `∇ₓu` and `D²ₓu` are locally parabolically `α`-Hölder. This is the
interior `C^{2+α, 1+α/2}` regularity, obtained in the library by the `L^∞` Campanato iteration
of Caffarelli (1989), L. Wang (1992) and Safonov (1988): approximation in the sup norm by caloric
functions and caloric polynomials at every point and every scale (not Campanato's `L²` integral
method).

Hölder continuity is measured in the parabolic metric
`pdist (x, t) (y, s) = max ‖x - y‖ √|t - s|`, under which space scales like the square root of
time, matching the scaling `(x, t) ↦ (r x, r² t)` of the heat equation. It is a plain function:
`E d × ℝ` keeps Mathlib's sup metric.

All project vocabulary is restated inline in `Vocabulary/Setting.lean`,
`Vocabulary/Classical.lean`, `Vocabulary/Viscosity.lean` and `Vocabulary/Holder.lean`, which import
`Mathlib` only.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Interior Schauder regularity.** Let `U ⊆ ℝᵈ` and `I ⊆ ℝ` be open and `α ∈ (0, 1)`. Let
`u` be continuous on `U × I` and a viscosity solution of `∂ₜu - Δₓu = H` there (`IsHeatSolOn`:
whenever a global `C²` function `ψ` touches `u` from above, resp. below, at `p`,
`∂ₜψ p - Δₓψ p ≤ H p`, resp. `≥ H p`), where `H` is continuous on `U × I` and locally
parabolically `α`-Hölder (`LocHolderOnPar α H`: on each compact `K ⊆ U × I`, for some `C`,
`|H p - H q| ≤ C * pdist p q ^ α` for `p, q ∈ K`, with
`pdist (x, t) (y, s) = max ‖x - y‖ √|t - s|`). Then:

* `u` is classical `C^{2,1}` on `U × I` (`IsC21On`: `u`, `∇ₓu`, `D²ₓu` and the two-sided `∂ₜu`
  exist and are continuous);
* `∂ₜu - Δₓu = H` pointwise on `U × I`;
* `∂ₜu`, every coordinate `∂ᵢu` of `∇ₓu`, and every spatial second derivative
  `∂ᵢ∂ⱼu = D²ₓu (eᵢ, eⱼ)` (written with `iteratedFDeriv ℝ 2` of the time slice applied to the
  standard basis vectors `EuclideanSpace.single i 1`, `EuclideanSpace.single j 1`) are locally
  parabolically `α`-Hölder on `U × I`.

This is the interior `C^{2+α, 1+α/2}` regularity in qualitative form: a Hölder constant exists on
each compact subset, with no explicit dependence on the data stated. The gradient is asserted to
be parabolically `α`-Hölder; the sharper time exponent `(1 + α)/2` for `∇ₓu` that is part of the
full `C^{2+α, 1+α/2}` norm is not part of the statement. The hypothesis is a viscosity solution,
which is weaker than a classical one. Degenerate cases: if `U` or `I` is empty the conclusion is
trivial; the endpoint exponents `α = 0` and `α = 1` are excluded. -/
theorem challenge_schauder_interior {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {u H : E d × ℝ → ℝ}
    (hu : ContinuousOn u (U ×ˢ I)) (hsol : IsHeatSolOn (U ×ˢ I) H u)
    (hH : ContinuousOn H (U ×ˢ I)) (hHα : LocHolderOnPar α H (U ×ˢ I)) :
    IsC21On U I u ∧ (∀ p ∈ U ×ˢ I, dₜ u p - lapₓ u p = H p) ∧
      LocHolderOnPar α (dₜ u) (U ×ˢ I) ∧
      (∀ i, LocHolderOnPar α (fun p ↦ gradₓ u p i) (U ×ˢ I)) ∧
      ∀ i j, LocHolderOnPar α (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (U ×ˢ I) := by
  sorry

end ParabolicBasic

end SchauderInterior
