module

-- challenge-prep: split vocabulary (aux proofs are shared only within a file, so the vocabulary
-- follows the library's files)
-- One module per restated library file. Lean reuses an auxiliary `_proof_k` constant only within a
-- file, so merging the files would rename the auxiliary proofs that the library mints per module and
-- the values would no longer match (`scripts/check-challenge-definitions.lean`).
public import Vocabulary.Classical

@[expose] public section

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
