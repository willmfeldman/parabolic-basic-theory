module

-- challenge-prep: split vocabulary (aux proofs are shared only within a file, so the vocabulary
-- follows the library's files)
-- One module per restated library file. Lean reuses an auxiliary `_proof_k` constant only within a
-- file, so merging the files would rename the auxiliary proofs that the library mints per module and
-- the values would no longer match (`scripts/check-challenge-definitions.lean`).
public import Vocabulary.Classical
public import Vocabulary.Viscosity

@[expose] public section

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
