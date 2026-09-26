import Challenge.Classical
import Challenge.Viscosity

/-!
# Challenge: classical solutions of the semilinear heat equation are viscosity solutions

Trusted statement surface for the consistency of the viscosity notion with classical solutions
[Crandall–Ishii–Lions, *User's guide to viscosity solutions*, §8]: a classical `C^{2,1}` solution
of `∂ₜu = Δₓu - f(x, u)` in `U × I` is a viscosity sub- and supersolution in the past-touching
sense. The project vocabulary is restated inline, token for token, in `Challenge/Setting.lean`
(the space `E d` and the operators `gradₓ`, `lapₓ`, `dₜ`), `Challenge/Touching.lean`,
`Challenge/Classical.lean` (`IsC21On`, `IsSemilinearSolOn`) and `Challenge/Viscosity.lean`
(`IsSemilinearViscSubOn`, `IsSemilinearViscSuperOn`), which together import `Mathlib` only. The
files follow the library's file boundaries, which Comparator needs (see the README).

The content is the second-order test at a touching point: the spatial slice of `ψ - u` has a local
extremum, so the gradients agree and the Laplacians are ordered; and the time slice is only
touched on the past side `s ≤ t`, so only a one-sided inequality between the time derivatives is
available, which has the right sign.
-/

open Set

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

end ParabolicBasic
