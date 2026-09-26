import Challenge.Parabolic
import Challenge.Classical
import Challenge.Viscosity

/-!
# Challenge: sign convention, non-vacuity and parabolic-boundary model cases

Supplemental sanity checks on the library's definitions, on explicit functions. They are not
headline coverage; they guard against definitions that are trivially true, trivially false, or
carry the wrong sign.

* `challenge_time_not_viscSub`: `u(x, t) = t` has `∂ₜu - Δₓu = 1 > 0`, so it is **not** a viscosity
  subsolution of the heat equation (`IsViscSubOn` with zero-order term `0`). This pins the sign
  convention `dₜu - lapₓu + F ≤ 0` for subsolutions and shows `IsViscSubOn` is not trivially true.
* `challenge_time_viscSuper`: the same `u` is a viscosity supersolution, so `IsViscSuperOn` is
  satisfiable by a function that is not a solution.
* `challenge_caloric_quadratic_solOn`: `u(x, t) = ‖x‖² + 2d·t` is a classical solution of the heat
  equation on all of `ℝᵈ × ℝ` (`IsSemilinearSolOn` with `f = 0`), so the classical-solution
  hypotheses of the headline theorems are satisfiable by a nonconstant function (for `d ≥ 1`).
* `challenge_parBdry_ball_nonempty`: the parabolic boundary of `B₁(0) × (0, 1]` is the classical
  set `(B̄₁(0) × {0}) ∪ (∂B₁(0) × [0, 1])`, and it is nonempty.

The project vocabulary is restated inline, token for token, in `Challenge/Setting.lean` (the space
`E d` and the operators `gradₓ`, `lapₓ`, `dₜ`), `Challenge/Parabolic.lean` (`parBdry`),
`Challenge/Touching.lean`, `Challenge/Classical.lean` (`IsC21On`, `IsSemilinearSolOn`) and
`Challenge/Viscosity.lean` (`IsViscSubOn`, `IsViscSuperOn`), which together import `Mathlib` only.
The files follow the library's file boundaries, which Comparator needs (see the README).
-/

open Set Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- **Sign convention (negative test).** The function `u(x, t) = t` is not a viscosity subsolution
of the heat equation `∂ₜu - Δₓu = 0` on the cylinder `B₁(0) × (0, 1)` in `ℝᵈ × ℝ`, for any `d`:
`u` touches itself from above, and `∂ₜu - Δₓu = 1 > 0`. -/
theorem challenge_time_not_viscSub :
    ¬ IsViscSubOn (ball (0 : E d) 1 ×ˢ Ioo 0 1) (fun _ _ ↦ 0) (fun p ↦ p.2) := by
  sorry

/-- **Supersolution model case.** The function `u(x, t) = t` is a viscosity supersolution of the
heat equation `∂ₜu - Δₓu = 0` on the cylinder `B₁(0) × (0, 1)` in `ℝᵈ × ℝ`, for any `d`. -/
theorem challenge_time_viscSuper :
    IsViscSuperOn (ball (0 : E d) 1 ×ˢ Ioo 0 1) (fun _ _ ↦ 0) (fun p ↦ p.2) := by
  sorry

/-- **Non-vacuity of classical solutions.** The function `u(x, t) = ‖x‖² + 2d·t` is a classical
`C^{2,1}` solution of the heat equation `∂ₜu = Δₓu` on `ℝᵈ × ℝ` (`IsSemilinearSolOn` with
`U = ℝᵈ`, `I = ℝ` and `f = 0`): `∂ₜu = 2d = Δₓu`. For `d = 0` this is the zero function; for
`d ≥ 1` it is nonconstant (for `d = 1` it is `x² + 2t`). -/
theorem challenge_caloric_quadratic_solOn :
    IsSemilinearSolOn univ (fun _ _ ↦ 0) univ (fun p : E d × ℝ ↦ ‖p.1‖ ^ 2 + 2 * d * p.2) := by
  sorry

/-- **Parabolic boundary of a ball cylinder.** In `ℝᵈ × ℝ`, the parabolic boundary of
`B₁(0) × (0, 1]` is `(B̄₁(0) × {0}) ∪ (∂B₁(0) × [0, 1])`, and it is nonempty. (For `d = 0` the
sphere is empty and only the initial face remains.) -/
theorem challenge_parBdry_ball_nonempty :
    parBdry (ball (0 : E d) 1) 0 1 = closedBall 0 1 ×ˢ {0} ∪ sphere 0 1 ×ˢ Icc 0 1 ∧
      (parBdry (ball (0 : E d) 1) 0 1).Nonempty := by
  sorry

end ParabolicBasic
