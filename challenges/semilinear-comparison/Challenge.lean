module

-- challenge-prep: split vocabulary (aux proofs are shared only within a file, so the vocabulary
-- follows the library's files)
-- One module per restated library file. Lean reuses an auxiliary `_proof_k` constant only within a
-- file, so merging the files would rename the auxiliary proofs that the library mints per module and
-- the values would no longer match (`scripts/check-challenge-definitions.lean`).
public import Vocabulary.Parabolic
public import Vocabulary.Classical
public import Vocabulary.Viscosity

@[expose] public section

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
