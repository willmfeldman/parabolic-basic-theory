import ParabolicBasic.MainTheorems

/-!
# Solution: classical solutions of the semilinear heat equation are viscosity solutions

Discharges the challenge through the library theorems
`ParabolicBasic.isSemilinearViscSubOn_of_solOn` and
`ParabolicBasic.isSemilinearViscSuperOn_of_solOn`.
-/

open Set

namespace ParabolicBasic

variable {d : ℕ}

theorem challenge_classical_viscSub {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSubOn U f I u :=
  isSemilinearViscSubOn_of_solOn hU hI hu

theorem challenge_classical_viscSuper {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSuperOn U f I u :=
  isSemilinearViscSuperOn_of_solOn hU hI hu

end ParabolicBasic
