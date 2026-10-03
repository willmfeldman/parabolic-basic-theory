module

public import ParabolicBasic

@[expose] public section

/-!
# Solution: existence for the semilinear Cauchy–Dirichlet problem

Discharges the challenge through the library theorem `ParabolicBasic.semilinear_exists`
(Perron's method with barriers gives a viscosity solution; interior Schauder estimates upgrade it
to a classical one).
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

theorem challenge_semilinear_exists {U : Set (E d)} {f : E d → ℝ → ℝ} {g : E d → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hC2 : HasC2Boundary U)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hfb : ∃ M : ℝ, ∀ x ∈ closure U, ∀ z, |f x z| ≤ M)
    (hg : ∃ L, LipschitzOnWith L g (closure U)) :
    ∃ u : E d × ℝ → ℝ, IsSemilinearSolution U f g u :=
  semilinear_exists hU hUb hC2 hfx hfz hfb hg

end ParabolicBasic
