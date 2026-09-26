import ParabolicBasic

/-!
# Solution: regularity for the semilinear heat equation

Discharges the challenge through the library theorems
`ParabolicBasic.semilinear_contDiffOn_of_contDiff` (difference-quotient bootstrap on interior
Schauder estimates) and `ParabolicBasic.semilinear_continuousOn_gradₓ_of_contDiff`.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

theorem challenge_semilinear_smooth {U : Set (E d)} {I : Set ℝ} {f : E d → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (hf : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ f q.1 q.2)) (hu : IsSemilinearSolOn U f I u) :
    ContDiffOn ℝ ∞ u (U ×ˢ I) :=
  semilinear_contDiffOn_of_contDiff hU hI hf hu

theorem challenge_semilinear_gradient_continuous {U : Set (E d)} {f : E d → ℝ → ℝ}
    {g : E d → ℝ} {u : E d × ℝ → ℝ} (hU : IsOpen U)
    (hf : Continuous (fun q : E d × ℝ ↦ f q.1 q.2)) (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) :
    ContinuousOn (gradₓ u) (U ×ˢ Ici 0) :=
  semilinear_continuousOn_gradₓ_of_contDiff hU hf hg hu

end ParabolicBasic
