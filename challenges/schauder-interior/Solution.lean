module

public import ParabolicBasic

@[expose] public section

/-!
# Solution: interior Schauder regularity for the heat equation

Discharges the challenge through the library theorem `ParabolicBasic.schauder_interior`
(the `L^∞` Campanato iteration of `ParabolicBasic.Schauder.Iteration`).
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

theorem challenge_schauder_interior {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {u H : E d × ℝ → ℝ}
    (hu : ContinuousOn u (U ×ˢ I)) (hsol : IsHeatSolOn (U ×ˢ I) H u)
    (hH : ContinuousOn H (U ×ˢ I)) (hHα : LocHolderOnPar α H (U ×ˢ I)) :
    IsC21On U I u ∧ (∀ p ∈ U ×ˢ I, dₜ u p - lapₓ u p = H p) ∧
      LocHolderOnPar α (dₜ u) (U ×ˢ I) ∧
      (∀ i, LocHolderOnPar α (fun p ↦ gradₓ u p i) (U ×ˢ I)) ∧
      ∀ i j, LocHolderOnPar α (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (U ×ˢ I) :=
  schauder_interior hU hI hα hu hsol hH hHα

end ParabolicBasic
