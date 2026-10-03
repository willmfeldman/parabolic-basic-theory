module

public import ParabolicBasic.MainTheorems

@[expose] public section

/-!
# Solution: comparison and uniqueness for the semilinear heat equation

Discharges the challenge through the library theorems `ParabolicBasic.semilinear_comparison` and
`ParabolicBasic.semilinear_unique`. The sanity check `challenge_parBdry_ball_nonempty` unfolds
`parBdry`.
-/

open Set Metric

namespace ParabolicBasic

variable {d : ℕ}

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
    ∀ p ∈ closure V ×ˢ Icc a b, u p ≤ v p :=
  semilinear_comparison hV hVb hab hfx hfz hu hv hsub hsuper hbdry

theorem challenge_semilinear_unique {U : Set (E d)} {f : E d → ℝ → ℝ} {g : E d → ℝ}
    {u v : E d × ℝ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure U, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    (hu : IsSemilinearSolution U f g u) (hv : IsSemilinearSolution U f g v) :
    ∀ p ∈ closure U ×ˢ Ici (0 : ℝ), u p = v p :=
  semilinear_unique hU hUb hfx hfz hu hv

theorem challenge_parBdry_ball_nonempty :
    parBdry (ball (0 : E d) 1) 0 1 = closedBall 0 1 ×ˢ {0} ∪ sphere 0 1 ×ˢ Icc 0 1 ∧
      (parBdry (ball (0 : E d) 1) 0 1).Nonempty := by
  refine ⟨by rw [parBdry, closure_ball 0 one_ne_zero, frontier_ball 0 one_ne_zero], ?_⟩
  exact ⟨((0 : E d), 0), Or.inl ⟨subset_closure (mem_ball_self one_pos), rfl⟩⟩

end ParabolicBasic
