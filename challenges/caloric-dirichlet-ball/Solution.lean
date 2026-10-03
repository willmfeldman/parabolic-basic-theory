module

public import ParabolicBasic.MainTheorems

@[expose] public section

/-!
# Solution: the Dirichlet problem for the heat equation on a ball cylinder

Discharges the challenge through the library theorem `ParabolicBasic.caloric_dirichlet_ball`.
The library states the boundary through `parBdry (ball x₀ ρ) a b`, i.e. with `closure (ball x₀ ρ)`
and `frontier (ball x₀ ρ)`; Mathlib's `closure_ball` and `frontier_ball` (for `ρ ≠ 0`) identify
these with `closedBall x₀ ρ` and `sphere x₀ ρ`. The equation `dₜ h = lapₓ h` unfolds definitionally
to the slice form `deriv (fun s ↦ h (x, s)) t = Δ (fun y ↦ h (y, t)) x`.
-/

open Set Metric
open scoped ContDiff Laplacian

namespace ParabolicBasic

theorem challenge_caloric_dirichlet_ball {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d)) {ρ : ℝ}
    (hρ : 0 < ρ) {a b : ℝ} (hab : a < b) {g : EuclideanSpace ℝ (Fin d) × ℝ → ℝ}
    (hg : ContinuousOn g (closedBall x₀ ρ ×ˢ {a} ∪ sphere x₀ ρ ×ˢ Icc a b)) :
    ∃ h : EuclideanSpace ℝ (Fin d) × ℝ → ℝ,
      ContinuousOn h (closedBall x₀ ρ ×ˢ Icc a b) ∧
      ContDiffOn ℝ ∞ h (ball x₀ ρ ×ˢ Ioo a b) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t ∈ Ioo a b,
        deriv (fun s ↦ h (x, s)) t = Δ (fun y ↦ h (y, t)) x) ∧
      (∀ x ∈ closedBall x₀ ρ, h (x, a) = g (x, a)) ∧
      (∀ x ∈ sphere x₀ ρ, ∀ t ∈ Icc a b, h (x, t) = g (x, t)) := by
  have hP : parBdry (ball x₀ ρ) a b = closedBall x₀ ρ ×ˢ {a} ∪ sphere x₀ ρ ×ˢ Icc a b := by
    rw [parBdry, closure_ball x₀ hρ.ne', frontier_ball x₀ hρ.ne']
  obtain ⟨h, hc, hsmooth, hcal, heq⟩ := caloric_dirichlet_ball x₀ hρ hab (hP ▸ hg)
  rw [hP] at heq
  refine ⟨h, hc, hsmooth, fun x hx t ht ↦ hcal (x, t) ⟨hx, ht⟩, fun x hx ↦ ?_,
    fun x hx t ht ↦ ?_⟩
  · exact heq (Or.inl ⟨hx, rfl⟩)
  · exact heq (Or.inr ⟨hx, ht⟩)

end ParabolicBasic
