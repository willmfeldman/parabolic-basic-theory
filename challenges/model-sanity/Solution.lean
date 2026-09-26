import ParabolicBasic.Defs.Parabolic
import ParabolicBasic.Classical.ToViscosity
import ParabolicBasic.Barriers.Radial
import ParabolicBasic.Calculus.Slice
import ParabolicBasic.Analysis.Partials

/-!
# Solution: sign convention, non-vacuity and parabolic-boundary model cases

Short direct proofs, using the library's slice calculus (`Calculus/Slice`, `Analysis/Partials`),
the radial Laplacian `laplacian_norm_sub_sq`, and `isViscSuperOn_of_contDiffOn` from
`Classical/ToViscosity`.
-/

open Set Metric
open scoped Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-- `∂ₜt = 1`. -/
private theorem dₜ_snd (p : E d × ℝ) : dₜ (fun q : E d × ℝ ↦ q.2) p = 1 := by
  simp [dₜ]

/-- `Δₓt = 0`. -/
private theorem lapₓ_snd (p : E d × ℝ) : lapₓ (fun q : E d × ℝ ↦ q.2) p = 0 := by
  simp [lapₓ]

theorem challenge_time_not_viscSub :
    ¬ IsViscSubOn (ball (0 : E d) 1 ×ˢ Ioo 0 1) (fun _ _ ↦ 0) (fun p ↦ p.2) := by
  rintro ⟨-, h⟩
  have hp : ((0 : E d), (1 / 2 : ℝ)) ∈ ball (0 : E d) 1 ×ˢ Ioo (0 : ℝ) 1 :=
    ⟨mem_ball_self one_pos, by norm_num, by norm_num⟩
  have := h (fun q ↦ q.2) contDiff_snd _ hp
    ⟨hp, rfl, Filter.Eventually.of_forall fun _ ↦ le_rfl⟩
  rw [dₜ_snd, lapₓ_snd] at this
  norm_num at this

theorem challenge_time_viscSuper :
    IsViscSuperOn (ball (0 : E d) 1 ×ˢ Ioo 0 1) (fun _ _ ↦ 0) (fun p ↦ p.2) :=
  isViscSuperOn_of_contDiffOn (isOpen_ball.prod isOpen_Ioo) contDiff_snd.contDiffOn
    fun p _ ↦ by rw [dₜ_snd, lapₓ_snd]; norm_num

theorem challenge_caloric_quadratic_solOn :
    IsSemilinearSolOn univ (fun _ _ ↦ 0) univ (fun p : E d × ℝ ↦ ‖p.1‖ ^ 2 + 2 * d * p.2) := by
  set u : E d × ℝ → ℝ := fun p ↦ ‖p.1‖ ^ 2 + 2 * d * p.2 with hu_def
  have hu : ContDiff ℝ 2 u :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).add (contDiff_const.mul contDiff_snd)
  refine ⟨hu.continuous.continuousOn, fun t _ ↦ (contDiff_sliceX hu t).contDiffOn,
    (continuous_gradₓ (hu.of_le one_le_two)).continuousOn,
    continuousOn_iteratedFDeriv_sliceX (isOpen_univ.prod isOpen_univ) hu.contDiffOn,
    fun p _ ↦ differentiableAt_sliceT (hu.differentiable two_ne_zero p),
    (continuous_dₜ (hu.of_le one_le_two)).continuousOn, fun p _ ↦ ?_⟩
  have hdt : dₜ u p = 2 * d :=
    (((hasDerivAt_id p.2).const_mul (2 * (d : ℝ))).const_add (‖p.1‖ ^ 2)).deriv.trans (mul_one _)
  have hlap : lapₓ u p = 2 * d := by
    have h1 := laplacian_const_mul_add_const (g := fun y : E d ↦ ‖y - 0‖ ^ 2) (x := p.1)
      (contDiff_norm_sub_sq 0).contDiffAt 1 (2 * d * p.2)
    simp only [sub_zero, one_mul] at h1
    have h2 := laplacian_norm_sub_sq (z := (0 : E d)) p.1
    simp only [sub_zero, finrank_euclideanSpace_fin] at h2
    simp only [lapₓ, hu_def]
    rw [h1, h2]
  simp [hdt, hlap]

theorem challenge_parBdry_ball_nonempty :
    parBdry (ball (0 : E d) 1) 0 1 = closedBall 0 1 ×ˢ {0} ∪ sphere 0 1 ×ˢ Icc 0 1 ∧
      (parBdry (ball (0 : E d) 1) 0 1).Nonempty := by
  refine ⟨by rw [parBdry, closure_ball 0 one_ne_zero, frontier_ball 0 one_ne_zero], ?_⟩
  exact ⟨((0 : E d), 0), Or.inl ⟨subset_closure (mem_ball_self one_pos), rfl⟩⟩

end ParabolicBasic
