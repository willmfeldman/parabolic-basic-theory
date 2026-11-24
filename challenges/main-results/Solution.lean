module

public import ParabolicBasic

@[expose] public section

/-!
# Solution: the main results of the library

Discharges every statement of `Challenge.lean` through the library. Each section below is the
proof of the matching section of `Challenge.lean`.
-/

section CaloricDirichletBall

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

end CaloricDirichletBall

section SemilinearComparison

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

end SemilinearComparison

section ClassicalViscosity

/-!
# Solution: classical solutions of the semilinear heat equation are viscosity solutions

Discharges the challenge through the library theorems
`ParabolicBasic.isSemilinearViscSubOn_of_solOn` and
`ParabolicBasic.isSemilinearViscSuperOn_of_solOn`. The sanity checks have short direct
proofs, using the library's slice calculus (`Calculus/Slice`, `Analysis/Partials`), the radial Laplacian
`laplacian_norm_sub_sq`, and `isViscSuperOn_of_contDiffOn` from `Classical/ToViscosity`.
-/

open Set Metric
open scoped Laplacian

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

end ParabolicBasic

end ClassicalViscosity

section SemilinearExistence

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

end SemilinearExistence

section SemilinearRegularity

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

end SemilinearRegularity

section CaloricSmooth

/-!
# Solution: viscosity solutions of the heat equation are smooth

Discharges the challenge through the library theorem `ParabolicBasic.isSmoothCaloricOn_of_isVisc`.
Its conclusion `IsSmoothCaloricOn O u` is by definition
`ContDiffOn ℝ ∞ u O ∧ ∀ p ∈ O, dₜ u p = lapₓ u p`.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

theorem challenge_caloric_smooth {O : Set (E d × ℝ)} (hO : IsOpen O) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u O) (hsub : IsViscSubOn O (fun _ _ ↦ 0) u)
    (hsuper : IsViscSuperOn O (fun _ _ ↦ 0) u) :
    ContDiffOn ℝ ∞ u O ∧ ∀ p ∈ O, dₜ u p = lapₓ u p := by
  have h : IsSmoothCaloricOn O u := isSmoothCaloricOn_of_isVisc hO hu hsub hsuper
  exact ⟨h.1, h.2⟩

end ParabolicBasic

end CaloricSmooth

section SchauderInterior

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

end SchauderInterior
