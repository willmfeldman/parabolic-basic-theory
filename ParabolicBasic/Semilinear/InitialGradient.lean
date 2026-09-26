/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Iteration.Interior
public import ParabolicBasic.Comparison.LinearSource
public import ParabolicBasic.Classical.ToViscosity
public import ParabolicBasic.Viscosity.Invariance
public import ParabolicBasic.Barriers.Heat

/-!
# Continuity of `∇ₓu` up to `t = 0`

Let `U` be open, `f` jointly continuous, `g ∈ C²` and `u` a solution of the semilinear
Cauchy–Dirichlet problem with data `g`.
With `v := u - g` and `H_v := Δg - f(x, u)`:

* `IsSemilinearSolution.isHeatSolOn_sub`: `v` solves `dₜv − lapₓv = H_v` in the viscosity sense on
  `U × (0, ∞)` (classical ⇒ viscosity with the *frozen* source `f(x, u(x, t))`, then adding the
  `C²` function `-g`; no freeze lemma is needed);
* `IsSemilinearSolution.exists_initial_bounds`: the explicit barrier
  `A (‖x − y‖² + (2d + 1) t) + M t` and comparison with a linear source give `|v(y, t)| ≤ C t`
  near `(x₀, 0)`;
* `IsSemilinearSolution.tendsto_gradₓ_sub_initial`: the scaled gradient bound J(1)
  on `cCyl (x, t) √(t/2)` gives `‖∇ₓu(x, t) − ∇g(x)‖ ≤ C' √(t/2)`;
* `IsSemilinearSolution.continuousOn_gradₓ`: `∇ₓu` is continuous on `U × [0, ∞)`.

No heat kernel is used. Everything holds for `d = 0` (then `ball = univ` and the lateral face of
the barrier comparison is empty).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Laplacian Gradient

namespace ParabolicBasic

variable {d : ℕ}

/-! ### `C²` data -/

/-- The gradient of a `C²` (indeed `C¹`) function is continuous. -/
theorem continuous_gradient_of_contDiff_two {g : E d → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (∇ g) := by
  have h : ∇ g = fun x ↦ (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ g x) := rfl
  rw [h]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp (hg.continuous_fderiv (by simp))

/-- The Laplacian of a `C²` function is continuous. -/
theorem continuous_laplacian_of_contDiff_two {g : E d → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (Δ g) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (continuous_eval_const _).comp (hg.continuous_iteratedFDeriv le_rfl)

/-! ### The equation for `v = u - g` -/

/-- `v := u - g` solves `dₜv − lapₓv = Δg − f(x, u)` in the viscosity sense on `U × (0, ∞)`. -/
theorem IsSemilinearSolution.isHeatSolOn_sub {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ → ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) :
    IsHeatSolOn (U ×ˢ Ioi 0) (fun p ↦ Δ g p.1 - f p.1 (u p)) (fun p ↦ u p - g p.1) := by
  obtain ⟨hC21, heq⟩ := isSemilinearSolOn_iff.1 hu.2.1
  have hΩ : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  have hsub : IsViscSubOn (U ×ˢ Ioi 0) (fun p _ ↦ f p.1 (u p)) u :=
    hC21.isViscSubOn hU isOpen_Ioi fun p hp ↦ by linarith [heq p hp]
  have hsuper : IsViscSuperOn (U ×ˢ Ioi 0) (fun p _ ↦ f p.1 (u p)) u :=
    hC21.isViscSuperOn hU isOpen_Ioi fun p hp ↦ by linarith [heq p hp]
  set φ : E d × ℝ → ℝ := fun p ↦ -g p.1 with hφ
  have hφd : ContDiffOn ℝ 2 φ (U ×ˢ Ioi 0) := (hg.comp contDiff_fst).neg.contDiffOn
  have hdt : ∀ p, dₜ φ p = 0 := fun p ↦ by simp [dₜ, hφ]
  have hlap : ∀ p, lapₓ φ p = -Δ g p.1 := fun p ↦ by
    change Δ (-g) p.1 = _
    rw [InnerProductSpace.laplacian_neg]
    rfl
  have hfun : (fun p ↦ u p + φ p) = fun p ↦ u p - g p.1 := by
    funext p; simp [hφ, sub_eq_add_neg]
  have hsrc : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), ∀ z : ℝ,
      (fun p _ ↦ f p.1 (u p)) p (z - φ p) - (dₜ φ p - lapₓ φ p) =
        -(Δ g p.1 - f p.1 (u p)) := fun p _ z ↦ by
    simp only [hdt, hlap]; ring
  refine ⟨?_, ?_⟩
  · have h := hsub.add_contDiff hΩ hφd
    rw [hfun] at h
    exact h.mono_source fun p hp z ↦ (hsrc p hp z).ge
  · have h := hsuper.add_contDiff hΩ hφd
    rw [hfun] at h
    exact h.mono_source fun p hp z ↦ (hsrc p hp z).le

/-! ### The barrier -/

/-- The initial barrier profile `A (‖x − y‖² + (2d + 1) t)` (`isSepBarrier_initial`, scaled). -/
noncomputable def r21Barrier (y : E d) (A : ℝ) (q : E d × ℝ) : ℝ :=
  A * (‖q.1 - y‖ ^ 2 + (2 * d + 1) * q.2)

theorem contDiff_r21Barrier (y : E d) (A : ℝ) : ContDiff ℝ 2 (r21Barrier y A) :=
  contDiff_const.mul (((contDiff_norm_sub_sq y).comp contDiff_fst).add
    (contDiff_const.mul contDiff_snd))

/-- `dₜ b − lapₓ b = A` for the barrier profile (valid for `d = 0`). -/
theorem heat_r21Barrier (y : E d) (A : ℝ) (p : E d × ℝ) :
    dₜ (r21Barrier y A) p - lapₓ (r21Barrier y A) p = A := by
  have e : r21Barrier y A = fun q : E d × ℝ ↦
      0 + A * (‖q.1 - y‖ ^ 2 + (2 * d + 1) * q.2) := by
    funext q; simp [r21Barrier]
  have hτ : DifferentiableAt ℝ (fun t : ℝ ↦ (2 * (d : ℝ) + 1) * t) p.2 :=
    (differentiableAt_id.const_mul _)
  have hτ' : deriv (fun t : ℝ ↦ (2 * (d : ℝ) + 1) * t) p.2 = 2 * d + 1 := by
    have := (hasDerivAt_id' p.2).const_mul ((2 : ℝ) * d + 1)
    exact this.deriv.trans (by ring)
  have h1 := dₜ_const_add_mul_sep (fun x : E d ↦ ‖x - y‖ ^ 2) 0 A hτ
  have h2 := lapₓ_const_add_mul_sep (fun t : ℝ ↦ (2 * (d : ℝ) + 1) * t) 0 A
    ((contDiff_norm_sub_sq y (n := 2)).contDiffAt (x := p.1))
  rw [e, h1, h2, hτ', laplacian_norm_sub_sq, finrank_euclideanSpace_fin]
  ring

theorem r21Barrier_center (y : E d) (A t : ℝ) :
    r21Barrier y A (y, t) = A * (2 * d + 1) * t := by
  simp [r21Barrier]; ring

/-- **Barrier bound** (with the local bounds used for the gradient limit). Near `x₀ ∈ U` there are
`r > 0`, `C, M ≥ 0` with `closedBall x₀ (2r) ⊆ U`, `|Δg − f(x, u)| ≤ M` on
`closedBall x₀ (2r) × [0, 2]`, and `|u(y, t) − g(y)| ≤ C t` for `y ∈ ball x₀ r`, `t ∈ [0, 2)`. -/
theorem IsSemilinearSolution.exists_initial_bounds {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ → ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}
    (hf : Continuous (fun q : E d × ℝ ↦ f q.1 q.2)) (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) {x₀ : E d} (hx₀ : x₀ ∈ U) :
    ∃ r C M : ℝ, 0 < r ∧ 0 ≤ C ∧ 0 ≤ M ∧ closedBall x₀ (2 * r) ⊆ U ∧
      (∀ p ∈ closedBall x₀ (2 * r) ×ˢ Icc (0 : ℝ) 2, |Δ g p.1 - f p.1 (u p)| ≤ M) ∧
      ∀ y ∈ ball x₀ r, ∀ t ∈ Ico (0 : ℝ) 2, |u (y, t) - g y| ≤ C * t := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set r := ε / 3 with hr_def
  have hr : 0 < r := by positivity
  have hball : closedBall x₀ (2 * r) ⊆ U :=
    (closedBall_subset_ball (by rw [hr_def]; linarith)).trans hεU
  set Kset : Set (E d × ℝ) := closedBall x₀ (2 * r) ×ˢ Icc (0 : ℝ) 2 with hKset
  have hKc : IsCompact Kset := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKsub : Kset ⊆ closure U ×ˢ Ici 0 := fun p hp ↦
    ⟨subset_closure (hball hp.1), hp.2.1⟩
  set v : E d × ℝ → ℝ := fun p ↦ u p - g p.1 with hv
  set Hv : E d × ℝ → ℝ := fun p ↦ Δ g p.1 - f p.1 (u p) with hHv
  have hgc : Continuous (fun p : E d × ℝ ↦ g p.1) := hg.continuous.comp continuous_fst
  have hvc : ContinuousOn v (closure U ×ˢ Ici 0) := hu.1.sub hgc.continuousOn
  have hHvc : ContinuousOn Hv Kset :=
    ((continuous_laplacian_of_contDiff_two hg).comp continuous_fst).continuousOn.sub
      (hf.comp_continuousOn (continuous_fst.continuousOn.prodMk (hu.1.mono hKsub)))
  obtain ⟨K, hK⟩ := hKc.exists_bound_of_continuousOn (hvc.mono hKsub)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hHvc
  set K' := max K 0
  set M' := max M 0
  have hK' : ∀ p ∈ Kset, |v p| ≤ K' := fun p hp ↦ (hK p hp).trans (le_max_left _ _)
  have hM' : ∀ p ∈ Kset, |Hv p| ≤ M' := fun p hp ↦ (hM p hp).trans (le_max_left _ _)
  have hK0 : 0 ≤ K' := le_max_right _ _
  have hM0 : 0 ≤ M' := le_max_right _ _
  set A := K' / r ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hAr : A * r ^ 2 = K' := by rw [hA]; field_simp
  have hvsol := hu.isHeatSolOn_sub hU hg
  refine ⟨r, A * (2 * d + 1) + M', M', hr, by positivity, hM0, hball, hM', ?_⟩
  intro y hy t ht
  have hyr : ∀ z ∈ closedBall y r, z ∈ closedBall x₀ (2 * r) := fun z hz ↦ by
    rw [mem_closedBall] at hz ⊢
    have := dist_triangle z y x₀
    have := (mem_ball.1 hy).le
    linarith
  have hVo : IsOpen (ball y r) := isOpen_ball
  have hVb : Bornology.IsBounded (ball y r) := isBounded_ball
  have hcl : closure (ball y r) ×ˢ Icc (0 : ℝ) 2 ⊆ Kset := fun p hp ↦
    ⟨hyr _ (closure_ball_subset_closedBall hp.1), hp.2⟩
  have hbox : ball y r ×ˢ Ioo (0 : ℝ) 2 ⊆ U ×ˢ Ioi 0 := fun p hp ↦
    ⟨hball (hyr _ (ball_subset_closedBall hp.1)), hp.2.1⟩
  have hboxK : ball y r ×ˢ Ioo (0 : ℝ) 2 ⊆ Kset := fun p hp ↦
    ⟨hyr _ (ball_subset_closedBall hp.1), Ioo_subset_Icc_self hp.2⟩
  have hbo : IsOpen (ball y r ×ˢ Ioo (0 : ℝ) 2) := hVo.prod isOpen_Ioo
  have hvcl : ContinuousOn v (closure (ball y r) ×ˢ Icc (0 : ℝ) 2) :=
    hvc.mono (hcl.trans hKsub)
  have hbc : ∀ B, Continuous (r21Barrier y B) := fun B ↦ (contDiff_r21Barrier y B).continuous
  -- the parabolic boundary
  have hbdry : ∀ p ∈ parBdry (ball y r) 0 2,
      (p.2 = 0 ∧ v p = 0) ∨ (‖p.1 - y‖ = r ∧ p ∈ Kset) := by
    rintro ⟨x, s⟩ (⟨hx, hs⟩ | ⟨hx, hs⟩)
    · left
      have hs0 : s = 0 := hs
      subst hs0
      refine ⟨rfl, ?_⟩
      simp only [hv]
      rw [hu.2.2.1 x (closure_mono (ball_subset_closedBall.trans
        (fun z hz ↦ hball (hyr z hz))) hx)]
      ring
    · right
      have hxs := frontier_ball_subset_sphere hx
      rw [mem_sphere_iff_norm] at hxs
      exact ⟨hxs, hyr x (by rw [mem_closedBall, dist_eq_norm, hxs]), hs⟩
  have hymem : (y, t) ∈ closure (ball y r) ×ˢ Ico (0 : ℝ) 2 :=
    ⟨subset_closure (mem_ball_self hr), ht⟩
  -- upper bound
  have hup := sub_le_of_heat_source (u := v) (v := r21Barrier y A) (H₁ := Hv)
    (H₂ := fun _ ↦ A) (σ := fun _ ↦ A) hVo hVb two_pos hM0 continuousOn_const
    (fun p hp ↦ by linarith [(abs_le.1 (hM' p (hboxK hp))).2]) (fun _ _ ↦ le_rfl)
    hvcl.upperSemicontinuousOn (hbc A).continuousOn.lowerSemicontinuousOn
    (hvsol.1.mono_set hbo hbox)
    (isViscSuperOn_of_contDiffOn hbo (contDiff_r21Barrier y A).contDiffOn fun p _ ↦ by
      rw [heat_r21Barrier]; simp)
    (fun p hp ↦ by
      rcases hbdry p hp with ⟨h2, h0⟩ | ⟨h1, hpK⟩
      · rw [h0]
        simp only [r21Barrier, h2, mul_zero, add_zero]
        positivity
      · have := (abs_le.1 (hK' p hpK)).2
        have hs : 0 ≤ A * ((2 * d + 1) * p.2) := mul_nonneg hA0 (by positivity [hpK.2.1])
        simp only [r21Barrier, h1, mul_add]
        linarith)
    (y, t) hymem
  -- lower bound
  have hlo := sub_le_of_heat_source (u := r21Barrier y (-A)) (v := v) (H₁ := fun _ ↦ -A)
    (H₂ := Hv) (σ := fun _ ↦ -A - M') hVo hVb two_pos hM0 continuousOn_const
    (fun _ _ ↦ by linarith)
    (fun p hp ↦ by linarith [(abs_le.1 (hM' p (hboxK hp))).1])
    (hbc (-A)).continuousOn.upperSemicontinuousOn hvcl.lowerSemicontinuousOn
    (isViscSubOn_of_contDiffOn hbo (contDiff_r21Barrier y (-A)).contDiffOn fun p _ ↦ by
      rw [heat_r21Barrier]; simp)
    (hvsol.2.mono_set hbo hbox)
    (fun p hp ↦ by
      rcases hbdry p hp with ⟨h2, h0⟩ | ⟨h1, hpK⟩
      · rw [h0]
        simp only [r21Barrier, h2, mul_zero, add_zero]
        have : 0 ≤ A * ‖p.1 - y‖ ^ 2 := by positivity
        linarith
      · have := (abs_le.1 (hK' p hpK)).1
        have hs : 0 ≤ A * ((2 * d + 1) * p.2) := mul_nonneg hA0 (by positivity [hpK.2.1])
        simp only [r21Barrier, h1, neg_mul, mul_add]
        linarith)
    (y, t) hymem
  rw [r21Barrier_center] at hup hlo
  simp only [hv, sub_zero] at hup hlo
  rw [abs_le]
  constructor <;> linarith

/-- **Barrier bound.** Near `x₀ ∈ U`, `|u(y, t) − g(y)| ≤ C t` for `y ∈ ball x₀ r`, `t ∈ [0, T]`. -/
theorem IsSemilinearSolution.abs_sub_initial_le {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ → ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}
    (hf : Continuous (fun q : E d × ℝ ↦ f q.1 q.2)) (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) {x₀ : E d} (hx₀ : x₀ ∈ U) :
    ∃ r T C : ℝ, 0 < r ∧ 0 < T ∧ ∀ y ∈ ball x₀ r, ∀ t ∈ Icc 0 T, |u (y, t) - g y| ≤ C * t := by
  obtain ⟨r, C, M, hr, -, -, -, -, h⟩ := hu.exists_initial_bounds hU hf hg hx₀
  exact ⟨r, 1, C, hr, one_pos, fun y hy t ht ↦ h y hy t ⟨ht.1, by linarith [ht.2]⟩⟩

/-! ### The gradient limit -/

/-- At `t = 0`, `∇ₓu(x, 0) = ∇g(x)` for `x ∈ U` (the slice `u(·, 0)` equals `g` near `x`). -/
theorem IsSemilinearSolution.gradₓ_initial {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ → ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}
    (hu : IsSemilinearSolution U f g u) {x : E d} (hx : x ∈ U) : gradₓ u (x, 0) = ∇ g x := by
  change ∇ (fun y ↦ u (y, 0)) x = ∇ g x
  refine Filter.EventuallyEq.gradient_eq ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hu.2.2.1 y (subset_closure hy)

/-- **Gradient limit.** `∇ₓu(x, t) − ∇g(x) → 0` as `(x, t) → (x₀, 0)` with `t > 0`. -/
theorem IsSemilinearSolution.tendsto_gradₓ_sub_initial {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ → ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}
    (hf : Continuous (fun q : E d × ℝ ↦ f q.1 q.2)) (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) {x₀ : E d} (hx₀ : x₀ ∈ U) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ball x₀ δ, ∀ t ∈ Ioo 0 δ, ‖gradₓ u (x, t) - ∇ g x‖ < ε := by
  obtain ⟨r, C, M, hr, hC, hM0, hball, hM, hbar⟩ := hu.exists_initial_bounds hU hf hg hx₀
  obtain ⟨CJ, hCJ, hJ⟩ := gradₓ_bound_of_isHeatSolOn (d := d)
  have hvsol := hu.isHeatSolOn_sub hU hg
  set L := CJ * (3 * C + M) + 1 with hL
  have hL0 : 0 < L := by positivity
  intro ε hε
  refine ⟨min (r / 2) (min 1 (min (r ^ 2 / 2) (2 * (ε / L) ^ 2))), by positivity, ?_⟩
  intro x hx t ht
  have hxr : dist x x₀ < r / 2 := (mem_ball.1 hx).trans_le (min_le_left _ _)
  have ht1 : t < 1 := ht.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htr : t < r ^ 2 / 2 :=
    ht.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hte : t ≤ 2 * (ε / L) ^ 2 :=
    ht.2.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ht0 : 0 < t := ht.1
  set ρ := Real.sqrt (t / 2) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have hρ2 : ρ ^ 2 = t / 2 := Real.sq_sqrt (by positivity)
  have hρr : ρ < r / 2 := (Real.sqrt_lt' (by positivity)).2 (by nlinarith)
  have hρe : ρ ≤ ε / L := by
    rw [hρ]
    calc Real.sqrt (t / 2) ≤ Real.sqrt ((ε / L) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = ε / L := Real.sqrt_sq (by positivity)
  -- the cylinder and its closure
  have hsub1 : ∀ z ∈ closedBall x ρ, z ∈ ball x₀ r := fun z hz ↦ by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    have := dist_triangle z x x₀
    linarith
  have hcl : closure (cCyl x t ρ) = closedBall x ρ ×ˢ Icc (t - ρ ^ 2) (t + ρ ^ 2) :=
    closure_cCyl x t hρ0
  have hclU : closure (cCyl x t ρ) ⊆ U ×ˢ Ioi 0 := by
    rw [hcl]
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    refine ⟨hball (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
      (hsub1 z hz)), ?_⟩
    change 0 < s
    linarith [hs.1]
  have hcylU : cCyl x t ρ ⊆ U ×ˢ Ioi 0 := subset_closure.trans hclU
  have hcylK : cCyl x t ρ ⊆ closedBall x₀ (2 * r) ×ˢ Icc (0 : ℝ) 2 := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    refine ⟨ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
      (hsub1 z (ball_subset_closedBall hz)), ?_, ?_⟩
    · linarith [hs.1]
    · linarith [hs.2]
  have hvc : ContinuousOn (fun p : E d × ℝ ↦ u p - g p.1) (closure (cCyl x t ρ)) :=
    (hu.1.mono (hclU.trans fun p hp ↦ ⟨subset_closure hp.1, mem_Ici.2 (le_of_lt hp.2)⟩)).sub
      (hg.continuous.comp continuous_fst).continuousOn
  have hco : IsOpen (cCyl x t ρ) := isOpen_cCyl x t ρ
  have hsol : IsHeatSolOn (cCyl x t ρ) (fun p ↦ Δ g p.1 - f p.1 (u p))
      (fun p ↦ u p - g p.1) :=
    ⟨hvsol.1.mono_set hco hcylU, hvsol.2.mono_set hco hcylU⟩
  have hS : ∀ q ∈ cCyl x t ρ, |u q - g q.1| ≤ C * (3 * t / 2) := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    have hs' : s ∈ Ico (0 : ℝ) 2 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    calc |u (z, s) - g z| ≤ C * s := hbar z (hsub1 z (ball_subset_closedBall hz)) s hs'
      _ ≤ C * (3 * t / 2) := by gcongr; linarith [hs.2]
  have hHM : ∀ q ∈ cCyl x t ρ, |Δ g q.1 - f q.1 (u q)| ≤ M := fun q hq ↦ hM q (hcylK hq)
  obtain ⟨hgradv, hnorm⟩ := hJ (p := (x, t)) hρ0 hvc hsol hS hHM
  -- `∇ₓu = ∇ₓv + ∇g`
  have hgg : HasGradientAt g (∇ g x) x :=
    ((hg.differentiable (by simp)) x).hasGradientAt
  have hsum : HasGradientAt (fun y ↦ u (y, t))
      (gradₓ (fun p : E d × ℝ ↦ u p - g p.1) (x, t) + ∇ g x) x := by
    have h := (hasGradientAt_iff_hasFDerivAt.1 hgradv).add (hasGradientAt_iff_hasFDerivAt.1 hgg)
    rw [← map_add] at h
    refine hasGradientAt_iff_hasFDerivAt.2 ?_
    convert h using 1
    funext y
    simp
  have hgu : gradₓ u (x, t) = gradₓ (fun p : E d × ℝ ↦ u p - g p.1) (x, t) + ∇ g x :=
    hsum.gradient
  rw [hgu, add_sub_cancel_right]
  have hbound : C * (3 * t / 2) / ρ + M * ρ = (3 * C + M) * ρ := by
    have ht2 : t = 2 * ρ ^ 2 := by rw [hρ2]; ring
    rw [ht2]
    field_simp
  rw [hbound] at hnorm
  calc ‖gradₓ (fun p : E d × ℝ ↦ u p - g p.1) (x, t)‖ ≤ CJ * ((3 * C + M) * ρ) := hnorm
    _ < L * ρ := by rw [hL]; nlinarith
    _ ≤ L * (ε / L) := by gcongr
    _ = ε := by field_simp

/-! ### Continuity of the gradient up to `t = 0` -/

/-- `∇ₓu` is continuous on `U × [0, ∞)`. -/
theorem IsSemilinearSolution.continuousOn_gradₓ {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ → ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}
    (hf : Continuous (fun q : E d × ℝ ↦ f q.1 q.2)) (hg : ContDiff ℝ 2 g)
    (hu : IsSemilinearSolution U f g u) :
    ContinuousOn (gradₓ u) (U ×ˢ Ici 0) := by
  rintro ⟨x₀, t₀⟩ ⟨hx₀, ht₀⟩
  rcases (mem_Ici.1 ht₀).lt_or_eq with htpos | rfl
  · have hopen : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
    have hmem : (x₀, t₀) ∈ U ×ˢ Ioi (0 : ℝ) := ⟨hx₀, htpos⟩
    exact (hu.2.1.2.2.1.continuousAt (hopen.mem_nhds hmem)).continuousWithinAt
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hgrad⟩ := hu.tendsto_gradₓ_sub_initial hU hf hg hx₀ (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, hcont⟩ :=
      Metric.continuous_iff.1 (continuous_gradient_of_contDiff_two hg) x₀ (ε / 2) (half_pos hε)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    rintro ⟨x, t⟩ ⟨hx, ht⟩ hq
    rw [Prod.dist_eq, max_lt_iff] at hq
    obtain ⟨hqx, hqt⟩ := hq
    have ht0 : 0 ≤ t := ht
    rw [hu.gradₓ_initial hU hx₀]
    have h2 : dist (∇ g x) (∇ g x₀) < ε / 2 := hcont x (hqx.trans_le (min_le_right _ _))
    have h1 : dist (gradₓ u (x, t)) (∇ g x) < ε / 2 := by
      rcases ht0.lt_or_eq with htp | rfl
      · rw [dist_eq_norm]
        refine hgrad x (mem_ball.2 (hqx.trans_le (min_le_left _ _))) t ⟨htp, ?_⟩
        have := hqt.trans_le (min_le_left _ _)
        rwa [Real.dist_eq, sub_zero, abs_of_pos htp] at this
      · rw [hu.gradₓ_initial hU hx, dist_self]
        exact half_pos hε
    calc dist (gradₓ u (x, t)) (∇ g x₀) ≤ dist (gradₓ u (x, t)) (∇ g x) + dist (∇ g x) (∇ g x₀) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε

end ParabolicBasic
