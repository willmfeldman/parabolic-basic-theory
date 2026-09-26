/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.PartitionMollifier
public import ParabolicBasic.Caloric.BernsteinLimit
public import ParabolicBasic.Comparison.SumClosure
public import ParabolicBasic.Viscosity.Stability
public import ParabolicBasic.Viscosity.Classical
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Continuous viscosity caloric functions are smooth

A continuous function that is a viscosity sub- and supersolution of the heat equation
`dₜu - lapₓu = 0` on an open `O ⊆ E d × ℝ` is `C^∞` on `O` and satisfies `dₜu = lapₓu` pointwise
(`IsSmoothCaloricOn O u`).

The proof avoids the heat kernel and Schauder theory:

* `mollifyOn φ K u := φ.normed ⋆ 1_K u` is `C^∞` (`contDiff_mollifyOn`);
* near `p`, it is a uniform limit of finite nonnegative combinations of translates of `u`
  (`exists_finite_weights_approx`), which are viscosity solutions
  (`IsViscSubOn.sum_smul_translate`); by stability it is a viscosity solution, and being smooth it
  is classical (`IsViscSubOn.heat_le_of_contDiffOn`): `IsViscCaloric.mollify_isSmoothCaloricOn`;
* the mollifications converge to `u` uniformly near `p` (`ContDiffBump.dist_normed_convolution_le`)
  and locally uniform limits of smooth caloric functions are smooth caloric
  (`IsSmoothCaloricOn.of_tendstoLocallyUniformlyOn`).

Space-time carries the sup metric, so `closedBall p ρ` is a product box; `d = 0` is included
(mollification is then in `t` only).
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Convolution
open ContinuousLinearMap (lsmul)

namespace ParabolicBasic

variable {d : ℕ}

/-- The mollification `φ.normed ⋆ (1_K u)` of `u` (cut off to `K`) by the normalized bump `φ`
(Lebesgue measure on `E d × ℝ`). -/
noncomputable def mollifyOn (φ : ContDiffBump (0 : E d × ℝ)) (K : Set (E d × ℝ))
    (u : E d × ℝ → ℝ) : E d × ℝ → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] K.indicator u

theorem integrable_indicator_of_continuousOn {K : Set (E d × ℝ)} (hK : IsCompact K)
    {u : E d × ℝ → ℝ} (hu : ContinuousOn u K) : Integrable (K.indicator u) :=
  (hu.integrableOn_compact hK).integrable_indicator hK.measurableSet

/-- The mollification of a function continuous on a compact set is `C^∞`. -/
theorem contDiff_mollifyOn (φ : ContDiffBump (0 : E d × ℝ)) {K : Set (E d × ℝ)}
    (hK : IsCompact K) {u : E d × ℝ → ℝ} (hu : ContinuousOn u K) :
    ContDiff ℝ ∞ (mollifyOn φ K u) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    (integrable_indicator_of_continuousOn hK hu).locallyIntegrable

/-- Away from the cut-off, the mollification is the plain integral `∫ η(w) u(z - w) dw`. -/
theorem mollifyOn_eq_integral (φ : ContDiffBump (0 : E d × ℝ)) {K : Set (E d × ℝ)}
    {u : E d × ℝ → ℝ} {z : E d × ℝ} (hz : ∀ w ∈ closedBall (0 : E d × ℝ) φ.rOut, z - w ∈ K) :
    mollifyOn φ K u z = ∫ w, φ.normed volume w * u (z - w) := by
  rw [mollifyOn, convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  by_cases hw : w ∈ closedBall (0 : E d × ℝ) φ.rOut
  · rw [indicator_of_mem (hz w hw)]
  · have : φ.normed volume w = 0 := Function.notMem_support.1 fun h ↦
      hw (ball_subset_closedBall (φ.support_normed_eq (μ := volume) ▸ h))
    simp [this]

/-- Uniform approximation: if `u` is `ε`-close to `u z` on `ball z φ.rOut ⊆ K`, the
mollification at `z` is `ε`-close to `u z`. -/
theorem dist_mollifyOn_le (φ : ContDiffBump (0 : E d × ℝ)) {K : Set (E d × ℝ)}
    (hK : IsCompact K) {u : E d × ℝ → ℝ} (hu : ContinuousOn u K) {z : E d × ℝ} {ε : ℝ}
    (hzK : ball z φ.rOut ⊆ K) (hε : ∀ x ∈ ball z φ.rOut, dist (u x) (u z) ≤ ε) :
    dist (mollifyOn φ K u z) (u z) ≤ ε := by
  have hz : z ∈ K := hzK (mem_ball_self φ.rOut_pos)
  have := φ.dist_normed_convolution_le (μ := volume) (x₀ := z) (ε := ε)
    (integrable_indicator_of_continuousOn hK hu).aestronglyMeasurable
    (fun x hx ↦ by rw [indicator_of_mem (hzK hx), indicator_of_mem hz]; exact hε x hx)
  rwa [indicator_of_mem hz] at this

theorem IsSmoothCaloricOn.mono_set {O O' : Set (E d × ℝ)} {v : E d × ℝ → ℝ}
    (h : IsSmoothCaloricOn O v) (hO' : O' ⊆ O) : IsSmoothCaloricOn O' v :=
  ⟨h.1.mono hO', fun q hq ↦ h.2 q (hO' hq)⟩

/-- Let `u` be continuous on `O` and a viscosity sub- and
supersolution of the heat equation there, with `closedBall p (3r) ⊆ O`. For a bump `φ` of
outer radius `≤ r`, the mollification `φ.normed ⋆ 1_{closedBall p (3r)} u` is `C^∞` on all of
`E d × ℝ` and smooth caloric on `ball p (2r)`. -/
theorem IsViscCaloric.mollify_isSmoothCaloricOn {O : Set (E d × ℝ)} {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u O) (hsub : IsViscSubOn O (fun _ _ ↦ 0) u)
    (hsuper : IsViscSuperOn O (fun _ _ ↦ 0) u) {p : E d × ℝ} {r : ℝ}
    (hK : closedBall p (3 * r) ⊆ O) (φ : ContDiffBump (0 : E d × ℝ)) (hφ : φ.rOut ≤ r) :
    ContDiff ℝ ∞ (mollifyOn φ (closedBall p (3 * r)) u) ∧
      IsSmoothCaloricOn (ball p (2 * r)) (mollifyOn φ (closedBall p (3 * r)) u) := by
  set K := closedBall p (3 * r) with hK_def
  set v := mollifyOn φ K u with hv_def
  set η := φ.normed (volume : Measure (E d × ℝ)) with hη_def
  have hKc : IsCompact K := isCompact_closedBall p _
  have huK : ContinuousOn u K := hu.mono hK
  have hvC : ContDiff ℝ ∞ v := contDiff_mollifyOn φ hKc huK
  refine ⟨hvC, ?_⟩
  set O' := ball p (2 * r) with hO'_def
  have hadm : ∀ z ∈ O', ∀ w ∈ closedBall (0 : E d × ℝ) φ.rOut, z - w ∈ K := by
    intro z hz w hw
    have h1 : dist (z - w) z = ‖w‖ := by simp
    have h2 : ‖w‖ ≤ φ.rOut := mem_closedBall_zero_iff.1 hw
    have h3 : dist z p < 2 * r := hz
    exact mem_closedBall.2 (by linarith [dist_triangle (z - w) z p])
  have hveq : ∀ z ∈ O', v z = ∫ w, η w * u (z - w) := fun z hz ↦
    mollifyOn_eq_integral φ (hadm z hz)
  have hηs : Function.support η ⊆ closedBall 0 φ.rOut := by
    rw [hη_def, φ.support_normed_eq]; exact ball_subset_closedBall
  have hη1 : ∫ w, η w = 1 := φ.integral_normed
  choose N c w hc hw _ hbd using fun n : ℕ ↦
    exists_finite_weights_approx hKc huK φ.nonneg_normed φ.integrable_normed hηs
      (Nat.one_div_pos_of_nat (n := n) (α := ℝ))
  set S : ℕ → E d × ℝ → ℝ := fun n z ↦ ∑ i, c n i * u (z - w n i) with hS_def
  have hmaps : ∀ n i, ∀ z ∈ O', z - w n i ∈ O := fun n i z hz ↦ hK (hadm z hz _ (hw n i))
  have hSsub : ∀ n, IsViscSubOn O' (fun _ _ ↦ 0) (S n) := fun n ↦
    hsub.sum_smul_translate (c n) (hc n) (w n) isOpen_ball (hmaps n)
  have hSsuper : ∀ n, IsViscSuperOn O' (fun _ _ ↦ 0) (S n) := fun n ↦
    hsuper.sum_smul_translate (c n) (hc n) (w n) isOpen_ball (hmaps n)
  have hconv : TendstoUniformlyOn S v atTop O' := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    refine eventually_atTop.2 ⟨M, fun n hn z hz ↦ ?_⟩
    have hb := hbd n z (hadm z hz)
    rw [hη1, mul_one] at hb
    rw [Real.dist_eq, hveq z hz, abs_sub_comm]
    exact hb.trans_lt ((Nat.one_div_le_one_div hn).trans_lt hM)
  have hF : TendstoLocallyUniformlyOn (fun (_ : ℕ) (_ : (E d × ℝ) × ℝ) ↦ (0 : ℝ))
      (fun _ ↦ 0) atTop (O' ×ˢ univ) :=
    Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε _ _ ↦
      ⟨univ, univ_mem, Eventually.of_forall fun _ _ _ ↦ by simpa using hε⟩
  have hvsub : IsViscSubOn O' (fun _ _ ↦ 0) v :=
    IsViscSubOn.of_tendstoLocallyUniformlyOn isOpen_ball (Fn := fun _ _ _ ↦ 0)
      (Eventually.of_forall hSsub) hconv.tendstoLocallyUniformlyOn
      (hvC.continuous.upperSemicontinuous.upperSemicontinuousOn _) hF continuousOn_const
  have hvsuper : IsViscSuperOn O' (fun _ _ ↦ 0) v :=
    IsViscSuperOn.of_tendstoLocallyUniformlyOn isOpen_ball (Fn := fun _ _ _ ↦ 0)
      (Eventually.of_forall hSsuper) hconv.tendstoLocallyUniformlyOn
      (hvC.continuous.lowerSemicontinuous.lowerSemicontinuousOn _) hF continuousOn_const
  have hv2 : ContDiffOn ℝ 2 v O' := (hvC.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn
  refine ⟨hvC.contDiffOn, fun q hq ↦ ?_⟩
  have h1 := hvsub.heat_le_of_contDiffOn isOpen_ball hv2 q hq
  have h2 := hvsuper.le_heat_of_contDiffOn isOpen_ball hv2 q hq
  simp only [add_zero] at h1 h2
  linarith

/-- Local form of `isSmoothCaloricOn_of_isVisc`: around each `p ∈ O`, `u` is smooth caloric on a
ball. -/
theorem exists_ball_isSmoothCaloricOn_of_isVisc {O : Set (E d × ℝ)} (hO : IsOpen O)
    {u : E d × ℝ → ℝ} (hu : ContinuousOn u O) (hsub : IsViscSubOn O (fun _ _ ↦ 0) u)
    (hsuper : IsViscSuperOn O (fun _ _ ↦ 0) u) {p : E d × ℝ} (hp : p ∈ O) :
    ∃ r > 0, IsSmoothCaloricOn (ball p r) u := by
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hp)
  set r := ρ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hK : closedBall p (3 * r) ⊆ O := by rwa [hr_def, mul_div_cancel₀ _ three_ne_zero]
  set K := closedBall p (3 * r) with hK_def
  have hKc : IsCompact K := isCompact_closedBall p _
  have huK : ContinuousOn u K := hu.mono hK
  -- the mollifiers `φ m` of radius `δ m = r / (m + 2)`
  set δ : ℕ → ℝ := fun m ↦ r / ((m : ℝ) + 2) with hδ_def
  have hδpos : ∀ m, 0 < δ m := fun m ↦ by positivity
  have hδr : ∀ m, δ m ≤ r := fun m ↦
    div_le_self hr.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hδ0 : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
  let φ : ℕ → ContDiffBump (0 : E d × ℝ) := fun m ↦
    ⟨δ m / 2, δ m, half_pos (hδpos m), half_lt_self (hδpos m)⟩
  have hmoll := fun m ↦ IsViscCaloric.mollify_isSmoothCaloricOn hu hsub hsuper hK (φ m) (hδr m)
  refine ⟨r, hr, IsSmoothCaloricOn.of_tendstoLocallyUniformlyOn (l := atTop) isOpen_ball
    (v := fun m ↦ mollifyOn (φ m) K u)
    (fun m ↦ (hmoll m).2.mono_set (ball_subset_ball (by linarith))) ?_⟩
  refine TendstoUniformlyOn.tendstoLocallyUniformlyOn
    (Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_)
  obtain ⟨γ, hγ, hγu⟩ :=
    Metric.uniformContinuousOn_iff.1 (hKc.uniformContinuousOn_of_continuous huK) (ε / 2)
      (half_pos hε)
  filter_upwards [hδ0.eventually (gt_mem_nhds hγ)] with m hm z hz
  rw [dist_comm]
  have hzr : dist z p < r := hz
  have hball : ball z (φ m).rOut ⊆ K := fun x hx ↦ by
    have hx' : dist x z < δ m := hx
    exact mem_closedBall.2 (by linarith [dist_triangle x z p, hδr m])
  refine (dist_mollifyOn_le (φ m) hKc huK hball fun x hx ↦ ?_).trans_lt (half_lt_self hε)
  exact (hγu x (hball hx) z (hball (mem_ball_self (φ m).rOut_pos))
    ((mem_ball.1 hx).trans hm)).le

/-- **Viscosity caloric functions are smooth.** A continuous viscosity solution of the heat
equation `dₜu - lapₓu = 0` (sub- and supersolution, source `0`) on an open `O ⊆ E d × ℝ` is
smooth caloric on `O`: `C^∞` on `O` (`ContDiffOn ℝ ∞`, not analytic) with `dₜu = lapₓu`
pointwise. Valid for all `d`, including `d = 0`. -/
theorem isSmoothCaloricOn_of_isVisc {O : Set (E d × ℝ)} (hO : IsOpen O) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u O) (hsub : IsViscSubOn O (fun _ _ ↦ 0) u)
    (hsuper : IsViscSuperOn O (fun _ _ ↦ 0) u) :
    IsSmoothCaloricOn O u := by
  choose! r hr hloc using fun p (hp : p ∈ O) ↦
    exists_ball_isSmoothCaloricOn_of_isVisc hO hu hsub hsuper hp
  refine ⟨contDiffOn_of_locally_contDiffOn fun p hp ↦
    ⟨ball p (r p), isOpen_ball, mem_ball_self (hr p hp), (hloc p hp).1.mono inter_subset_right⟩,
    fun p hp ↦ (hloc p hp).2 p (mem_ball_self (hr p hp))⟩

end ParabolicBasic
