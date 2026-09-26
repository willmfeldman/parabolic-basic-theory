/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite partition weights

The integral `∫ η(w) u(z - w) dw` of a continuous `u` against a nonnegative integrable weight
`η` supported in `closedBall 0 δ` is approximated, uniformly in the admissible `z`, by a finite
sum `∑ᵢ cᵢ u(z - wᵢ)` with `cᵢ ≥ 0` and `wᵢ ∈ closedBall 0 δ`.

Proof: cover `closedBall 0 δ` by finitely many balls of radius `γ` (a modulus of uniform
continuity of `u` on `K`), disjointify, and take `cᵢ := ∫_{Aᵢ} η` and `wᵢ` the centres.

We also record that the product volume on `E d × ℝ` is an additive Haar measure (Mathlib has the
instance for `μ.prod ν` but it does not fire on `volume` of a product).
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped Function

namespace ParabolicBasic

variable {d : ℕ}

/-- The product volume on space-time is an additive Haar measure. -/
instance instIsAddHaarMeasureVolumeSpaceTime : (volume : Measure (E d × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- **Finite partition weights.** For `u` continuous on a compact
`K` and `η ≥ 0` integrable with support in `closedBall 0 δ`, there are finitely many weights
`c i ≥ 0` (summing to `∫ η`) and nodes `w i ∈ closedBall 0 δ` such that
`|∑ c i * u (z - w i) - ∫ η w * u (z - w) dw| ≤ ε ∫ η` for all `z` with `z - closedBall 0 δ ⊆ K`. -/
theorem exists_finite_weights_approx {K : Set (E d × ℝ)} (hK : IsCompact K) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u K) {η : E d × ℝ → ℝ} (hη0 : ∀ w, 0 ≤ η w) (hηi : Integrable η)
    {δ : ℝ} (hηs : Function.support η ⊆ closedBall 0 δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (w : Fin N → E d × ℝ), (∀ i, 0 ≤ c i) ∧
      (∀ i, w i ∈ closedBall 0 δ) ∧ ∑ i, c i = ∫ w', η w' ∧
      ∀ z, (∀ w' ∈ closedBall (0 : E d × ℝ) δ, z - w' ∈ K) →
        |∑ i, c i * u (z - w i) - ∫ w', η w' * u (z - w')| ≤ ε * ∫ w', η w' := by
  classical
  set B : Set (E d × ℝ) := closedBall 0 δ with hB_def
  have hB : IsCompact B := isCompact_closedBall 0 δ
  have hηB : ∀ w, w ∉ B → η w = 0 := fun w hw ↦ Function.notMem_support.1 fun h ↦ hw (hηs h)
  obtain ⟨γ, hγ, hγu⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hu) ε hε
  obtain ⟨t, htB, htf, hcov⟩ := finite_cover_balls_of_compact hB hγ
  set N := htf.toFinset.card
  let e : htf.toFinset ≃ Fin N := htf.toFinset.equivFin
  let y : Fin N → E d × ℝ := fun i ↦ (e.symm i : E d × ℝ)
  have hyt : ∀ i, y i ∈ t := fun i ↦ htf.mem_toFinset.1 (e.symm i).2
  have hcov' : B ⊆ ⋃ i, ball (y i) γ := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 (hcov hw)
    refine mem_iUnion.2 ⟨e ⟨x, htf.mem_toFinset.2 hx⟩, ?_⟩
    simpa [y] using hwx
  let A : Fin N → Set (E d × ℝ) := fun i ↦ B ∩ disjointed (fun j ↦ ball (y j) γ) i
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    refine measurableSet_closedBall.inter ?_
    rw [disjointed_eq_inter_compl]
    exact measurableSet_ball.inter
      (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ measurableSet_ball.compl)
  have hAd : Pairwise (Disjoint on A) := fun i j hij ↦
    (disjoint_disjointed _ hij).mono inter_subset_right inter_subset_right
  have hAU : ⋃ i, A i = B := by
    simp only [A]
    rw [← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.2 hcov'
  have hAy : ∀ i, ∀ w ∈ A i, dist w (y i) < γ := fun i w hw ↦ disjointed_subset _ i hw.2
  -- the total mass splits over the cells
  have hmass : ∑ i, ∫ w in A i, η w = ∫ w', η w' := by
    rw [← integral_iUnion_fintype hAm hAd (fun i ↦ hηi.integrableOn), hAU]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hηB
  refine ⟨N, fun i ↦ ∫ w in A i, η w, y, fun i ↦ setIntegral_nonneg (hAm i) fun w _ ↦ hη0 w,
    fun i ↦ htB (hyt i), hmass, fun z hz ↦ ?_⟩
  have hcont : ContinuousOn (fun w ↦ u (z - w)) B :=
    hu.comp (continuousOn_const.sub continuousOn_id) fun w hw ↦ hz w hw
  have hfB : IntegrableOn (fun w ↦ η w * u (z - w)) B :=
    hηi.integrableOn.mul_continuousOn hcont hB
  have hsplit : ∫ w', η w' * u (z - w') = ∑ i, ∫ w in A i, η w * u (z - w) := by
    rw [← integral_iUnion_fintype hAm hAd (fun i ↦ hfB.mono_set (hAU ▸ subset_iUnion A i)), hAU]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by simp [hηB w hw]).symm
  have hcell : ∀ i, |(∫ w in A i, η w) * u (z - y i) - ∫ w in A i, η w * u (z - w)| ≤
      ε * ∫ w in A i, η w := by
    intro i
    have hfi : IntegrableOn (fun w ↦ η w * u (z - w)) (A i) :=
      hfB.mono_set (hAU ▸ subset_iUnion A i)
    rw [← integral_mul_const, ← integral_sub (hηi.integrableOn.mul_const _) hfi,
      ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hηi.integrableOn.const_mul ε) ?_
    refine (ae_restrict_iff' (hAm i)).2 (Eventually.of_forall fun w hw ↦ ?_)
    have hwB : w ∈ B := hw.1
    have hlt : dist (u (z - y i)) (u (z - w)) < ε := by
      refine hγu _ (hz _ (htB (hyt i))) _ (hz _ hwB) ?_
      rw [dist_sub_left, dist_comm]
      exact hAy i w hw
    rw [Real.dist_eq] at hlt
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hη0 w), mul_comm ε]
    exact mul_le_mul_of_nonneg_left hlt.le (hη0 w)
  rw [hsplit, ← Finset.sum_sub_distrib, ← hmass, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hcell i)

end ParabolicBasic
