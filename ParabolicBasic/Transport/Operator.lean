/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Transport.Calculus
public import ViscositySolns.Operators.Linear
public import ViscositySolns.Operators.Trace
public import ViscositySolns.Operators.Examples
public import ViscositySolns.Operators.Proper
public import ViscositySolns.Operators.Comparison
public import ViscositySolns.Comparison.OperatorCondition.IshiiCondition
public import ViscositySolns.Comparison.ProperComparison.Setup
public import ViscositySolns.TestFunctions.Smooth

/-!
# The heat operator on `Point (d + 1)` and its operator conditions

With `A = diag(1, …, 1, 0)` (`heatDiag`) and `β = e_last` (`timeVec`):

* `heatTraceOp d := traceSecondOrderOperator A β 0 0`, i.e. `-tr(A X) + q_last`;
* `parabolicOp F := heatTraceOp d + zeroOrderOperator ((z, r) ↦ F (e⁻¹ z) r)`, the operator
  `dₜ − lapₓ + F` on `Point (d + 1)`;
* `heatOp S := traceSecondOrderOperator A β 0 (S ∘ e⁻¹)`, the operator `dₜ − lapₓ − S`
  (`heatOp_eq_parabolicOp`).

Explicitly `parabolicOp F z r q X = -(∑ i : Fin d, X i.castSucc i.castSucc) + q (Fin.last d)
+ F (e⁻¹ z) r` (`parabolicOp_apply`). The file records the `ViscositySolns` operator hypotheses
(`Proper`, `OperatorContinuous`, `HessianSymmetricInvariant`, continuity in the Hessian,
`IshiiOperatorComparisonConditionOn`, `UniformScalarDecreaseOn`), and two helpers: a monotone
comparison modulus from compactness and a Tietze wrapper.

Moduli are stated in the `E d × ℝ` distance; the norm constant of `e⁻¹` (sup norm on `Point`) is
absorbed inside `parabolicOp_ishiiCondition`.
-/

@[expose] public section

open Set Filter Topology
open scoped MatrixOrder

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Definitions -/

/-- The diagonal of the second-order coefficient `diag(1, …, 1, 0)` (no second derivative in
time). -/
noncomputable def heatDiag (d : ℕ) : Fin (d + 1) → ℝ := fun i ↦ if i = Fin.last d then 0 else 1

/-- The time direction `e_last`. -/
noncomputable def timeVec (d : ℕ) : ViscositySolns.Point (d + 1) :=
  ViscositySolns.coordinateVector (Fin.last d)

/-- The heat operator `-tr(diag(1,…,1,0) X) + q_last` as a `ViscositySolns` trace operator. -/
noncomputable def heatTraceOp (d : ℕ) : ViscositySolns.Operator (d + 1) :=
  ViscositySolns.traceSecondOrderOperator (fun _ ↦ Matrix.diagonal (heatDiag d))
    (fun _ ↦ timeVec d) (fun _ ↦ 0) (fun _ ↦ 0)

/-- The operator `dₜ − lapₓ + F` on `Point (d+1)`. -/
noncomputable def parabolicOp (F : E d × ℝ → ℝ → ℝ) : ViscositySolns.Operator (d + 1) :=
  ViscositySolns.addOperator (heatTraceOp d)
    (ViscositySolns.zeroOrderOperator fun z r ↦ F ((spaceTimeEquiv d).symm z) r)

/-- The linear operator `dₜ − lapₓ − S`. -/
noncomputable def heatOp (S : E d × ℝ → ℝ) : ViscositySolns.Operator (d + 1) :=
  ViscositySolns.traceSecondOrderOperator (fun _ ↦ Matrix.diagonal (heatDiag d))
    (fun _ ↦ timeVec d) (fun _ ↦ 0) (S ∘ (spaceTimeEquiv d).symm)

/-! ### Explicit form -/

@[simp]
theorem heatDiag_castSucc (i : Fin d) : heatDiag d i.castSucc = 1 := by
  simp [heatDiag, Fin.castSucc_ne_last]

@[simp]
theorem heatDiag_last : heatDiag d (Fin.last d) = 0 := by
  simp [heatDiag]

theorem heatDiag_nonneg (i : Fin (d + 1)) : 0 ≤ heatDiag d i := by
  unfold heatDiag; split_ifs <;> norm_num

/-- `tr(diag(1,…,1,0) X)` is the sum of the first `d` diagonal entries. -/
theorem trace_heatDiag_mul (X : ViscositySolns.Hessian (d + 1)) :
    Matrix.trace (Matrix.diagonal (heatDiag d) * X) = ∑ i : Fin d, X i.castSucc i.castSucc := by
  simp [Matrix.trace, Matrix.diagonal_mul, Fin.sum_univ_castSucc]

@[simp]
theorem dotProduct_timeVec (q : ViscositySolns.Point (d + 1)) :
    timeVec d ⬝ᵥ q = q (Fin.last d) := by
  simp [timeVec, coordinateVector_eq_single]

/-- Trace monotonicity on the first `d` indices: the Loewner order `X ≤ Y` gives
`∑ᵢ Xᵢᵢ ≤ ∑ᵢ Yᵢᵢ` over the space indices. -/
theorem sum_castSucc_diag_le_of_le {X Y : ViscositySolns.Hessian (d + 1)} (h : X ≤ Y) :
    ∑ i : Fin d, X i.castSucc i.castSucc ≤ ∑ i : Fin d, Y i.castSucc i.castSucc := by
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have := (Matrix.le_iff.1 h).diag_nonneg (i := i.castSucc)
  simp only [Matrix.sub_apply] at this
  linarith

/-- **Explicit form.** -/
@[simp]
theorem parabolicOp_apply (F : E d × ℝ → ℝ → ℝ) (z : ViscositySolns.Point (d + 1)) (r : ℝ)
    (q : ViscositySolns.Point (d + 1)) (X : ViscositySolns.Hessian (d + 1)) :
    parabolicOp F z r q X = -(∑ i : Fin d, X i.castSucc i.castSucc) + q (Fin.last d)
      + F ((spaceTimeEquiv d).symm z) r := by
  simp [parabolicOp, heatTraceOp, ViscositySolns.addOperator, trace_heatDiag_mul]

@[simp]
theorem heatOp_apply (S : E d × ℝ → ℝ) (z : ViscositySolns.Point (d + 1)) (r : ℝ)
    (q : ViscositySolns.Point (d + 1)) (X : ViscositySolns.Hessian (d + 1)) :
    heatOp S z r q X = -(∑ i : Fin d, X i.castSucc i.castSucc) + q (Fin.last d)
      - S ((spaceTimeEquiv d).symm z) := by
  simp [heatOp, trace_heatDiag_mul]

theorem heatOp_eq_parabolicOp (S : E d × ℝ → ℝ) : heatOp S = parabolicOp (fun p _ ↦ -S p) := by
  funext z r q X
  simp only [heatOp_apply, parabolicOp_apply]
  ring

/-- `d = 0`: `parabolicOp F z r q X = q 0 + F (e⁻¹ z) r`. -/
example (F : E 0 × ℝ → ℝ → ℝ) (z : ViscositySolns.Point 1) (r : ℝ) (q : ViscositySolns.Point 1)
    (X : ViscositySolns.Hessian 1) :
    parabolicOp F z r q X = q 0 + F ((spaceTimeEquiv 0).symm z) r := by
  simp

/-- **Smooth jets**: on the Fréchet jet of `ψ♯ = ψ ∘ e⁻¹` at `e p`,
`parabolicOp F` evaluates to `dₜ ψ p − lapₓ ψ p + F p r`. -/
theorem parabolicOp_smoothJet (F : E d × ℝ → ℝ → ℝ) {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (p : E d × ℝ) (r : ℝ) :
    parabolicOp F (spaceTimeEquiv d p) r
        (ViscositySolns.linearMapGradient (fderiv ℝ (toPointFun ψ) (spaceTimeEquiv d p)))
        (ViscositySolns.bilinearMapHessian
          (fderiv ℝ (fderiv ℝ (toPointFun ψ)) (spaceTimeEquiv d p)))
      = dₜ ψ p - lapₓ ψ p + F p r := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  rw [parabolicOp_apply, dₜ_eq_fderiv_toPointFun hψ1, lapₓ_eq_sum_fderiv_fderiv_toPointFun hψ,
    ContinuousLinearEquiv.symm_apply_apply]
  simp only [ViscositySolns.linearMapGradient_apply, ViscositySolns.bilinearMapHessian_apply]
  ring

/-! ### Operator conditions for `parabolicOp` -/

/-- **Proper.** -/
theorem parabolicOp_proper {F : E d × ℝ → ℝ → ℝ} (hF : ∀ p, Monotone (F p)) :
    ViscositySolns.Proper (parabolicOp F) := by
  refine ViscositySolns.Proper.add ?_ ?_
  · exact ViscositySolns.proper_traceSecondOrderOperator_diagonal (a := fun _ ↦ heatDiag d)
      (fun _ i ↦ heatDiag_nonneg i) (fun _ ↦ le_rfl)
  · exact ViscositySolns.proper_zeroOrderOperator fun z ↦ hF _

/-- **Continuity.** Global, as `ViscositySolns` requires. -/
theorem parabolicOp_operatorContinuous {F : E d × ℝ → ℝ → ℝ}
    (hF : Continuous fun q : (E d × ℝ) × ℝ ↦ F q.1 q.2) :
    ViscositySolns.OperatorContinuous (parabolicOp F) := by
  unfold ViscositySolns.OperatorContinuous ViscositySolns.operatorGraphEval
  simp only [parabolicOp_apply]
  have hH : ∀ i j : Fin (d + 1), Continuous fun z : (ViscositySolns.Point (d + 1) × ℝ) ×
      ViscositySolns.Jet (d + 1) ↦ z.2.hessian i j := fun i j ↦
    ((continuous_apply j).comp (continuous_apply i)).comp
      (ViscositySolns.Jet.continuous_hessian.comp continuous_snd)
  have hG : Continuous fun z : (ViscositySolns.Point (d + 1) × ℝ) ×
      ViscositySolns.Jet (d + 1) ↦ z.2.gradient (Fin.last d) :=
    (continuous_apply _).comp (ViscositySolns.Jet.continuous_gradient.comp continuous_snd)
  have hFz : Continuous fun z : (ViscositySolns.Point (d + 1) × ℝ) ×
      ViscositySolns.Jet (d + 1) ↦ F ((spaceTimeEquiv d).symm z.1.1) z.1.2 :=
    hF.comp (((spaceTimeEquiv d).symm.continuous.comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp continuous_fst))
  exact ((continuous_finsetSum _ fun i _ ↦ hH _ _).neg.add hG).add hFz

/-- **Hessian symmetry**: `parabolicOp F` depends only on the symmetric part of the Hessian, for
every `F`. -/
theorem parabolicOp_hessianSymmetricInvariant (F : E d × ℝ → ℝ → ℝ) :
    ViscositySolns.HessianSymmetricInvariant (parabolicOp F) := by
  intro z r q X
  have h : ∀ i : Fin d, (1 / 2 : ℝ) * (X i.castSucc i.castSucc + X i.castSucc i.castSucc) =
      X i.castSucc i.castSucc := fun i ↦ by ring
  simp only [parabolicOp_apply, ViscositySolns.symHessian_apply, h]

/-- **Continuity in the Hessian**, for every `F`. -/
theorem parabolicOp_continuous_hessian (F : E d × ℝ → ℝ → ℝ) (z : ViscositySolns.Point (d + 1))
    (r : ℝ) (q : ViscositySolns.Point (d + 1)) :
    Continuous fun X : ViscositySolns.Hessian (d + 1) ↦ parabolicOp F z r q X := by
  simp only [parabolicOp_apply]
  exact ((continuous_finsetSum _ fun i _ ↦
    (continuous_apply i.castSucc).comp (continuous_apply i.castSucc)).neg.add
      continuous_const).add continuous_const

/-- **Structure condition** (CIL (3.14)). The modulus hypothesis is in
the `E d × ℝ` distance. -/
theorem parabolicOp_ishiiCondition {F : E d × ℝ → ℝ → ℝ} {Ω : Set (E d × ℝ)} {R : Set ℝ}
    {ω : ℝ → ℝ} (hω : ViscositySolns.ComparisonModulus ω) (hmono : Monotone ω)
    (hF : ∀ p ∈ Ω, ∀ q ∈ Ω, ∀ r ∈ R, F q r - F p r ≤ ω (dist p q)) :
    ViscositySolns.IshiiOperatorComparisonConditionOn (toPointSet Ω) R (parabolicOp F) := by
  set C : ℝ := max ‖((spaceTimeEquiv d).symm : ViscositySolns.Point (d + 1) →L[ℝ] E d × ℝ)‖ 1
    with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hω' : ViscositySolns.ComparisonModulus fun s ↦ ω (C * s) := by
    refine ⟨fun t ht ↦ hω.1 _ (mul_nonneg hCpos.le ht), hω.2.comp ?_⟩
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ ↦ C * s) (𝓝 0) (𝓝 (C * 0)) := tendsto_id.const_mul C
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs using mul_pos hCpos hs
  have hmono' : Monotone fun s ↦ ω (C * s) := fun a b hab ↦
    hmono (mul_le_mul_of_nonneg_left hab hCpos.le)
  refine ViscositySolns.IshiiOperatorComparisonConditionOn.addOperator ?_ ?_
  · exact ViscositySolns.ishiiOperatorComparisonConditionOn_const_traceSecondOrderOperator _ _
      (Matrix.posSemidef_diagonal_iff.2 fun i ↦ heatDiag_nonneg i)
  · refine ViscositySolns.ishiiOperatorComparisonConditionOn_zeroOrderOperator_of_norm_bound
      hω' hmono' ?_
    intro x hx y hy r hr
    refine (hF _ hx _ hy r hr).trans (hmono ?_)
    rw [dist_eq_norm, ← map_sub]
    calc ‖(spaceTimeEquiv d).symm (x - y)‖
        ≤ ‖((spaceTimeEquiv d).symm : ViscositySolns.Point (d + 1) →L[ℝ] E d × ℝ)‖ * ‖x - y‖ :=
          ((spaceTimeEquiv d).symm : ViscositySolns.Point (d + 1) →L[ℝ] E d × ℝ).le_opNorm _
      _ ≤ C * ‖x - y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **Scalar decrease.** -/
theorem parabolicOp_uniformScalarDecreaseOn {F : E d × ℝ → ℝ → ℝ} {Ω : Set (E d × ℝ)}
    {δ ε : ℝ} (hF : ∀ p ∈ Ω, ∀ r, F p (r - δ) ≤ F p r - ε) :
    ViscositySolns.UniformScalarDecreaseOn (toPointSet Ω) (parabolicOp F) δ ε := by
  intro z hz r q X
  simp only [parabolicOp_apply]
  linarith [hF _ hz r]

/-! ### Operator conditions for `heatOp` -/

theorem heatOp_proper (S : E d × ℝ → ℝ) : ViscositySolns.Proper (heatOp S) := by
  rw [heatOp_eq_parabolicOp]
  exact parabolicOp_proper fun _ ↦ monotone_const

theorem heatOp_operatorContinuous {S : E d × ℝ → ℝ} (hS : Continuous S) :
    ViscositySolns.OperatorContinuous (heatOp S) := by
  rw [heatOp_eq_parabolicOp]
  exact parabolicOp_operatorContinuous (hS.comp continuous_fst).neg

theorem heatOp_hessianSymmetricInvariant (S : E d × ℝ → ℝ) :
    ViscositySolns.HessianSymmetricInvariant (heatOp S) := by
  rw [heatOp_eq_parabolicOp]
  exact parabolicOp_hessianSymmetricInvariant _

theorem heatOp_continuous_hessian (S : E d × ℝ → ℝ) (z : ViscositySolns.Point (d + 1))
    (r : ℝ) (q : ViscositySolns.Point (d + 1)) :
    Continuous fun X : ViscositySolns.Hessian (d + 1) ↦ heatOp S z r q X := by
  rw [heatOp_eq_parabolicOp]
  exact parabolicOp_continuous_hessian _ z r q

theorem heatOp_ishiiCondition {S : E d × ℝ → ℝ} {Ω : Set (E d × ℝ)} {R : Set ℝ}
    {ω : ℝ → ℝ} (hω : ViscositySolns.ComparisonModulus ω) (hmono : Monotone ω)
    (hS : ∀ p ∈ Ω, ∀ q ∈ Ω, S p - S q ≤ ω (dist p q)) :
    ViscositySolns.IshiiOperatorComparisonConditionOn (toPointSet Ω) R (heatOp S) := by
  rw [heatOp_eq_parabolicOp]
  exact parabolicOp_ishiiCondition hω hmono fun p hp q hq r _ ↦ by linarith [hS p hp q hq]

/-! ### Helpers: modulus from compactness, Tietze -/

/-- **Comparison modulus from compactness.** -/
theorem exists_comparisonModulus_of_isCompact {K : Set (E d × ℝ)} {J : Set ℝ} (hK : IsCompact K)
    (hJ : IsCompact J) {g : E d × ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun q : (E d × ℝ) × ℝ ↦ g q.1 q.2) (K ×ˢ J)) :
    ∃ ω : ℝ → ℝ, ViscositySolns.ComparisonModulus ω ∧ Monotone ω ∧
      ∀ p ∈ K, ∀ q ∈ K, ∀ m ∈ J, |g q m - g p m| ≤ ω (dist p q) := by
  obtain ⟨B, hB⟩ := (hK.prod hJ).exists_bound_of_continuousOn hg
  set T : ℝ → Set ℝ := fun s ↦
    {x | ∃ p ∈ K, ∃ q ∈ K, ∃ m ∈ J, dist p q ≤ s ∧ x = |g q m - g p m|} with hT
  have hbdd : ∀ s, BddAbove (T s) := by
    intro s
    refine ⟨2 * B, ?_⟩
    rintro x ⟨p, hp, q, hq, m, hm, -, rfl⟩
    have h1 := hB (q, m) ⟨hq, hm⟩
    have h2 := hB (p, m) ⟨hp, hm⟩
    simp only [Real.norm_eq_abs] at h1 h2
    calc |g q m - g p m| ≤ |g q m| + |g p m| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hnn : ∀ s, ∀ x ∈ T s, 0 ≤ x := by
    rintro s x ⟨p, -, q, -, m, -, -, rfl⟩
    exact abs_nonneg _
  refine ⟨fun s ↦ sSup (T s), ⟨fun t _ ↦ Real.sSup_nonneg (hnn t), ?_⟩, ?_, ?_⟩
  · have huc := (hK.prod hJ).uniformContinuousOn_of_continuous hg
    rw [Metric.uniformContinuousOn_iff] at huc
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun s hs hsd ↦ ?_⟩
    have hs0 : (0 : ℝ) < s := hs
    have hs' : s < δ := by rwa [Real.dist_eq, sub_zero, abs_of_pos hs0] at hsd
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sSup_nonneg (hnn s))]
    refine lt_of_le_of_lt (Real.sSup_le ?_ (half_pos hε).le) (half_lt_self hε)
    rintro x ⟨p, hp, q, hq, m, hm, hpq, rfl⟩
    have := hδ' (p, m) ⟨hp, hm⟩ (q, m) ⟨hq, hm⟩ (by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact lt_of_le_of_lt hpq hs')
    simp only [Real.dist_eq] at this
    rw [abs_sub_comm] at this
    exact this.le
  · intro a b hab
    rcases (T a).eq_empty_or_nonempty with h | h
    · simp only [h, Real.sSup_empty]
      exact Real.sSup_nonneg (hnn b)
    · exact csSup_le_csSup (hbdd b) h fun x ⟨p, hp, q, hq, m, hm, hpq, hx⟩ ↦
        ⟨p, hp, q, hq, m, hm, hpq.trans hab, hx⟩
  · intro p hp q hq m hm
    exact le_csSup (hbdd _) ⟨p, hp, q, hq, m, hm, le_rfl, rfl⟩

/-- **Tietze wrapper.** -/
theorem exists_continuous_eqOn_of_continuousOn {A : Set (E d × ℝ)} (hA : IsClosed A)
    {S : E d × ℝ → ℝ} (hS : ContinuousOn S A) :
    ∃ S' : E d × ℝ → ℝ, Continuous S' ∧ EqOn S' S A := by
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hA ⟨A.domRestrict S, hS.domRestrict⟩
  refine ⟨G, G.continuous, fun x hx ↦ ?_⟩
  exact congrArg (fun f : C(A, ℝ) ↦ f ⟨x, hx⟩) hG

end ParabolicBasic
