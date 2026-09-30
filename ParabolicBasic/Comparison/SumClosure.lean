/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Transport.Viscosity
public import ParabolicBasic.Transport.Quartic
public import ParabolicBasic.Viscosity.Invariance
public import ParabolicBasic.Classical.ToViscosity
public import ViscositySolns.Comparison.CILMaximumPrinciple
public import ViscositySolns.Comparison.IshiiLemma
public import ViscositySolns.Comparison.MatrixInequalities.QuadraticModel
public import ViscositySolns.Analysis.SemiconvexJensen.ExternalAleksandrov
public import ViscositySolns.Semijets.Closure
public import ViscositySolns.TestFunctions.Characterization

/-!
# Sum-closure of viscosity subsolutions of the heat equation

If `dₜuᵢ − lapₓuᵢ ≤ Sᵢ` in the viscosity sense on an open set `O` with `Sᵢ`
continuous on `O`, then `dₜ(u₁ + u₂) − lapₓ(u₁ + u₂) ≤ S₁ + S₂` in the viscosity sense on `O`
(`IsViscSubOn.add_source`). The proof is direct: strictify the test with the quartic
`spaceTimeQuartic`, double the variables for `u₁` and `ψ̃ − u₂` on a closed ball, apply the
Crandall–Ishii lemma of `ViscositySolns`
(`QuadraticPenaltyIshiiLemmaOn.of_aleksandrov`, Aleksandrov parameter discharged by
`proof_external`), shift the closed subjet of `ψ̃ − u₂` by the jet of `ψ̃`, add the two closed-jet
inequalities (the Ishii relation gives `X ≤ Y`), and let the penalty parameter tend to `∞`.

Corollaries: finite sums (`IsViscSubOn.finset_sum_source`) and nonnegative combinations of
translates of a caloric subsolution (`IsViscSubOn.sum_smul_translate`), with supersolution mirrors.

References: Crandall–Ishii–Lions, *User's guide*, Bull. AMS 27 (1992), Thm 3.2 and §3; Ishii,
CPAM 42 (1989).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff MatrixOrder

namespace ParabolicBasic

/-! ### Doubling of variables -/

section Doubling

variable {n : ℕ}

private theorem dotProduct_self_nonneg' (v : ViscositySolns.Point n) : 0 ≤ v ⬝ᵥ v :=
  Fintype.sum_nonneg fun _ ↦ mul_self_nonneg _

/-- **Doubling of variables.** If `U − V` has a strict maximum at `z₀` on the compact `K` and
`(x k, y k) ∈ K × K` does at least as well as `(z₀, z₀)` for the doubled objective with
penalty parameters `α k → ∞`, then `x k → z₀` and `y k → z₀`. -/
private theorem doubling_maximizers_tendsto {K : Set (ViscositySolns.Point n)} (hK : IsCompact K)
    {U V : ViscositySolns.Point n → ℝ} (hU : UpperSemicontinuousOn U K)
    (hV : LowerSemicontinuousOn V K) {z₀ : ViscositySolns.Point n} (hz₀ : z₀ ∈ K)
    (hstrict : ∀ z ∈ K, z ≠ z₀ → U z - V z < U z₀ - V z₀)
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop) (hαpos : ∀ k, 0 < α k)
    {x y : ℕ → ViscositySolns.Point n} (hx : ∀ k, x k ∈ K) (hy : ∀ k, y k ∈ K)
    (hmax : ∀ k, U z₀ - V z₀ ≤
      U (x k) - V (y k) - ViscositySolns.quadraticPenalty (α k) (x k) (y k)) :
    Tendsto x atTop (𝓝 z₀) ∧ Tendsto y atTop (𝓝 z₀) := by
  set m₀ := U z₀ - V z₀ with hm₀
  obtain ⟨xM, hxM, hUmax⟩ := hU.exists_isMaxOn ⟨z₀, hz₀⟩ hK
  obtain ⟨xm, hxm, hVmin⟩ := hV.exists_isMinOn ⟨z₀, hz₀⟩ hK
  set B := U xM - V xm - m₀
  set D : ℕ → ℝ := fun k ↦ (x k - y k) ⬝ᵥ (x k - y k) with hD
  have hDle : ∀ k, D k ≤ 2 * B / α k := by
    intro k
    rw [le_div_iff₀ (hαpos k)]
    have h1 := hmax k
    have h2 : U (x k) ≤ U xM := isMaxOn_iff.1 hUmax _ (hx k)
    have h3 : V xm ≤ V (y k) := isMinOn_iff.1 hVmin _ (hy k)
    simp only [ViscositySolns.quadraticPenalty_apply] at h1
    change (x k - y k) ⬝ᵥ (x k - y k) * α k ≤ 2 * B
    nlinarith
  have hD0 : Tendsto D atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ dotProduct_self_nonneg' _) hDle
      (Tendsto.div_atTop tendsto_const_nhds hα)
  have hpair : Tendsto (fun k ↦ (x k, y k)) atTop (𝓝 (z₀, z₀)) := by
    refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    obtain ⟨⟨a, b⟩, hab, φ, hφ, hlim⟩ := (hK.prod hK).tendsto_subseq
      (x := fun k ↦ (x (ns k), y (ns k))) fun k ↦ ⟨hx _, hy _⟩
    refine ⟨φ, ?_⟩
    have hnsφ : Tendsto (fun k ↦ ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
    have hxl : Tendsto (fun k ↦ x (ns (φ k))) atTop (𝓝 a) := (continuous_fst.tendsto _).comp hlim
    have hyl : Tendsto (fun k ↦ y (ns (φ k))) atTop (𝓝 b) := (continuous_snd.tendsto _).comp hlim
    -- `a = b`
    have hab' : a = b := by
      have h1 : Tendsto (fun k ↦ D (ns (φ k))) atTop (𝓝 ((a - b) ⬝ᵥ (a - b))) :=
        ((continuous_id.dotProduct continuous_id).tendsto _).comp (hxl.sub hyl)
      have h2 : Tendsto (fun k ↦ D (ns (φ k))) atTop (𝓝 0) := hD0.comp hnsφ
      have := tendsto_nhds_unique h1 h2
      exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 this)
    subst hab'
    -- `a = z₀`
    have haz : a = z₀ := by
      by_contra haz
      have hlt := hstrict a hab.1 haz
      set δ := m₀ - (U a - V a) with hδ
      have hδpos : 0 < δ := by linarith
      have hxw : Tendsto (fun k ↦ x (ns (φ k))) atTop (𝓝[K] a) :=
        tendsto_nhdsWithin_iff.2 ⟨hxl, Eventually.of_forall fun _ ↦ hx _⟩
      have hyw : Tendsto (fun k ↦ y (ns (φ k))) atTop (𝓝[K] a) :=
        tendsto_nhdsWithin_iff.2 ⟨hyl, Eventually.of_forall fun _ ↦ hy _⟩
      have hU' := hxw.eventually (hU a hab.1 (U a + δ / 2) (by linarith))
      have hV' := hyw.eventually (hV a hab.1 (V a - δ / 2) (by linarith))
      obtain ⟨k, hk1, hk2⟩ := (hU'.and hV').exists
      have h1 := hmax (ns (φ k))
      have h2 : 0 ≤ ViscositySolns.quadraticPenalty (α (ns (φ k))) (x (ns (φ k)))
          (y (ns (φ k))) := by
        rw [ViscositySolns.quadraticPenalty_apply]
        exact mul_nonneg (div_nonneg (hαpos _).le zero_le_two) (dotProduct_self_nonneg' _)
      linarith
    subst haz
    exact hlim
  exact ⟨(continuous_fst.tendsto _).comp hpair, (continuous_snd.tendsto _).comp hpair⟩

end Doubling

variable {d : ℕ}

/-! ### Sum-closure -/

/-- The canonical Fréchet jet of a function on `Point n`. -/
private noncomputable def fderivJet {n : ℕ} (φ : ViscositySolns.Point n → ℝ)
    (z : ViscositySolns.Point n) : ViscositySolns.Jet n :=
  ViscositySolns.Jet.ofDerivatives (fderiv ℝ φ z) (fderiv ℝ (fderiv ℝ φ) z)

private theorem continuous_fderivJet {n : ℕ} {φ : ViscositySolns.Point n → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (fderivJet φ) := by
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  refine continuous_induced_rng.mpr ?_
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun i ↦ hD.clm_apply continuous_const
  · exact continuous_pi fun i ↦ continuous_pi fun j ↦
      (hD2.clm_apply continuous_const).clm_apply continuous_const

/-- **Sum-closure.** Sum of viscosity subsolutions of the heat equation with continuous
sources: if `dₜuᵢ − lapₓuᵢ ≤ Sᵢ` in the viscosity sense on the open set `O`, then
`dₜ(u₁ + u₂) − lapₓ(u₁ + u₂) ≤ S₁ + S₂` in the viscosity sense on `O`. -/
theorem IsViscSubOn.add_source {O : Set (E d × ℝ)} (hO : IsOpen O)
    {S₁ S₂ : E d × ℝ → ℝ} (hS₁ : ContinuousOn S₁ O) (hS₂ : ContinuousOn S₂ O)
    {u₁ u₂ : E d × ℝ → ℝ}
    (hu₁ : IsViscSubOn O (fun p _ ↦ -S₁ p) u₁) (hu₂ : IsViscSubOn O (fun p _ ↦ -S₂ p) u₂) :
    IsViscSubOn O (fun p _ ↦ -(S₁ p + S₂ p)) (u₁ + u₂) := by
  refine ⟨hu₁.1.add hu₂.1, fun ψ hψ z₀ hz₀ ht ↦ ?_⟩
  simp only
  -- Step 1: localize and strictify.
  have hev := ht.2.2
  rw [hO.nhdsWithin_eq hz₀] at hev
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hev (hO.mem_nhds hz₀))
  set ρ := ε / 2 with hρdef
  have hρ : 0 < ρ := half_pos hε
  set Kₛ := Metric.closedBall z₀ ρ with hKₛ
  set Bₛ := Metric.ball z₀ ρ with hBₛ
  have hKε : Kₛ ⊆ Metric.ball z₀ ε := Metric.closedBall_subset_ball (half_lt_self hε)
  have hKO : Kₛ ⊆ O := fun z hz ↦ (hεsub (hKε hz)).2
  have hKle : ∀ z ∈ Kₛ, u₁ z + u₂ z ≤ ψ z := fun z hz ↦ (hεsub (hKε hz)).1
  have hBK : Bₛ ⊆ Kₛ := Metric.ball_subset_closedBall
  have hz₀K : z₀ ∈ Kₛ := Metric.mem_closedBall_self hρ.le
  have hz₀B : z₀ ∈ Bₛ := Metric.mem_ball_self hρ
  obtain ⟨S₁', hS₁'c, hS₁'eq⟩ :=
    exists_continuous_eqOn_of_continuousOn Metric.isClosed_closedBall (hS₁.mono hKO)
  obtain ⟨S₂', hS₂'c, hS₂'eq⟩ :=
    exists_continuous_eqOn_of_continuousOn Metric.isClosed_closedBall (hS₂.mono hKO)
  have hv₁ : IsViscSubOn Bₛ (fun p _ ↦ -S₁' p) u₁ :=
    (hu₁.mono_set Metric.isOpen_ball (hBK.trans hKO)).mono_source fun p hp _ ↦ by
      rw [hS₁'eq (hBK hp)]
  have hv₂ : IsViscSubOn Bₛ (fun p _ ↦ -S₂' p) u₂ :=
    (hu₂.mono_set Metric.isOpen_ball (hBK.trans hKO)).mono_source fun p hp _ ↦ by
      rw [hS₂'eq (hBK hp)]
  set ψ' : E d × ℝ → ℝ := fun q ↦ ψ q + spaceTimeQuartic z₀ q with hψ'def
  have hQ : ContDiff ℝ 2 (spaceTimeQuartic z₀) :=
    (contDiff_spaceTimeQuartic z₀).of_le (WithTop.coe_le_coe.2 le_top)
  have hψ' : ContDiff ℝ 2 ψ' := hψ.add hQ
  have hdₜ : dₜ ψ' z₀ = dₜ ψ z₀ := by
    rw [hψ'def, dₜ_add (hψ.differentiable (by norm_num)) (hQ.differentiable (by norm_num)),
      dₜ_spaceTimeQuartic_self, add_zero]
  have hlapₓ : lapₓ ψ' z₀ = lapₓ ψ z₀ := by
    rw [hψ'def, lapₓ_add hψ hQ, lapₓ_spaceTimeQuartic_self, add_zero]
  have hψz₀ : ψ z₀ = u₁ z₀ + u₂ z₀ := ht.2.1
  -- Step 2: transport and double the variables.
  set e := spaceTimeEquiv d with he
  set K := toPointSet Kₛ with hK
  set C := toPointSet Bₛ with hC
  set U : ViscositySolns.Point (d + 1) → ℝ := toPointFun u₁ with hU
  set φ : ViscositySolns.Point (d + 1) → ℝ := toPointFun ψ' with hφ
  set V : ViscositySolns.Point (d + 1) → ℝ := fun z ↦ -toPointFun u₂ z + φ z with hV
  set w₀ := e z₀ with hw₀
  have hKc : IsCompact K := isCompact_toPointSet (isCompact_closedBall z₀ ρ)
  have hCo : IsOpen C := isOpen_toPointSet Metric.isOpen_ball
  have hCK : C ⊆ K := fun z hz ↦ hBK hz
  have hw₀K : w₀ ∈ K := spaceTimeEquiv_mem_toPointSet.2 hz₀K
  have hw₀C : w₀ ∈ C := spaceTimeEquiv_mem_toPointSet.2 hz₀B
  have hφc : ContDiff ℝ 2 φ := contDiff_toPointFun_iff.2 hψ'
  have hUK : UpperSemicontinuousOn U K :=
    upperSemicontinuousOn_toPointFun_iff.2 (hu₁.1.mono hKO)
  have hVK : LowerSemicontinuousOn V K := by
    have h1 : LowerSemicontinuousOn (fun z ↦ -toPointFun u₂ z) K :=
      upperSemicontinuousOn_iff_lowerSemicontinuousOn_neg.1
        (upperSemicontinuousOn_toPointFun_iff.2 (hu₂.1.mono hKO))
    exact h1.add (hφc.continuous.lowerSemicontinuous.lowerSemicontinuousOn K)
  have hUV : ∀ z, U z - V z = u₁ (e.symm z) + u₂ (e.symm z) - ψ' (e.symm z) := by
    intro z; simp only [hU, hV, hφ, toPointFun_apply]; ring
  have hUVw₀ : U w₀ - V w₀ = 0 := by
    rw [hUV, hw₀, ContinuousLinearEquiv.symm_apply_apply, hψ'def]
    simp only [spaceTimeQuartic_self, hψz₀]; ring
  have hstrict : ∀ z ∈ K, z ≠ w₀ → U z - V z < U w₀ - V w₀ := by
    intro z hz hne
    rw [hUVw₀, hUV]
    have hne' : e.symm z ≠ z₀ := fun h ↦ hne (by
      rw [hw₀, ← h, ContinuousLinearEquiv.apply_symm_apply])
    have hpos : 0 < spaceTimeQuartic z₀ (e.symm z) :=
      lt_of_lt_of_le (pow_pos (dist_pos.2 hne') 4) (dist_pow_four_le_spaceTimeQuartic z₀ _)
    have := hKle _ hz
    simp only [hψ'def]
    linarith
  set α : ℕ → ℝ := fun k ↦ (k : ℝ) + 1 with hαdef
  have hαpos : ∀ k, 0 < α k := fun k ↦ by positivity
  have hα : Tendsto α atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hex : ∀ k : ℕ, ∃ q ∈ K ×ˢ K,
      IsMaxOn (fun q ↦ ViscositySolns.doubledObjective U V (α k) q) (K ×ˢ K) q :=
    fun k ↦ ViscositySolns.exists_isMaxOn_doubledObjective_of_isCompact ⟨w₀, hw₀K⟩ ⟨w₀, hw₀K⟩
      hKc hKc hUK hVK
  choose q hqK hqmax using hex
  set x : ℕ → ViscositySolns.Point (d + 1) := fun k ↦ (q k).1 with hx
  set y : ℕ → ViscositySolns.Point (d + 1) := fun k ↦ (q k).2 with hy
  have hmax : ∀ k, U w₀ - V w₀ ≤
      U (x k) - V (y k) - ViscositySolns.quadraticPenalty (α k) (x k) (y k) := by
    intro k
    have := isMaxOn_iff.1 (hqmax k) (w₀, w₀) ⟨hw₀K, hw₀K⟩
    simpa [ViscositySolns.doubledObjective] using this
  obtain ⟨hxt, hyt⟩ := doubling_maximizers_tendsto hKc hUK hVK hw₀K hstrict hα hαpos
    (fun k ↦ (hqK k).1) (fun k ↦ (hqK k).2) hmax
  -- Steps 3–5: Ishii, jet shift, and the approximate inequality.
  set A := fderivJet φ with hA
  set G : ViscositySolns.Point (d + 1) → ℝ := fun z ↦
    (A z).gradient (Fin.last d) - ∑ i : Fin d, (A z).hessian i.castSucc i.castSucc with hG
  have hAc : Continuous A := continuous_fderivJet hφc
  have hGc : Continuous G :=
    ((continuous_apply _).comp (ViscositySolns.Jet.continuous_gradient.comp hAc)).sub
      (continuous_finsetSum _ fun i _ ↦ (continuous_apply _).comp ((continuous_apply _).comp
        (ViscositySolns.Jet.continuous_hessian.comp hAc)))
  have happrox : ∀ k, x k ∈ C → y k ∈ C →
      G (y k) ≤ S₁' (e.symm (x k)) + S₂' (e.symm (y k)) := by
    intro k hxC hyC
    have : LocallyCompactSpace C := locallyCompactSpace_toPointSet Metric.isOpen_ball
    have hloc : ViscositySolns.HasQuadraticPenaltyLocalMaximumOn C C U V (α k) (x k) (y k) :=
      ViscositySolns.hasQuadraticPenaltyLocalMaximumOn_of_isMaxOn_doubledObjective ⟨hxC, hyC⟩
        ((hqmax k).on_subset (prod_mono hCK hCK))
    obtain ⟨J⟩ := ViscositySolns.QuadraticPenaltyIshiiLemmaOn.of_aleksandrov
      (ViscositySolns.AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external _)
      (hUK.mono hCK) (hVK.mono hCK) (α k) (hαpos k) (x k) (y k) hloc
    have hXY : J.X ≤ J.Y := ViscositySolns.IshiiMatrixRelation.left_le_right J.matrix_relation
    have h1 := hv₁.closedSuperjet_le (hS₁'c.comp continuous_fst).neg J.superjet_mem
    have hexp : ∀ z ∈ C, ViscositySolns.HasSecondOrderExpansionWithin C φ z (A z) :=
      fun z hz ↦ ViscositySolns.hasSecondOrderExpansionWithin_of_contDiff_two_isOpen hCo hz hφc
        (ViscositySolns.Jet.toFirstDerivative_ofDerivatives _ _).symm
        (ViscositySolns.Jet.toSecondDerivative_ofDerivatives _ _).symm
    have hshift := ViscositySolns.closedSubjet_sub_of_add_hasSecondOrderExpansionWithin
      (u := fun z ↦ -toPointFun u₂ z) hexp hφc.continuous hAc J.subjet_mem
    have hshift' := ViscositySolns.closedSubjet_neg_iff_closedSuperjet.1 hshift
    have hnn : (fun z ↦ -(-toPointFun u₂ z)) = toPointFun u₂ := by funext z; simp
    rw [hnn] at hshift'
    have h2 := hv₂.closedSuperjet_le (hS₂'c.comp continuous_fst).neg hshift'
    have h3 := sum_castSucc_diag_le_of_le hXY
    simp only [ViscositySolns.Jet.neg_gradient, ViscositySolns.Jet.neg_hessian,
      ViscositySolns.Jet.sub_gradient, ViscositySolns.Jet.sub_hessian, Pi.neg_apply,
      Pi.sub_apply, Matrix.neg_apply, Matrix.sub_apply, Finset.sum_neg_distrib,
      Finset.sum_sub_distrib, ViscositySolns.quadraticPenaltyGradientRight,
      ViscositySolns.quadraticPenaltyGradientLeft, Pi.smul_apply, smul_eq_mul, neg_smul,
      neg_neg] at h1 h2
    rw [← he] at h1 h2
    simp only [hG]
    linarith
  -- Step 6: the limit.
  have hev2 : ∀ᶠ k in atTop, G (y k) ≤ S₁' (e.symm (x k)) + S₂' (e.symm (y k)) := by
    filter_upwards [hxt.eventually (hCo.mem_nhds hw₀C), hyt.eventually (hCo.mem_nhds hw₀C)]
      with k hxk hyk
    exact happrox k hxk hyk
  have hlimL : Tendsto (fun k ↦ G (y k)) atTop (𝓝 (G w₀)) := (hGc.tendsto _).comp hyt
  have hes : Continuous e.symm := e.symm.continuous
  have hlimR : Tendsto (fun k ↦ S₁' (e.symm (x k)) + S₂' (e.symm (y k))) atTop
      (𝓝 (S₁' (e.symm w₀) + S₂' (e.symm w₀))) :=
    (((hS₁'c.comp hes).tendsto _).comp hxt).add (((hS₂'c.comp hes).tendsto _).comp hyt)
  have hfin := le_of_tendsto_of_tendsto hlimL hlimR hev2
  have hGw₀ : G w₀ = dₜ ψ' z₀ - lapₓ ψ' z₀ := by
    have := parabolicOp_smoothJet (fun _ _ ↦ 0) hψ' z₀ 0
    rw [parabolicOp_apply] at this
    simp only [hG, hA, fderivJet, ViscositySolns.Jet.ofDerivatives, hw₀, hφ]
    linarith
  rw [hGw₀, hdₜ, hlapₓ, hw₀, ContinuousLinearEquiv.symm_apply_apply, hS₁'eq hz₀K,
    hS₂'eq hz₀K] at hfin
  linarith

/-- **Sum-closure**, supersolution mirror: if `dₜvᵢ − lapₓvᵢ ≥ Sᵢ` in the viscosity sense
on `O`, then `dₜ(v₁ + v₂) − lapₓ(v₁ + v₂) ≥ S₁ + S₂`. -/
theorem IsViscSuperOn.add_source {O : Set (E d × ℝ)} (hO : IsOpen O)
    {S₁ S₂ : E d × ℝ → ℝ} (hS₁ : ContinuousOn S₁ O) (hS₂ : ContinuousOn S₂ O)
    {v₁ v₂ : E d × ℝ → ℝ}
    (hv₁ : IsViscSuperOn O (fun p _ ↦ -S₁ p) v₁) (hv₂ : IsViscSuperOn O (fun p _ ↦ -S₂ p) v₂) :
    IsViscSuperOn O (fun p _ ↦ -(S₁ p + S₂ p)) (v₁ + v₂) := by
  rw [isViscSuperOn_neg_iff] at hv₁ hv₂ ⊢
  have := IsViscSubOn.add_source (S₁ := fun p ↦ -S₁ p) (S₂ := fun p ↦ -S₂ p) hO hS₁.neg hS₂.neg
    hv₁ hv₂
  convert this using 1
  · funext p z
    ring
  · funext p
    simp only [Pi.neg_apply, Pi.add_apply]
    ring

/-! ### Corollaries -/

/-- The zero function is a viscosity subsolution of the heat equation on an open set. -/
theorem isViscSubOn_zero {O : Set (E d × ℝ)} (hO : IsOpen O) :
    IsViscSubOn O (fun _ _ ↦ 0) (0 : E d × ℝ → ℝ) :=
  isViscSubOn_of_contDiffOn hO contDiffOn_const fun p _ ↦ by
    simp [dₜ, lapₓ]

/-- The zero function is a viscosity supersolution of the heat equation on an open set. -/
theorem isViscSuperOn_zero {O : Set (E d × ℝ)} (hO : IsOpen O) :
    IsViscSuperOn O (fun _ _ ↦ 0) (0 : E d × ℝ → ℝ) :=
  isViscSuperOn_of_contDiffOn hO contDiffOn_const fun p _ ↦ by
    simp [dₜ, lapₓ]

/-- Finite sums of subsolutions with continuous sources. -/
theorem IsViscSubOn.finset_sum_source {ι : Type*} (s : Finset ι) {O : Set (E d × ℝ)}
    (hO : IsOpen O) {S : ι → E d × ℝ → ℝ} (hS : ∀ i ∈ s, ContinuousOn (S i) O)
    {u : ι → E d × ℝ → ℝ} (hu : ∀ i ∈ s, IsViscSubOn O (fun p _ ↦ -S i p) (u i)) :
    IsViscSubOn O (fun p _ ↦ -∑ i ∈ s, S i p) (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, neg_zero]
    exact isViscSubOn_zero hO
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Finset.sum_insert ha]
    refine IsViscSubOn.add_source (S₂ := fun p ↦ ∑ i ∈ s, S i p) hO
      (hS a (Finset.mem_insert_self a s)) ?_ (hu a (Finset.mem_insert_self a s))
      (ih (fun i hi ↦ hS i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))
    exact continuousOn_finsetSum s fun i hi ↦ hS i (Finset.mem_insert_of_mem hi)

/-- Finite sums of supersolutions with continuous sources. -/
theorem IsViscSuperOn.finset_sum_source {ι : Type*} (s : Finset ι) {O : Set (E d × ℝ)}
    (hO : IsOpen O) {S : ι → E d × ℝ → ℝ} (hS : ∀ i ∈ s, ContinuousOn (S i) O)
    {v : ι → E d × ℝ → ℝ} (hv : ∀ i ∈ s, IsViscSuperOn O (fun p _ ↦ -S i p) (v i)) :
    IsViscSuperOn O (fun p _ ↦ -∑ i ∈ s, S i p) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, neg_zero]
    exact isViscSuperOn_zero hO
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Finset.sum_insert ha]
    refine IsViscSuperOn.add_source (S₂ := fun p ↦ ∑ i ∈ s, S i p) hO
      (hS a (Finset.mem_insert_self a s)) ?_ (hv a (Finset.mem_insert_self a s))
      (ih (fun i hi ↦ hS i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hv i (Finset.mem_insert_of_mem hi))
    exact continuousOn_finsetSum s fun i hi ↦ hS i (Finset.mem_insert_of_mem hi)

/-- Translation by `-h` as the parabolic affine map with `r = 1`. -/
private theorem parAffine_neg_one (h q : E d × ℝ) : parAffine (-h.1) (-h.2) 1 q = q - h := by
  ext <;> simp [parAffine] <;> abel

/-- A nonnegative multiple of a translate of a caloric subsolution, on `O'`. -/
private theorem IsViscSubOn.smul_translate {O O' : Set (E d × ℝ)} (hO' : IsOpen O')
    {u : E d × ℝ → ℝ} (hu : IsViscSubOn O (fun _ _ ↦ 0) u) {c : ℝ} (hc : 0 ≤ c)
    (h : E d × ℝ) (hO'O : ∀ z ∈ O', z - h ∈ O) :
    IsViscSubOn O' (fun _ _ ↦ 0) (fun z ↦ c * u (z - h)) := by
  rcases hc.eq_or_lt with hc0 | hcpos
  · subst hc0
    refine IsViscSubOn.of_eqOn (fun z _ ↦ ?_) (isViscSubOn_zero hO')
    simp
  · have ht := hu.comp_parAffine (x₀ := -h.1) (t₀ := -h.2) one_pos
    have hsub : O' ⊆ parAffine (-h.1) (-h.2) 1 ⁻¹' O := fun z hz ↦ by
      simpa [mem_preimage, parAffine_neg_one] using hO'O z hz
    have ht' : IsViscSubOn O' (fun _ _ ↦ 0) (fun z ↦ u (z - h)) := by
      have := (ht.mono_set hO' hsub).mono_source (F' := fun _ _ ↦ 0) fun _ _ _ ↦ by simp
      refine IsViscSubOn.of_eqOn (fun z _ ↦ ?_) this
      simp [parAffine_neg_one]
    exact (ht'.const_smul hcpos).mono_source fun _ _ _ ↦ by simp

/-- Nonnegative combinations of translates of a caloric subsolution: if `u` is a viscosity
subsolution of the heat equation on `O`, `w i ≥ 0`, and `z − h i ∈ O` for all `z ∈ O'` (open),
then `z ↦ ∑ᵢ w i * u (z − h i)` is a viscosity subsolution of the heat equation on `O'`. -/
theorem IsViscSubOn.sum_smul_translate {O : Set (E d × ℝ)} {N : ℕ} (w : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i) (h : Fin N → E d × ℝ) {u : E d × ℝ → ℝ}
    (hu : IsViscSubOn O (fun _ _ ↦ 0) u) {O' : Set (E d × ℝ)} (hO' : IsOpen O')
    (hO'O : ∀ i, ∀ z ∈ O', z - h i ∈ O) :
    IsViscSubOn O' (fun _ _ ↦ 0) (fun z ↦ ∑ i, w i * u (z - h i)) := by
  have := IsViscSubOn.finset_sum_source (S := fun _ _ ↦ 0) Finset.univ hO'
    (fun _ _ ↦ continuousOn_const)
    (u := fun i z ↦ w i * u (z - h i)) fun i _ ↦
      (hu.smul_translate hO' (hw i) (h i) (hO'O i)).mono_source fun _ _ _ ↦ by simp
  refine IsViscSubOn.of_eqOn (fun z _ ↦ ?_) (this.mono_source fun _ _ _ ↦ by simp)
  simp [Finset.sum_apply]

/-- Nonnegative combinations of translates of a caloric supersolution, the supersolution mirror
of `IsViscSubOn.sum_smul_translate`. -/
theorem IsViscSuperOn.sum_smul_translate {O : Set (E d × ℝ)} {N : ℕ} (w : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i) (h : Fin N → E d × ℝ) {v : E d × ℝ → ℝ}
    (hv : IsViscSuperOn O (fun _ _ ↦ 0) v) {O' : Set (E d × ℝ)} (hO' : IsOpen O')
    (hO'O : ∀ i, ∀ z ∈ O', z - h i ∈ O) :
    IsViscSuperOn O' (fun _ _ ↦ 0) (fun z ↦ ∑ i, w i * v (z - h i)) := by
  have hv' : IsViscSubOn O (fun _ _ ↦ 0) (-v) :=
    (isViscSuperOn_neg_iff.1 hv).mono_source fun _ _ _ ↦ by simp
  have := IsViscSubOn.sum_smul_translate w hw h hv' hO' hO'O
  rw [isViscSuperOn_neg_iff]
  refine IsViscSubOn.of_eqOn (fun z _ ↦ ?_) (this.mono_source fun _ _ _ ↦ by simp)
  simp [Finset.sum_neg_distrib]

end ParabolicBasic
