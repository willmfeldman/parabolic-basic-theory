/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Perron.Class
public import ParabolicBasic.Viscosity.SliceAux

/-!
# Perron's method: the upper envelope is a subsolution; boundary values

The subsolution property of `W^*` is proved by a direct argument, the same as the stability lemma
`IsViscSubOn.of_tendstoLocallyUniformlyOn`. The boundary values (Step 3) are placed here rather
than in `Existence.lean` because the bump step uses them.

`perronUpper = W^*` and `perronLower = W_*` are the envelopes of `W = perronSup` relative to the
open cylinder `Ω = V ×ˢ Ioo a b`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- `W^*`: the upper envelope of the Perron supremum relative to `V ×ˢ Ioo a b`. -/
noncomputable def perronUpper (V : Set (E d)) (a b : ℝ) (f : E d → ℝ → ℝ) (g : E d × ℝ → ℝ) :
    E d × ℝ → ℝ :=
  upperEnv (V ×ˢ Ioo a b) (perronSup V a b f g)

/-- `W_*`: the lower envelope of the Perron supremum relative to `V ×ˢ Ioo a b`. -/
noncomputable def perronLower (V : Set (E d)) (a b : ℝ) (f : E d → ℝ → ℝ) (g : E d × ℝ → ℝ) :
    E d × ℝ → ℝ :=
  lowerEnv (V ×ˢ Ioo a b) (perronSup V a b f g)

namespace PerronHyp

variable {V : Set (E d)} {a b : ℝ} {f : E d → ℝ → ℝ} {g : E d × ℝ → ℝ}

/-! ### Envelope facts -/

theorem upperSemicontinuousOn_perronUpper (H : PerronHyp V a b f g) :
    UpperSemicontinuousOn (perronUpper V a b f g) (closure V ×ˢ Icc a b) := by
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  have := upperSemicontinuousOn_upperEnv hlo hup
  rwa [H.closure_cyl] at this

theorem lowerSemicontinuousOn_perronLower (H : PerronHyp V a b f g) :
    LowerSemicontinuousOn (perronLower V a b f g) (closure V ×ˢ Icc a b) := by
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  have := lowerSemicontinuousOn_lowerEnv hlo hup
  rwa [H.closure_cyl] at this

theorem perronSup_le_perronUpper (H : PerronHyp V a b f g) {q : E d × ℝ}
    (hq : q ∈ V ×ˢ Ioo a b) : perronSup V a b f g q ≤ perronUpper V a b f g q := by
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  exact le_upperEnv hup hq

theorem perronLower_le_perronSup (H : PerronHyp V a b f g) {q : E d × ℝ}
    (hq : q ∈ V ×ˢ Ioo a b) : perronLower V a b f g q ≤ perronSup V a b f g q := by
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  exact lowerEnv_le hlo hq

/-- `W^* ≤ U` on the closed cylinder for every continuous supersolution `U ≥ g` on `Γ`. -/
theorem perronUpper_le (H : PerronHyp V a b f g) {U : E d × ℝ → ℝ}
    (hU : ContinuousOn U (closure V ×ˢ Icc a b))
    (hsup : IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) U)
    (hgU : ∀ q ∈ parBdry V a b, g q ≤ U q) {z : E d × ℝ} (hz : z ∈ closure V ×ˢ Icc a b) :
    perronUpper V a b f g z ≤ U z := by
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  exact upperEnv_le_of_continuousWithinAt (H.closure_cyl ▸ hz) hlo
    ((hU z hz).mono H.cyl_subset) fun q hq ↦ H.perronSup_le hU hsup hgU hq

/-- `L ≤ W_*` on the closed cylinder for every continuous subsolution `L ≤ g` on `Γ`. -/
theorem le_perronLower (H : PerronHyp V a b f g) {L : E d × ℝ → ℝ}
    (hL : ContinuousOn L (closure V ×ˢ Icc a b))
    (hsub : IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) L)
    (hLg : ∀ q ∈ parBdry V a b, L q ≤ g q) {z : E d × ℝ} (hz : z ∈ closure V ×ˢ Icc a b) :
    L z ≤ perronLower V a b f g z := by
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  exact le_lowerEnv_of_continuousWithinAt (H.closure_cyl ▸ hz) hup
    ((hL z hz).mono H.cyl_subset) fun q hq ↦ H.le_perronSup (mem_perronClass hL hsub hLg) hq

/-! ### Step 2: `W^*` is a subsolution -/

/-- `W^*` is a subsolution in the open cylinder. Direct argument: strictify the test by the quartic,
pick `w ∈ 𝒫` and `q` with `w q` close to `W^*(z₀)`, and test `w` at a maximum point of `w - ψ'` on a
small closed ball. -/
theorem isViscSubOn_perronUpper (H : PerronHyp V a b f g) :
    IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) (perronUpper V a b f g) := by
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  have hΩo : IsOpen (V ×ˢ Ioo a b) := H.isOpen_cyl
  refine ⟨H.upperSemicontinuousOn_perronUpper.mono H.cyl_subset, fun ψ hψ z₀ hz₀ ht ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  set Wu := perronUpper V a b f g with hWu_def
  /- Strictification. -/
  set ψ' : E d × ℝ → ℝ := fun q ↦ ψ q + ViscAux.quartic z₀ q with hψ'_def
  have hσc : ContDiff ℝ 2 (ViscAux.quartic z₀) := ViscAux.contDiff_quartic z₀
  have hψ'c : ContDiff ℝ 2 ψ' := hψ.add hσc
  have hdt : dₜ ψ' z₀ = dₜ ψ z₀ := by
    rw [dₜ_add (hψ.differentiable two_ne_zero) (hσc.differentiable two_ne_zero),
      ViscAux.dₜ_quartic, add_zero]
  have hlap : lapₓ ψ' z₀ = lapₓ ψ z₀ := by
    rw [lapₓ_add hψ hσc, ViscAux.lapₓ_quartic, add_zero]
  have hψ'z : ψ' z₀ = Wu z₀ := by simp [ψ', ht.2.1]
  /- Continuity of the operator at `(z₀, W^* z₀)`. -/
  set G : (E d × ℝ) × ℝ → ℝ := fun pr ↦ dₜ ψ' pr.1 - lapₓ ψ' pr.1 + f pr.1.1 pr.2 with hG_def
  have hfc : ContinuousAt (fun pr : (E d × ℝ) × ℝ ↦ f pr.1.1 pr.2) (z₀, Wu z₀) := by
    have h1 : ContinuousAt (fun q : E d × ℝ ↦ f q.1 q.2) (z₀.1, Wu z₀) :=
      H.semilinear.continuousOn.continuousAt
        (prod_mem_nhds (mem_of_superset (H.isOpen.mem_nhds hz₀.1) subset_closure) univ_mem)
    exact h1.comp_of_eq (f := fun pr : (E d × ℝ) × ℝ ↦ (pr.1.1, pr.2))
      (continuous_fst.fst.prodMk continuous_snd).continuousAt rfl
  have hGc : ContinuousAt G (z₀, Wu z₀) :=
    ((((continuous_dₜ (hψ'c.of_le (by norm_num))).comp continuous_fst).sub
      ((continuous_lapₓ hψ'c).comp continuous_fst)).continuousAt).add hfc
  have hG0 : 0 < G (z₀, Wu z₀) := by
    simp only [G, hdt, hlap]
    exact hcon
  obtain ⟨δ, hδ, hδG⟩ := Metric.eventually_nhds_iff.1 (hGc.eventually (lt_mem_nhds hG0))
  /- A compact neighbourhood where `W^* ≤ ψ`. -/
  have hle : ∀ᶠ q in 𝓝 z₀, q ∈ V ×ˢ Ioo a b ∧ Wu q ≤ ψ q := by
    have := ht.2.2
    rw [hΩo.nhdsWithin_eq hz₀] at this
    filter_upwards [this, hΩo.mem_nhds hz₀] with q h1 h2 using ⟨h2, h1⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hle
  set ρ := min (ε₀ / 2) (δ / 2) with hρ_def
  have hρ : 0 < ρ := by positivity
  set K := closedBall z₀ ρ with hK_def
  have hKsub : K ⊆ ball z₀ ε₀ :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hpK : z₀ ∈ K := mem_closedBall_self hρ.le
  have hKΩ : K ⊆ V ×ˢ Ioo a b := fun q hq ↦ (hball (hKsub hq)).1
  have hstrict : ∀ w ∈ perronClass V a b f g, ∀ q ∈ K,
      w q - ψ' q ≤ -ViscAux.quartic z₀ q := fun w hw q hq ↦ by
    have h1 := H.le_perronSup hw (hKΩ hq)
    have h2 := H.perronSup_le_perronUpper (hKΩ hq)
    have h3 := (hball (hKsub hq)).2
    simp only [ψ']
    linarith
  /- Continuity of `ψ'` at `z₀`. -/
  obtain ⟨η₁, hη₁, hψ'η⟩ := Metric.continuousAt_iff.1 hψ'c.continuous.continuousAt (δ / 2)
    (by positivity)
  set s := min ρ η₁ with hs_def
  have hs : 0 < s := lt_min hρ hη₁
  set ε := min (s ^ 4) δ / 8 with hε_def
  have hε : 0 < ε := by positivity
  have hε1 : 3 * ε < s ^ 4 := by
    have := min_le_left (s ^ 4) δ
    have : 0 < s ^ 4 := by positivity
    rw [hε_def]; linarith
  have hε2 : 3 * ε < δ / 2 := by
    have := min_le_right (s ^ 4) δ
    rw [hε_def]; linarith
  /- A point `q` and a member `w` of the class with `w q` close to `W^*(z₀)`. -/
  have hfreq := frequently_lt_of_lt_upperEnv (subset_closure hz₀) hlo
    (y := Wu z₀ - ε) (by change Wu z₀ - ε < Wu z₀; linarith)
  have hev : ∀ᶠ q in 𝓝[V ×ˢ Ioo a b] z₀,
      q ∈ V ×ˢ Ioo a b ∧ dist q z₀ < s ∧ dist (ψ' q) (ψ' z₀) < ε := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hs),
      nhdsWithin_le_nhds ((hψ'c.continuous.tendsto z₀).eventually (ball_mem_nhds _ hε))]
      with q h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨q, hqW, hqΩ, hqs, hqψ⟩ := (hfreq.and_eventually hev).exists
  obtain ⟨w, hw, hwq⟩ := H.exists_lt_perronSup (show perronSup V a b f g q - ε < _ by linarith)
  have hqK : q ∈ K := mem_closedBall.2 (hqs.le.trans (min_le_left _ _))
  /- A maximum point `p` of `w - ψ'` on `K`. -/
  have husc : UpperSemicontinuousOn (fun q ↦ w q + -ψ' q) K :=
    (hw.1.mono (hKΩ.trans H.cyl_subset)).add
      hψ'c.continuous.neg.continuousOn.upperSemicontinuousOn
  simp only [← sub_eq_add_neg] at husc
  obtain ⟨p, hpK, hpmax⟩ := husc.exists_isMaxOn ⟨z₀, hpK⟩ (isCompact_closedBall z₀ ρ)
  have hmax : w q - ψ' q ≤ w p - ψ' p := hpmax hqK
  have hψq := abs_lt.1 (Real.dist_eq _ _ ▸ hqψ)
  have hlow : -(3 * ε) < w p - ψ' p := by linarith
  have hσp := hstrict w hw p hpK
  have hσnn := ViscAux.quartic_nonneg z₀ p
  have hdp : dist p z₀ < s := by
    have h4 : dist p z₀ ^ 4 < s ^ 4 := by
      have := ViscAux.dist_pow_four_le_quartic z₀ p
      linarith
    exact lt_of_pow_lt_pow_left₀ 4 hs.le h4
  have hdpρ : dist p z₀ < ρ := hdp.trans_le (min_le_left _ _)
  have hψp := abs_lt.1 (Real.dist_eq _ _ ▸ hψ'η (hdp.trans_le (min_le_right _ _)))
  have hGp : 0 < G (p, w p) := by
    refine hδG ?_
    have hρδ : ρ < δ := by rw [hρ_def]; exact (min_le_right _ _).trans_lt (by linarith)
    rw [Prod.dist_eq]
    refine max_lt (show dist p z₀ < δ from hdpρ.trans hρδ) ?_
    change dist (w p) (Wu z₀) < δ
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  /- The test inequality for `w` at `p`. -/
  have hpΩ : p ∈ V ×ˢ Ioo a b := hKΩ hpK
  have htouch : TouchesAbove (fun q ↦ ψ' q + (w p - ψ' p)) w (V ×ˢ Ioo a b) p := by
    refine ⟨hpΩ, by ring, ?_⟩
    have hmem : ball z₀ ρ ∈ 𝓝 p := isOpen_ball.mem_nhds (mem_ball.2 hdpρ)
    filter_upwards [nhdsWithin_le_nhds hmem] with q hq
    have := hpmax (ball_subset_closedBall hq)
    simp only [mem_setOf_eq] at this
    linarith
  have := hw.2.1.2 _ (hψ'c.add contDiff_const) p hpΩ htouch
  rw [dₜ_add_const, lapₓ_add_const] at this
  simp only [G] at hGp
  linarith

/-! ### Step 3: boundary values -/

/-- `W^* ≤ g` on `Γ`. -/
theorem perronUpper_le_g (H : PerronHyp V a b f g) {z : E d × ℝ} (hz : z ∈ parBdry V a b) :
    perronUpper V a b f g z ≤ g z := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨U, hU, hsup, hgU, hUz⟩ := H.barriers.upper z hz ε hε
  exact (H.perronUpper_le hU hsup hgU (H.parBdry_subset hz)).trans hUz

/-- `g ≤ W_*` on `Γ`. -/
theorem g_le_perronLower (H : PerronHyp V a b f g) {z : E d × ℝ} (hz : z ∈ parBdry V a b) :
    g z ≤ perronLower V a b f g z := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨L, hL, hsub, hLg, hLz⟩ := H.barriers.lower z hz ε hε
  have := H.le_perronLower hL hsub hLg (H.parBdry_subset hz)
  linarith

/-- `W^*` belongs to the Perron class. -/
theorem perronUpper_mem_perronClass (H : PerronHyp V a b f g) :
    perronUpper V a b f g ∈ perronClass V a b f g :=
  ⟨H.upperSemicontinuousOn_perronUpper, H.isViscSubOn_perronUpper,
    fun _ hq ↦ H.perronUpper_le_g hq⟩

/-- `W = W^*` in the open cylinder. -/
theorem perronUpper_eq_perronSup (H : PerronHyp V a b f g) {q : E d × ℝ}
    (hq : q ∈ V ×ˢ Ioo a b) : perronUpper V a b f g q = perronSup V a b f g q :=
  le_antisymm (H.le_perronSup H.perronUpper_mem_perronClass hq) (H.perronSup_le_perronUpper hq)

theorem perronLower_le_perronUpper (H : PerronHyp V a b f g) {q : E d × ℝ}
    (hq : q ∈ V ×ˢ Ioo a b) : perronLower V a b f g q ≤ perronUpper V a b f g q :=
  (H.perronLower_le_perronSup hq).trans (H.perronSup_le_perronUpper hq)

end PerronHyp

end ParabolicBasic
