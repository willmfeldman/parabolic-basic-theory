/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Perron.SupStability
public import ParabolicBasic.Classical.ToViscosity

/-!
# Perron's method: the bump

The bump construction (CIL *User's guide*, Lemma 4.4, with one correction: the bumped competitor is
built from the USC envelope `W^*`, not from `W`). The lower envelope `W_*` is a supersolution. **No
comparison principle is used.**
-/

@[expose] public section

open Set Filter Topology Metric

namespace ParabolicBasic

variable {d : ℕ}

namespace PerronHyp

variable {V : Set (E d)} {a b : ℝ} {f : E d → ℝ → ℝ} {g : E d × ℝ → ℝ}

/-- `W_*` is a supersolution in the open cylinder. -/
theorem isViscSuperOn_perronLower (H : PerronHyp V a b f g) :
    IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) (perronLower V a b f g) := by
  classical
  obtain ⟨m, M, hlo, hup⟩ := H.exists_bounds
  have hΩo : IsOpen (V ×ˢ Ioo a b) := H.isOpen_cyl
  refine ⟨H.lowerSemicontinuousOn_perronLower.mono H.cyl_subset, fun ψ hψ z₀ hz₀ ht ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  set Wl := perronLower V a b f g with hWl_def
  set Wu := perronUpper V a b f g with hWu_def
  /- The quartic bump `φ = ψ - σ`. -/
  set φ : E d × ℝ → ℝ := fun q ↦ ψ q - ViscAux.quartic z₀ q with hφ_def
  have hσc : ContDiff ℝ 2 (ViscAux.quartic z₀) := ViscAux.contDiff_quartic z₀
  have hφc : ContDiff ℝ 2 φ := hψ.sub hσc
  have hdt : dₜ φ z₀ = dₜ ψ z₀ := by
    rw [dₜ_sub (hψ.differentiable two_ne_zero) (hσc.differentiable two_ne_zero),
      ViscAux.dₜ_quartic, sub_zero]
  have hlap : lapₓ φ z₀ = lapₓ ψ z₀ := by
    rw [lapₓ_sub hψ hσc, ViscAux.lapₓ_quartic, sub_zero]
  have hφz : φ z₀ = Wl z₀ := by simp [φ, ht.2.1]
  /- Continuity of the operator at `(z₀, W_* z₀)`. -/
  set G : (E d × ℝ) × ℝ → ℝ := fun pr ↦ dₜ φ pr.1 - lapₓ φ pr.1 + f pr.1.1 pr.2 with hG_def
  have hfc : ContinuousAt (fun pr : (E d × ℝ) × ℝ ↦ f pr.1.1 pr.2) (z₀, Wl z₀) := by
    have h1 : ContinuousAt (fun q : E d × ℝ ↦ f q.1 q.2) (z₀.1, Wl z₀) :=
      H.semilinear.continuousOn.continuousAt
        (prod_mem_nhds (mem_of_superset (H.isOpen.mem_nhds hz₀.1) subset_closure) univ_mem)
    exact h1.comp_of_eq (f := fun pr : (E d × ℝ) × ℝ ↦ (pr.1.1, pr.2))
      (continuous_fst.fst.prodMk continuous_snd).continuousAt rfl
  have hGc : ContinuousAt G (z₀, Wl z₀) :=
    ((((continuous_dₜ (hφc.of_le (by norm_num))).comp continuous_fst).sub
      ((continuous_lapₓ hφc).comp continuous_fst)).continuousAt).add hfc
  have hG0 : G (z₀, Wl z₀) < 0 := by
    simp only [G, hdt, hlap]
    exact hcon
  obtain ⟨δ, hδ, hδG⟩ := Metric.eventually_nhds_iff.1 (hGc.eventually (gt_mem_nhds hG0))
  /- A ball where `ψ ≤ W_*`. -/
  have hle : ∀ᶠ q in 𝓝 z₀, q ∈ V ×ˢ Ioo a b ∧ ψ q ≤ Wl q := by
    have := ht.2.2
    rw [hΩo.nhdsWithin_eq hz₀] at this
    filter_upwards [this, hΩo.mem_nhds hz₀] with q h1 h2 using ⟨h2, h1⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hle
  obtain ⟨η₁, hη₁, hφη⟩ := Metric.continuousAt_iff.1 hφc.continuous.continuousAt (δ / 2)
    (by positivity)
  set r := min (ε₀ / 2) (min δ η₁) with hr_def
  have hr : 0 < r := by positivity
  have hrε : r < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrδ : r ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hrη : r ≤ η₁ := (min_le_right _ _).trans (min_le_right _ _)
  have hBsub : ∀ p, dist p z₀ < r → p ∈ V ×ˢ Ioo a b ∧ ψ p ≤ Wl p := fun p hp ↦
    hball (mem_ball.2 (hp.trans hrε))
  have hBΩ : ball z₀ r ⊆ V ×ˢ Ioo a b := fun p hp ↦ (hBsub p (mem_ball.1 hp)).1
  /- The bump height `κ` and the competitor `ψ̃ = φ + κ`. -/
  set κ := min (δ / 2) ((r / 2) ^ 4 / 2) with hκ_def
  have hκ : 0 < κ := by positivity
  have hκδ : κ ≤ δ / 2 := min_le_left _ _
  have hκr : κ < (r / 2) ^ 4 := by
    have := min_le_right (δ / 2) ((r / 2) ^ 4 / 2)
    have : 0 < (r / 2) ^ 4 := by positivity
    rw [hκ_def]; linarith
  set ψt : E d × ℝ → ℝ := fun q ↦ φ q + κ with hψt_def
  have hψtc : ContDiff ℝ 2 ψt := hφc.add contDiff_const
  /- (i) `ψ̃` is a classical, hence viscosity, subsolution on the ball. -/
  have hψt_sub : IsViscSubOn (ball z₀ r) (fun p r ↦ f p.1 r) ψt := by
    refine isViscSubOn_of_contDiffOn isOpen_ball hψtc.contDiffOn fun p hp ↦ ?_
    rw [dₜ_add_const, lapₓ_add_const]
    have hp' := mem_ball.1 hp
    have hφp := abs_lt.1 (Real.dist_eq _ _ ▸ hφη (hp'.trans_le hrη))
    have := hδG (y := (p, ψt p)) (by
      rw [Prod.dist_eq]
      refine max_lt (show dist p z₀ < δ from hp'.trans_le hrδ) ?_
      change dist (φ p + κ) (Wl z₀) < δ
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith)
    exact this.le
  /- (ii) Off the half ball, `ψ̃ ≤ W^*`. -/
  have hann : ∀ p, dist p z₀ < r → r / 2 < dist p z₀ → ψt p ≤ Wu p := fun p hp hp2 ↦ by
    obtain ⟨hpΩ, hψp⟩ := hBsub p hp
    have h1 := ViscAux.dist_pow_four_le_quartic z₀ p
    have h2 : (r / 2) ^ 4 < dist p z₀ ^ 4 := pow_lt_pow_left₀ hp2 (by positivity) (by norm_num)
    have h3 := H.perronLower_le_perronUpper hpΩ
    simp only [ψt, φ]
    linarith
  /- The bumped function `Ŵ`. -/
  set Wh : E d × ℝ → ℝ := fun p ↦ if p ∈ ball z₀ r then max (Wu p) (ψt p) else Wu p with hWh_def
  have hWh_in : ∀ p ∈ ball z₀ r, Wh p = max (Wu p) (ψt p) := fun p hp ↦ ite_eq_left hp
  have hWh_out : ∀ p, r / 2 < dist p z₀ → Wh p = Wu p := fun p hp ↦ by
    by_cases hpB : p ∈ ball z₀ r
    · rw [hWh_in p hpB, max_eq_left (hann p (mem_ball.1 hpB) hp)]
    · exact ite_eq_right hpB
  set O₂ : Set (E d × ℝ) := {p | r / 2 < dist p z₀} with hO₂_def
  have hO₂ : IsOpen O₂ := isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hO₂mem : ∀ p, p ∉ ball z₀ r → p ∈ O₂ := fun p hp ↦ by
    have := not_lt.1 (mt mem_ball.2 hp)
    change r / 2 < dist p z₀
    linarith
  have hWu_usc := H.upperSemicontinuousOn_perronUpper
  have hWu_sub := H.isViscSubOn_perronUpper
  have hWh_mem : Wh ∈ perronClass V a b f g := by
    refine ⟨fun p hp ↦ ?_, ?_, fun q hq ↦ ?_⟩
    · by_cases hpB : p ∈ ball z₀ r
      · refine UpperSemicontinuousWithinAt.congr_of_eventuallyEq
          (UpperSemicontinuousWithinAt.sup (hWu_usc p hp)
            hψtc.continuous.continuousAt.continuousWithinAt.upperSemicontinuousWithinAt) hp ?_
        filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hpB)] with q hq
        exact (hWh_in q hq).symm
      · refine UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hWu_usc p hp) hp ?_
        filter_upwards [nhdsWithin_le_nhds (hO₂.mem_nhds (hO₂mem p hpB))] with q hq
        exact (hWh_out q hq).symm
    · refine IsViscSubOn.of_locally hΩo fun p hp ↦ ?_
      by_cases hpB : p ∈ ball z₀ r
      · refine ⟨ball z₀ r, isOpen_ball, hpB, hBΩ, ?_⟩
        exact ((hWu_sub.mono_set isOpen_ball hBΩ).max hψt_sub).of_eqOn
          fun q hq ↦ (hWh_in q hq).symm
      · refine ⟨O₂ ∩ V ×ˢ Ioo a b, hO₂.inter hΩo, ⟨hO₂mem p hpB, hp⟩, inter_subset_right, ?_⟩
        exact (hWu_sub.mono_set (hO₂.inter hΩo) inter_subset_right).of_eqOn
          fun q hq ↦ (hWh_out q hq.1).symm
    · have hqB : q ∉ ball z₀ r := fun h ↦ notMem_cyl_of_mem_parBdry H.isOpen hq (hBΩ h)
      rw [show Wh q = Wu q from ite_eq_right hqB]
      exact H.perronUpper_le_g hq
  /- (iii) Contradiction at points where `W` is close to `W_*(z₀)`. -/
  have hfreq := frequently_lt_of_lowerEnv_lt (subset_closure hz₀) hup
    (y := Wl z₀ + κ / 2) (by change Wl z₀ < Wl z₀ + κ / 2; linarith)
  have hψtz : ψt z₀ = Wl z₀ + κ := by simp only [ψt, hφz]
  have hev : ∀ᶠ q in 𝓝[V ×ˢ Ioo a b] z₀,
      q ∈ V ×ˢ Ioo a b ∧ q ∈ ball z₀ r ∧ ψt z₀ - κ / 2 < ψt q := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hr),
      nhdsWithin_le_nhds ((hψtc.continuous.tendsto z₀).eventually
        (lt_mem_nhds (show ψt z₀ - κ / 2 < ψt z₀ by linarith)))]
      with q h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨q, hqW, hqΩ, hqB, hqψ⟩ := (hfreq.and_eventually hev).exists
  have h1 := H.le_perronSup hWh_mem hqΩ
  rw [hWh_in q hqB] at h1
  have h2 := le_max_right (Wu q) (ψt q)
  linarith

end PerronHyp

end ParabolicBasic
