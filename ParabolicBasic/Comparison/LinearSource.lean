/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Comparison.Continuous

/-!
# Comparison with a linear source

* `sub_le_of_heat_source`: if `dₜu − lapₓu ≤ H₁ ≤ σ + δ` and `dₜv − lapₓv ≥ H₂ ≥ σ` (viscosity
  sense) and `u ≤ v` on the parabolic boundary, then `u ≤ v + δ (t − a)` on `closure V ×ˢ Ico a b`;
* `closure_cCyl`: the closure of a centred cylinder (all `d`, including `d = 0`);
* `abs_sub_le_of_heat_source_cCyl`: the two-sided form on a centred cylinder, the shape used by the
  Schauder iteration.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-- The affine function `δ (t − a)`: `dₜ = δ`. -/
theorem dₜ_affine_time (δ a : ℝ) (p : E d × ℝ) : dₜ (fun q : E d × ℝ ↦ δ * (q.2 - a)) p = δ := by
  have h : HasDerivAt (fun s : ℝ ↦ δ * (s - a)) (δ * 1) p.2 :=
    ((hasDerivAt_id p.2).sub_const a).const_mul δ
  change deriv (fun s : ℝ ↦ δ * (s - a)) p.2 = δ
  rw [h.deriv, mul_one]

/-- The affine function `δ (t − a)`: `lapₓ = 0`. -/
theorem lapₓ_affine_time (δ a : ℝ) (p : E d × ℝ) :
    lapₓ (fun q : E d × ℝ ↦ δ * (q.2 - a)) p = 0 := by
  change Δ (fun _ : E d ↦ δ * (p.2 - a)) p.1 = 0
  simp

/-- **Comparison with a linear source**: `u ≤ v + δ (t − a)` on `closure V ×ˢ Ico a b`. -/
theorem sub_le_of_heat_source {V : Set (E d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {a b : ℝ} (hab : a < b) {u v H₁ H₂ σ : E d × ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hσ : ContinuousOn σ (closure V ×ˢ Icc a b))
    (hH₁ : ∀ p ∈ V ×ˢ Ioo a b, H₁ p ≤ σ p + δ) (hH₂ : ∀ p ∈ V ×ˢ Ioo a b, σ p ≤ H₂ p)
    (husc : UpperSemicontinuousOn u (closure V ×ˢ Icc a b))
    (hvlsc : LowerSemicontinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsViscSubOn (V ×ˢ Ioo a b) (fun p _ ↦ -H₁ p) u)
    (hsuper : IsViscSuperOn (V ×ˢ Ioo a b) (fun p _ ↦ -H₂ p) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Ico a b, u p ≤ v p + δ * (p.2 - a) := by
  have hQo : IsOpen (V ×ˢ Ioo a b) := hV.prod isOpen_Ioo
  set φ : E d × ℝ → ℝ := fun q ↦ δ * (q.2 - a) with hφ
  have hφc : Continuous φ := continuous_const.mul (continuous_snd.sub continuous_const)
  have hφd : ContDiffOn ℝ 2 φ (V ×ˢ Ioo a b) :=
    (contDiff_const.mul (contDiff_snd.sub contDiff_const)).contDiffOn
  have hsub' : IsViscSubOn (V ×ˢ Ioo a b)
      (fun p z ↦ (fun (_ : E d) (_ : ℝ) ↦ (0 : ℝ)) p.1 z - (σ p + δ)) u :=
    hsub.mono_source fun p hp _ ↦ by simp only; linarith [hH₁ p hp]
  have hsuper' : IsViscSuperOn (V ×ˢ Ioo a b)
      (fun p z ↦ (fun (_ : E d) (_ : ℝ) ↦ (0 : ℝ)) p.1 z - (σ p + δ)) (fun p ↦ v p + φ p) :=
    (hsuper.add_contDiff hQo hφd).mono_source fun p hp _ ↦ by
      simp only [hφ, dₜ_affine_time, lapₓ_affine_time]
      linarith [hH₂ p hp]
  have hmain := comparison_usc_lsc_source hV hVb hab (f := fun _ _ ↦ 0)
    ⟨0, 1, one_pos, le_rfl, fun _ _ _ _ _ ↦ by simp⟩ ⟨0, fun _ _ _ _ ↦ by simp⟩
    (hσ.add continuousOn_const) husc
    (LowerSemicontinuousOn.add hvlsc hφc.continuousOn.lowerSemicontinuousOn) hsub' hsuper'
    (fun p hp ↦ by
      have h1 := hbdry p hp
      have h2 : a ≤ p.2 := (parBdry_subset_closure V hab.le hp).2.1
      have : 0 ≤ φ p := mul_nonneg hδ (sub_nonneg.2 h2)
      linarith)
  exact hmain

/-- The closure of a centred cylinder, for every `d` (including `d = 0`). -/
theorem closure_cCyl (x₀ : E d) (t₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    closure (cCyl x₀ t₀ r) = closedBall x₀ r ×ˢ Icc (t₀ - r ^ 2) (t₀ + r ^ 2) := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  rw [cCyl, closure_prod_Ioo_eq _ (by linarith), closure_ball x₀ hr.ne']

/-- Two-sided comparison on a centred cylinder: if `H` is `δ`-close to the constant `c`, then
`|u − h| ≤ 2 r² δ`. -/
theorem abs_sub_le_of_heat_source_cCyl (x₀ : E d) (t₀ : ℝ) {r : ℝ} (hr : 0 < r)
    {u h H : E d × ℝ → ℝ} {c δ : ℝ}
    (hu : ContinuousOn u (closure (cCyl x₀ t₀ r))) (hh : ContinuousOn h (closure (cCyl x₀ t₀ r)))
    (husub : IsViscSubOn (cCyl x₀ t₀ r) (fun p _ ↦ -H p) u)
    (husuper : IsViscSuperOn (cCyl x₀ t₀ r) (fun p _ ↦ -H p) u)
    (hhsub : IsViscSubOn (cCyl x₀ t₀ r) (fun _ _ ↦ -c) h)
    (hhsuper : IsViscSuperOn (cCyl x₀ t₀ r) (fun _ _ ↦ -c) h)
    (hH : ∀ p ∈ cCyl x₀ t₀ r, |H p - c| ≤ δ)
    (hbd : EqOn u h (parBdry (ball x₀ r) (t₀ - r ^ 2) (t₀ + r ^ 2))) :
    ∀ p ∈ closure (cCyl x₀ t₀ r), |u p - h p| ≤ 2 * r ^ 2 * δ := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  set a := t₀ - r ^ 2 with ha
  set b := t₀ + r ^ 2 with hb
  have hab : a < b := by linarith
  have hcl : closure (cCyl x₀ t₀ r) = closure (ball x₀ r) ×ˢ Icc a b :=
    closure_prod_Ioo_eq _ hab
  rw [hcl] at hu hh ⊢
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hH (x₀, t₀) ⟨mem_ball_self hr, by
    simp only [mem_Ioo]; constructor <;> linarith⟩)
  have hVo : IsOpen (ball x₀ r) := isOpen_ball
  have hVb : Bornology.IsBounded (ball x₀ r) := isBounded_ball
  have h1 := sub_le_of_heat_source (σ := fun _ ↦ c) (H₂ := fun _ ↦ c) hVo hVb hab hδ
    continuousOn_const (fun p hp ↦ by linarith [(abs_le.1 (hH p hp)).2]) (fun _ _ ↦ le_rfl)
    hu.upperSemicontinuousOn hh.lowerSemicontinuousOn husub hhsuper
    (fun p hp ↦ (hbd hp).le)
  have h2 := sub_le_of_heat_source (σ := fun _ ↦ c - δ) (H₁ := fun _ ↦ c) hVo hVb hab hδ
    continuousOn_const (fun _ _ ↦ by linarith)
    (fun p hp ↦ by linarith [(abs_le.1 (hH p hp)).1])
    hh.upperSemicontinuousOn hu.lowerSemicontinuousOn hhsub husuper
    (fun p hp ↦ (hbd hp).ge)
  refine le_on_Icc_of_le_on_Ico hab (hu.sub hh).abs continuousOn_const fun p hp ↦ ?_
  have ht : δ * (p.2 - a) ≤ 2 * r ^ 2 * δ := by
    have : p.2 - a ≤ 2 * r ^ 2 := by linarith [hp.2.2]
    nlinarith
  rw [abs_le]
  constructor
  · linarith [h2 p hp]
  · linarith [h1 p hp]

end ParabolicBasic
