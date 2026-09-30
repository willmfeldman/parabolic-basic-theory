/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Viscosity
public import ParabolicBasic.Defs.Parabolic
public import ParabolicBasic.Calculus.Slice
public import ParabolicBasic.Viscosity.Basic

/-!
# Penalized maximum principle with a source

Here `W` is only upper semicontinuous (Perron members are USC), the barrier `b` is only `C²` in
`Ω`, and the equation carries a source term `F : E d × ℝ → ℝ` (evaluated only at the maximum
point, so no regularity is needed).

* `penalty T₁ q = (T₁ - q.2)⁻¹` and `dₜ_sub_lapₓ_penalty`;
* `exists_isMaxOn_penalized`: the penalized difference attains its maximum inside `Ω`;
* `domain_comparison_sub` / `_super`: a viscosity sub/supersolution lies below/above a classical
  super/subsolution on `closure Ω ∩ {t < T₁}` if it does on `frontier Ω ∩ {t < T₁}`;
  the `_of_continuousOn` forms reach all of `closure Ω`;
* `comparison_classical_cyl_sub` / `_super` (and `_of_continuousOn`): the same on cylinders
  `A × (T₀, T₁)` with data on the parabolic boundary.

The proof is the Ishii-free penalization argument: a positive maximum of `W - b - ε/(T₁ - t)` is
attained at an interior point, where `b + ε/(T₁ - t) + const` touches `W` from above, and the
test inequality contradicts `dₜb - Δₓb + F ≥ 0` because `(∂ₜ - Δₓ)(T₁ - t)⁻¹ > 0`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-! ### The penalization `ε / (T₁ - t)` -/

/-- The penalization profile `(T₁ - t)⁻¹`. -/
noncomputable def penalty (T₁ : ℝ) (q : E d × ℝ) : ℝ := (T₁ - q.2)⁻¹

theorem penalty_pos {T₁ : ℝ} {q : E d × ℝ} (hq : q.2 < T₁) : 0 < penalty T₁ q :=
  inv_pos.2 (sub_pos.2 hq)

theorem contDiffOn_penalty {n : WithTop ℕ∞} (T₁ : ℝ) :
    ContDiffOn ℝ n (penalty (d := d) T₁) {q | q.2 < T₁} :=
  ((contDiff_const.sub contDiff_snd).contDiffOn).inv fun _ hq ↦ (sub_pos.2 hq).ne'

theorem continuousOn_penalty (T₁ : ℝ) :
    ContinuousOn (penalty (d := d) T₁) {q | q.2 < T₁} :=
  (contDiffOn_penalty (n := 0) T₁).continuousOn

theorem isOpen_setOf_snd_lt (T₁ : ℝ) : IsOpen {q : E d × ℝ | q.2 < T₁} :=
  isOpen_lt continuous_snd continuous_const

/-- Heat operator of the penalization: `(∂ₜ - Δₓ) (T₁ - t)⁻¹ = ((T₁ - t) ^ 2)⁻¹` for `t < T₁`. -/
theorem dₜ_sub_lapₓ_penalty {T₁ : ℝ} {p : E d × ℝ} (hp : p.2 < T₁) :
    dₜ (penalty T₁) p - lapₓ (penalty T₁) p = ((T₁ - p.2) ^ 2)⁻¹ := by
  have hne : T₁ - p.2 ≠ 0 := (sub_pos.2 hp).ne'
  have hd : HasDerivAt (fun s : ℝ ↦ (T₁ - s)⁻¹) (-(-1) / (T₁ - p.2) ^ 2) p.2 :=
    ((hasDerivAt_id p.2).const_sub T₁).inv hne
  have h1 : dₜ (penalty T₁) p = ((T₁ - p.2) ^ 2)⁻¹ := by
    simp only [dₜ, penalty]
    rw [hd.deriv]
    field_simp
  have h2 : lapₓ (penalty T₁) p = 0 := by
    simp only [lapₓ, penalty]
    rw [InnerProductSpace.laplacian_const]
    rfl
  rw [h1, h2, sub_zero]

/-! ### The penalized maximum -/

section Max

variable {Ω : Set (E d × ℝ)} {D : E d × ℝ → ℝ} {T₁ : ℝ}

/-- **Penalized maximum** (for USC `D`). Let `Ω ⊆ {t < T₁}` be
open and bounded, `D` upper semicontinuous on `closure Ω` with `D ≤ 0` on
`frontier Ω ∩ {t < T₁}`. If `D - ε (T₁ - t)⁻¹` is positive somewhere on `Ω`, it attains its
maximum over `Ω` at a point of `Ω`. -/
theorem exists_isMaxOn_penalized (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩT : ∀ p ∈ Ω, p.2 < T₁) (hD : UpperSemicontinuousOn D (closure Ω))
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → D p ≤ 0)
    {ε : ℝ} (hε : 0 < ε) {q₁ : E d × ℝ} (hq₁ : q₁ ∈ Ω) (hpos : 0 < D q₁ - ε * penalty T₁ q₁) :
    ∃ p ∈ Ω, 0 < D p - ε * penalty T₁ p ∧
      ∀ q ∈ Ω, D q - ε * penalty T₁ q ≤ D p - ε * penalty T₁ p := by
  have hK₀ : IsCompact (closure Ω) := hΩb.isCompact_closure
  obtain ⟨Λ₀, hΛ₀⟩ := hD.bddAbove_of_isCompact hK₀
  set Λ := max Λ₀ 0 with hΛdef
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hDΛ : ∀ q ∈ closure Ω, D q ≤ Λ := fun q hq ↦
    (hΛ₀ (mem_image_of_mem D hq)).trans (le_max_left _ _)
  set δ := ε / (Λ + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  -- near the top time the penalized function is negative
  have hneg : ∀ q ∈ closure Ω, q.2 < T₁ → T₁ - δ < q.2 → D q - ε * penalty T₁ q < 0 := by
    intro q hq hqT hqδ
    have hpos' : 0 < T₁ - q.2 := sub_pos.2 hqT
    have hlt : ε * penalty T₁ q > Λ + 1 := by
      rw [penalty, ← div_eq_mul_inv, gt_iff_lt, lt_div_iff₀ hpos']
      have : (Λ + 1) * (T₁ - q.2) < (Λ + 1) * δ :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      rwa [hδdef, mul_div_cancel₀ _ (by linarith)] at this
    linarith [hDΛ q hq]
  set K := closure Ω ∩ {q | q.2 ≤ T₁ - δ} with hKdef
  have hK : IsCompact K := hK₀.inter_right (isClosed_le continuous_snd continuous_const)
  have hKT : ∀ q ∈ K, q.2 < T₁ := fun q hq ↦ by linarith [hq.2.out]
  have hfK : UpperSemicontinuousOn (fun q ↦ D q - ε * penalty T₁ q) K := by
    have hc : ContinuousOn (fun q ↦ -(ε * penalty T₁ q)) K :=
      (continuousOn_const.mul ((continuousOn_penalty T₁).mono fun q hq ↦ hKT q hq)).neg
    simp only [sub_eq_add_neg]
    exact (hD.mono inter_subset_left).add hc.upperSemicontinuousOn
  have hq₁K : q₁ ∈ K := by
    refine ⟨subset_closure hq₁, ?_⟩
    by_contra h
    exact absurd hpos (not_lt.2 (hneg q₁ (subset_closure hq₁) (hΩT q₁ hq₁)
      (by simpa using h)).le)
  obtain ⟨p, hpK, hpmax⟩ := hfK.exists_isMaxOn ⟨q₁, hq₁K⟩ hK
  have hpq₁ : D q₁ - ε * penalty T₁ q₁ ≤ D p - ε * penalty T₁ p := hpmax hq₁K
  have hppos : 0 < D p - ε * penalty T₁ p := hpos.trans_le hpq₁
  have hpT : p.2 < T₁ := hKT p hpK
  -- the maximum point is not on the frontier, hence in `Ω`
  have hpΩ : p ∈ Ω := by
    have hnf : p ∉ frontier Ω := fun hfr ↦ by
      have h1 := hbdry p hfr hpT
      have h2 := penalty_pos (d := d) hpT
      nlinarith
    have : p ∈ closure Ω \ frontier Ω := ⟨hpK.1, hnf⟩
    rwa [closure_sdiff_frontier, hΩo.interior_eq] at this
  refine ⟨p, hpΩ, hppos, fun q hq ↦ ?_⟩
  by_cases hqK : q.2 ≤ T₁ - δ
  · exact hpmax ⟨subset_closure hq, hqK⟩
  · exact (hneg q (subset_closure hq) (hΩT q hq) (not_le.1 hqK)).le.trans hppos.le

/-- If `D ≤ ε (T₁ - t)⁻¹` on `Ω ⊆ {t < T₁}` for every `ε > 0`, then `D ≤ 0` on `Ω`. -/
theorem nonpos_of_penalized (hΩT : ∀ p ∈ Ω, p.2 < T₁)
    (h : ∀ ε > 0, ∀ q ∈ Ω, D q - ε * penalty T₁ q ≤ 0) : ∀ q ∈ Ω, D q ≤ 0 := by
  intro q hq
  have hpos : 0 < T₁ - q.2 := sub_pos.2 (hΩT q hq)
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have := h (η * (T₁ - q.2)) (mul_pos hη hpos) q hq
  rw [penalty, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one] at this
  linarith

/-- If `D ≤ ε (T₁ - t)⁻¹` on `Ω ⊆ {t < T₁}` for every `ε > 0` and `D` is continuous on
`closure Ω`, then `D ≤ 0` on `closure Ω` (including the top face `closure Ω ∩ {t = T₁}`). -/
theorem nonpos_on_closure_of_penalized (hΩT : ∀ p ∈ Ω, p.2 < T₁)
    (hD : ContinuousOn D (closure Ω))
    (h : ∀ ε > 0, ∀ q ∈ Ω, D q - ε * penalty T₁ q ≤ 0) : ∀ p ∈ closure Ω, D p ≤ 0 := by
  intro p hp
  exact ContinuousWithinAt.closure_le hp ((hD p hp).mono subset_closure) continuousWithinAt_const
    (nonpos_of_penalized hΩT h)

end Max

/-! ### Comparison on a bounded open set -/

section Domain

variable {Ω : Set (E d × ℝ)} {T₁ : ℝ} {F : E d × ℝ → ℝ} {W b : E d × ℝ → ℝ}

/-- The penalized comparison inside `Ω`: under the hypotheses of `domain_comparison_sub`,
`W ≤ b` on `Ω`. -/
theorem le_on_of_domain_comparison_sub (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩT : ∀ p ∈ Ω, p.2 < T₁) (hW : IsViscSubOn Ω (fun p _ ↦ F p) W)
    (hWusc : UpperSemicontinuousOn W (closure Ω))
    (hbc : ContinuousOn b (closure Ω)) (hb : ContDiffOn ℝ 2 b Ω)
    (hheat : ∀ p ∈ Ω, 0 ≤ dₜ b p - lapₓ b p + F p)
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → W p ≤ b p) :
    ∀ q ∈ Ω, W q ≤ b q := by
  set D : E d × ℝ → ℝ := fun q ↦ W q - b q with hDdef
  have hD : UpperSemicontinuousOn D (closure Ω) := by
    simpa [hDdef, sub_eq_add_neg] using hWusc.add hbc.neg.upperSemicontinuousOn
  suffices h : ∀ q ∈ Ω, D q ≤ 0 from fun q hq ↦ sub_nonpos.1 (h q hq)
  refine nonpos_of_penalized hΩT fun ε hε q₁ hq₁ ↦ ?_
  by_contra hpos
  rw [not_le] at hpos
  obtain ⟨p, hpΩ, -, hmax⟩ := exists_isMaxOn_penalized hΩo hΩb hΩT hD
    (fun p hp hpT ↦ sub_nonpos.2 (hbdry p hp hpT)) hε hq₁ hpos
  have hpT : p.2 < T₁ := hΩT p hpΩ
  have hpen : ContDiffOn ℝ 2 (penalty T₁) Ω := (contDiffOn_penalty T₁).mono hΩT
  set c := W p - (b p + ε * penalty T₁ p) with hc
  -- the penalized barrier plus a constant touches `W` from above in `Ω` at `p`
  have ht : TouchesAbove (fun q ↦ b q + (ε * penalty T₁ q + c)) W Ω p := by
    refine ⟨hpΩ, by rw [hc]; ring, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    have := hmax q hq
    simp only [hDdef] at this
    rw [hc]
    linarith
  have hsmooth : ContDiffOn ℝ 2 (fun q ↦ b q + (ε * penalty T₁ q + c)) Ω :=
    hb.add ((contDiffOn_const.mul hpen).add contDiffOn_const)
  have h1 := hW.of_contDiffOn_test hΩo hpΩ hsmooth ht
  rw [dₜ_sub_lapₓ_add_mul_add_of_contDiffOn hΩo hpΩ hb hpen, dₜ_sub_lapₓ_penalty hpT] at h1
  have h2 := hheat p hpΩ
  have h3 : 0 < ε * ((T₁ - p.2) ^ 2)⁻¹ :=
    mul_pos hε (inv_pos.2 (pow_pos (sub_pos.2 hpT) 2))
  linarith

/-- **Comparison on a bounded open set** (sub form). Let `Ω ⊆ {t < T₁}` be open and bounded. A
viscosity subsolution `W` of `dₜW - lapₓW + F ≤ 0` in `Ω`, USC on `closure Ω`, lies below a
classical supersolution `b` (continuous on `closure Ω`, `C²` in `Ω`, `dₜb - lapₓb + F ≥ 0`) on
`closure Ω ∩ {t < T₁}` if it does on `frontier Ω ∩ {t < T₁}`. -/
theorem domain_comparison_sub (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩT : ∀ p ∈ Ω, p.2 < T₁) (hW : IsViscSubOn Ω (fun p _ ↦ F p) W)
    (hWusc : UpperSemicontinuousOn W (closure Ω))
    (hbc : ContinuousOn b (closure Ω)) (hb : ContDiffOn ℝ 2 b Ω)
    (hheat : ∀ p ∈ Ω, 0 ≤ dₜ b p - lapₓ b p + F p)
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → W p ≤ b p) :
    ∀ p ∈ closure Ω, p.2 < T₁ → W p ≤ b p := by
  intro p hp hpT
  by_cases hpΩ : p ∈ Ω
  · exact le_on_of_domain_comparison_sub hΩo hΩb hΩT hW hWusc hbc hb hheat hbdry p hpΩ
  · refine hbdry p ?_ hpT
    rw [← closure_sdiff_interior, hΩo.interior_eq]
    exact ⟨hp, hpΩ⟩

/-- **Comparison on a bounded open set** (sub form, continuous `W`): the conclusion holds on all
of `closure Ω`, including the top face. -/
theorem domain_comparison_sub_of_continuousOn (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩT : ∀ p ∈ Ω, p.2 < T₁) (hW : IsViscSubOn Ω (fun p _ ↦ F p) W)
    (hWc : ContinuousOn W (closure Ω))
    (hbc : ContinuousOn b (closure Ω)) (hb : ContDiffOn ℝ 2 b Ω)
    (hheat : ∀ p ∈ Ω, 0 ≤ dₜ b p - lapₓ b p + F p)
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → W p ≤ b p) :
    ∀ p ∈ closure Ω, W p ≤ b p := by
  intro p hp
  exact ContinuousWithinAt.closure_le hp ((hWc p hp).mono subset_closure)
    ((hbc p hp).mono subset_closure)
    (le_on_of_domain_comparison_sub hΩo hΩb hΩT hW hWc.upperSemicontinuousOn hbc hb hheat
      hbdry)

/-- Negation turns the hypotheses of `domain_comparison_super` into those of
`domain_comparison_sub`. -/
theorem IsViscSuperOn.neg_source {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ} {W : E d × ℝ → ℝ}
    (hW : IsViscSuperOn Ω (fun p _ ↦ F p) W) :
    IsViscSubOn Ω (fun p _ ↦ -F p) (fun q ↦ -W q) :=
  isViscSuperOn_neg_iff.1 hW

theorem heat_neg_add_neg (b : E d × ℝ → ℝ) (F : E d × ℝ → ℝ) (p : E d × ℝ) :
    dₜ (fun q ↦ -b q) p - lapₓ (fun q ↦ -b q) p + -F p = -(dₜ b p - lapₓ b p + F p) := by
  rw [dₜ_neg, lapₓ_neg]
  ring

/-- **Comparison on a bounded open set** (super form, the mirror of `domain_comparison_sub`): a
viscosity supersolution `W`, LSC on `closure Ω`, lies above a classical subsolution `b` on
`closure Ω ∩ {t < T₁}` if it does on `frontier Ω ∩ {t < T₁}`. -/
theorem domain_comparison_super (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩT : ∀ p ∈ Ω, p.2 < T₁) (hW : IsViscSuperOn Ω (fun p _ ↦ F p) W)
    (hWlsc : LowerSemicontinuousOn W (closure Ω))
    (hbc : ContinuousOn b (closure Ω)) (hb : ContDiffOn ℝ 2 b Ω)
    (hheat : ∀ p ∈ Ω, dₜ b p - lapₓ b p + F p ≤ 0)
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → b p ≤ W p) :
    ∀ p ∈ closure Ω, p.2 < T₁ → b p ≤ W p := by
  have husc : UpperSemicontinuousOn (fun q ↦ -W q) (closure Ω) :=
    upperSemicontinuousOn_iff_lowerSemicontinuousOn_neg.2 (by
      have h : (-fun q ↦ -W q) = W := by funext q; simp
      rwa [h])
  intro p hp hpT
  have := domain_comparison_sub (F := fun q ↦ -F q) (b := fun q ↦ -b q) hΩo hΩb hΩT
    hW.neg_source husc hbc.neg hb.neg
    (fun q hq ↦ by rw [heat_neg_add_neg]; linarith [hheat q hq])
    (fun q hq hqT ↦ neg_le_neg (hbdry q hq hqT)) p hp hpT
  linarith

/-- **Comparison on a bounded open set** (super form, continuous `W`): the conclusion holds on all
of `closure Ω`. -/
theorem domain_comparison_super_of_continuousOn (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩT : ∀ p ∈ Ω, p.2 < T₁)
    (hW : IsViscSuperOn Ω (fun p _ ↦ F p) W) (hWc : ContinuousOn W (closure Ω))
    (hbc : ContinuousOn b (closure Ω)) (hb : ContDiffOn ℝ 2 b Ω)
    (hheat : ∀ p ∈ Ω, dₜ b p - lapₓ b p + F p ≤ 0)
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → b p ≤ W p) :
    ∀ p ∈ closure Ω, b p ≤ W p := by
  intro p hp
  have := domain_comparison_sub_of_continuousOn (F := fun q ↦ -F q) (b := fun q ↦ -b q)
    hΩo hΩb hΩT hW.neg_source hWc.neg hbc.neg hb.neg
    (fun q hq ↦ by rw [heat_neg_add_neg]; linarith [hheat q hq])
    (fun q hq hqT ↦ neg_le_neg (hbdry q hq hqT)) p hp
  linarith

end Domain

/-! ### Cylinders -/

section Cylinder

variable {A : Set (E d)} {T₀ T₁ : ℝ}

/-- The closure of the open cylinder `A × (T₀, T₁)` is `closure A × [T₀, T₁]`. -/
theorem closure_prod_Ioo (hT : T₀ < T₁) :
    closure (A ×ˢ Ioo T₀ T₁) = closure A ×ˢ Icc T₀ T₁ := by
  rw [closure_prod_eq, closure_Ioo hT.ne]

/-- `frontier (A × (T₀, T₁)) ∩ {t < T₁} ⊆ parBdry A T₀ T₁`. -/
theorem mem_parBdry_of_mem_frontier (hT : T₀ < T₁) {p : E d × ℝ}
    (hp : p ∈ frontier (A ×ˢ Ioo T₀ T₁)) (hpT : p.2 < T₁) : p ∈ parBdry A T₀ T₁ := by
  rw [frontier_prod_eq, frontier_Ioo hT, closure_Ioo hT.ne] at hp
  rcases hp with ⟨h1, h2⟩ | h
  · rcases h2 with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd (h2 ▸ hpT : T₁ < T₁) (lt_irrefl _)
  · exact Or.inr h

theorem isBounded_prod_Ioo (hAb : Bornology.IsBounded A) :
    Bornology.IsBounded (A ×ˢ Ioo T₀ T₁) :=
  hAb.prod (Metric.isBounded_Ioo T₀ T₁)

variable {F : E d × ℝ → ℝ} {W b : E d × ℝ → ℝ}

/-- **Comparison on cylinders** (sub form). Let `A` be open and bounded and `T₀ < T₁`. A viscosity
subsolution `W` of `dₜW - lapₓW + F ≤ 0` in `A × (T₀, T₁)`, USC on `closure A × [T₀, T₁]`, lies
below a classical supersolution `b` on `closure A × [T₀, T₁)` if it does on the parabolic
boundary. -/
theorem comparison_classical_cyl_sub (hA : IsOpen A) (hAb : Bornology.IsBounded A)
    (hT : T₀ < T₁) (hW : IsViscSubOn (A ×ˢ Ioo T₀ T₁) (fun p _ ↦ F p) W)
    (hWusc : UpperSemicontinuousOn W (closure A ×ˢ Icc T₀ T₁))
    (hbc : ContinuousOn b (closure A ×ˢ Icc T₀ T₁)) (hb : ContDiffOn ℝ 2 b (A ×ˢ Ioo T₀ T₁))
    (hheat : ∀ p ∈ A ×ˢ Ioo T₀ T₁, 0 ≤ dₜ b p - lapₓ b p + F p)
    (hbdry : ∀ p ∈ parBdry A T₀ T₁, W p ≤ b p) :
    ∀ p ∈ closure A ×ˢ Icc T₀ T₁, p.2 < T₁ → W p ≤ b p := by
  rw [← closure_prod_Ioo hT] at hWusc hbc ⊢
  exact domain_comparison_sub (hA.prod isOpen_Ioo) (isBounded_prod_Ioo hAb)
    (fun p hp ↦ hp.2.2) hW hWusc hbc hb hheat
    fun p hp hpT ↦ hbdry p (mem_parBdry_of_mem_frontier hT hp hpT)

/-- **Comparison on cylinders** (sub form, continuous `W`): the conclusion holds on
`closure A × [T₀, T₁]`. -/
theorem comparison_classical_cyl_sub_of_continuousOn (hA : IsOpen A)
    (hAb : Bornology.IsBounded A) (hT : T₀ < T₁)
    (hW : IsViscSubOn (A ×ˢ Ioo T₀ T₁) (fun p _ ↦ F p) W)
    (hWc : ContinuousOn W (closure A ×ˢ Icc T₀ T₁))
    (hbc : ContinuousOn b (closure A ×ˢ Icc T₀ T₁)) (hb : ContDiffOn ℝ 2 b (A ×ˢ Ioo T₀ T₁))
    (hheat : ∀ p ∈ A ×ˢ Ioo T₀ T₁, 0 ≤ dₜ b p - lapₓ b p + F p)
    (hbdry : ∀ p ∈ parBdry A T₀ T₁, W p ≤ b p) :
    ∀ p ∈ closure A ×ˢ Icc T₀ T₁, W p ≤ b p := by
  rw [← closure_prod_Ioo hT] at hWc hbc ⊢
  exact domain_comparison_sub_of_continuousOn (hA.prod isOpen_Ioo) (isBounded_prod_Ioo hAb)
    (fun p hp ↦ hp.2.2) hW hWc hbc hb hheat
    fun p hp hpT ↦ hbdry p (mem_parBdry_of_mem_frontier hT hp hpT)

/-- **Comparison on cylinders** (super form). -/
theorem comparison_classical_cyl_super (hA : IsOpen A) (hAb : Bornology.IsBounded A)
    (hT : T₀ < T₁) (hW : IsViscSuperOn (A ×ˢ Ioo T₀ T₁) (fun p _ ↦ F p) W)
    (hWlsc : LowerSemicontinuousOn W (closure A ×ˢ Icc T₀ T₁))
    (hbc : ContinuousOn b (closure A ×ˢ Icc T₀ T₁)) (hb : ContDiffOn ℝ 2 b (A ×ˢ Ioo T₀ T₁))
    (hheat : ∀ p ∈ A ×ˢ Ioo T₀ T₁, dₜ b p - lapₓ b p + F p ≤ 0)
    (hbdry : ∀ p ∈ parBdry A T₀ T₁, b p ≤ W p) :
    ∀ p ∈ closure A ×ˢ Icc T₀ T₁, p.2 < T₁ → b p ≤ W p := by
  rw [← closure_prod_Ioo hT] at hWlsc hbc ⊢
  exact domain_comparison_super (hA.prod isOpen_Ioo) (isBounded_prod_Ioo hAb)
    (fun p hp ↦ hp.2.2) hW hWlsc hbc hb hheat
    fun p hp hpT ↦ hbdry p (mem_parBdry_of_mem_frontier hT hp hpT)

/-- **Comparison on cylinders** (super form, continuous `W`). -/
theorem comparison_classical_cyl_super_of_continuousOn (hA : IsOpen A)
    (hAb : Bornology.IsBounded A) (hT : T₀ < T₁)
    (hW : IsViscSuperOn (A ×ˢ Ioo T₀ T₁) (fun p _ ↦ F p) W)
    (hWc : ContinuousOn W (closure A ×ˢ Icc T₀ T₁))
    (hbc : ContinuousOn b (closure A ×ˢ Icc T₀ T₁)) (hb : ContDiffOn ℝ 2 b (A ×ˢ Ioo T₀ T₁))
    (hheat : ∀ p ∈ A ×ˢ Ioo T₀ T₁, dₜ b p - lapₓ b p + F p ≤ 0)
    (hbdry : ∀ p ∈ parBdry A T₀ T₁, b p ≤ W p) :
    ∀ p ∈ closure A ×ˢ Icc T₀ T₁, b p ≤ W p := by
  rw [← closure_prod_Ioo hT] at hWc hbc ⊢
  exact domain_comparison_super_of_continuousOn (hA.prod isOpen_Ioo) (isBounded_prod_Ioo hAb)
    (fun p hp ↦ hp.2.2) hW hWc hbc hb hheat
    fun p hp hpT ↦ hbdry p (mem_parBdry_of_mem_frontier hT hp hpT)

end Cylinder

end ParabolicBasic
