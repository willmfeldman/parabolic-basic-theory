/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Poly
public import ParabolicBasic.Viscosity.Invariance
public import ParabolicBasic.Comparison.Parabolic

/-!
# The Schauder iteration: normalization toolkit and cylinder geometry

`IsHeatSolOn Ω H u` (`dₜu − lapₓu = H` in the viscosity sense) is defined in
`ParabolicBasic.Defs.Viscosity`.

* `isHeatSolOn_rescale`: if `u` solves with source `H` on the open `Ω` and `P` is a
  caloric polynomial, then `w y = (u (S y) - P (S y - p)) / λ` with `S = parAffine p.1 p.2 r`
  solves with source `r² (H (S y) - src P) / λ` on `S ⁻¹' Ω`. This is the only normalization
  lemma the iteration uses.
* `frontier_cCyl_subset`, `closure_cCylAt_subset_closedBall`, `exists_compact_margin`: the
  geometry of centred cylinders.

All statements hold for every `d`, including `d = 0`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Basic properties of `IsHeatSolOn` -/

/-- Restriction of a heat solution to an open subset. -/
theorem IsHeatSolOn.mono {Ω Ω' : Set (E d × ℝ)} {H u : E d × ℝ → ℝ} (hΩ' : IsOpen Ω')
    (h : Ω' ⊆ Ω) (hu : IsHeatSolOn Ω H u) : IsHeatSolOn Ω' H u :=
  ⟨hu.1.mono_set hΩ' h, hu.2.mono_set hΩ' h⟩

/-! ### Caloric polynomials along parabolic affine maps -/

namespace CaloricPoly

theorem src_neg (P : CaloricPoly d) : (-P).src = -P.src := by
  simp only [src, neg_c, neg_M, Matrix.trace_neg]
  ring

/-- `P (S_{p,r} y - p) = P_{r,1} (y)`. -/
theorem eval_parAffine_sub (P : CaloricPoly d) (p : E d × ℝ) (r : ℝ) (y : E d × ℝ) :
    P.eval (parAffine p.1 p.2 r y - p) = (P.rescale r 1).eval y := by
  rw [rescale_eval, div_one]
  congr 1
  ext <;> simp [parAffine]

end CaloricPoly

/-! ### The normalization toolkit -/

/-- **Rescaling.** Subtracting a caloric polynomial, translating and parabolically rescaling, and
dividing by `λ > 0`: `w y = (u (S y) - P (S y - p)) / λ`, `S = parAffine p.1 p.2 r`, solves
`dₜ w - lapₓ w = r² (H (S y) - src P) / λ` on `S ⁻¹' Ω`. -/
theorem isHeatSolOn_rescale {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {H u : E d × ℝ → ℝ}
    (hu : IsHeatSolOn Ω H u) (P : CaloricPoly d) (p : E d × ℝ) {r lam : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) :
    IsHeatSolOn (parAffine p.1 p.2 r ⁻¹' Ω)
      (fun y ↦ r ^ 2 * (H (parAffine p.1 p.2 r y) - P.src) / lam)
      (fun y ↦ (u (parAffine p.1 p.2 r y) - P.eval (parAffine p.1 p.2 r y - p)) / lam) := by
  set Q : CaloricPoly d := -(P.recenter (-p)) with hQ
  have hQe : ∀ q, Q.eval q = -P.eval (q - p) := fun q ↦ by
    simp [hQ, CaloricPoly.recenter_eval, sub_eq_add_neg]
  have hQs : Q.src = -P.src := by simp [hQ, CaloricPoly.src_neg]
  have hφ : ContDiffOn ℝ 2 Q.eval Ω :=
    (Q.contDiff_eval.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn
  have hilam : 0 < lam⁻¹ := inv_pos.2 hlam
  have hfun : (fun y ↦ (u (parAffine p.1 p.2 r y) - P.eval (parAffine p.1 p.2 r y - p)) / lam) =
      fun y ↦ lam⁻¹ * ((fun q ↦ u q + Q.eval q) ∘ parAffine p.1 p.2 r) y := by
    funext y
    simp only [Function.comp_apply, hQe]
    rw [div_eq_inv_mul]
    ring
  rw [hfun]
  refine ⟨?_, ?_⟩
  · have h1 := ((hu.1.add_contDiff hΩ hφ).comp_parAffine (x₀ := p.1) (t₀ := p.2) hr).const_smul
      hilam
    refine h1.mono_source fun q _ z ↦ le_of_eq ?_
    simp only [CaloricPoly.dₜ_sub_lapₓ_eval, hQs]
    field_simp
    ring
  · have h1 := ((hu.2.add_contDiff hΩ hφ).comp_parAffine (x₀ := p.1) (t₀ := p.2) hr).const_smul
      hilam
    refine h1.mono_source fun q _ z ↦ le_of_eq ?_
    simp only [CaloricPoly.dₜ_sub_lapₓ_eval, hQs]
    field_simp
    ring

/-! ### Geometry of centred cylinders -/

theorem isOpen_cCyl (x : E d) (t r : ℝ) : IsOpen (cCyl x t r) :=
  isOpen_ball.prod isOpen_Ioo

theorem center_mem_cCyl (x : E d) (t : ℝ) {r : ℝ} (hr : 0 < r) : (x, t) ∈ cCyl x t r := by
  have : 0 < r ^ 2 := by positivity
  exact ⟨mem_ball_self hr, by simp only [mem_Ioo]; constructor <;> linarith⟩

/-- The frontier of a centred cylinder below its top face lies on the parabolic boundary. (The
closure is `closure_cCyl`.) -/
theorem frontier_cCyl_subset (x : E d) (t r : ℝ) :
    frontier (cCyl x t r) ∩ {q | q.2 < t + r ^ 2} ⊆
      parBdry (ball x r) (t - r ^ 2) (t + r ^ 2) := by
  rintro q ⟨hq, hqt⟩
  rcases frontier_prod_Ioo_subset (ball x r) (t - r ^ 2) (t + r ^ 2) hq with h | ⟨-, h⟩
  · exact h
  · exact absurd (mem_singleton_iff.1 h ▸ hqt : t + r ^ 2 < t + r ^ 2) (lt_irrefl _)

/-- For `0 < r ≤ 1` the closed centred cylinder lies in the closed ball of the sup metric. -/
theorem closure_cCylAt_subset_closedBall (p : E d × ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    closure (cCylAt p r) ⊆ closedBall p r := by
  have hcl : closure (cCylAt p r) = closedBall p.1 r ×ˢ Icc (p.2 - r ^ 2) (p.2 + r ^ 2) := by
    rw [cCylAt, cCyl, closure_prod_Ioo_eq _ (by nlinarith [pow_pos hr 2]), closure_ball _ hr.ne']
  rw [hcl]
  rintro q ⟨hq1, hq2⟩
  have hr2 : r ^ 2 ≤ r := by nlinarith
  rw [mem_closedBall, Prod.dist_eq]
  refine max_le hq1 ?_
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hq2.1, hq2.2]

/-- Compact margin: for `K ⊆ Ω` compact and `Ω` open there is `r₀ ∈ (0, 1]` such that
`K' := cthickening r₀ K` is compact, `K' ⊆ Ω`, and `closure (cCylAt p r₀) ⊆ K'` for every `p ∈ K`.
-/
theorem exists_compact_margin {Ω K : Set (E d × ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ IsCompact (cthickening r₀ K) ∧ cthickening r₀ K ⊆ Ω ∧
      ∀ p ∈ K, closure (cCylAt p r₀) ⊆ cthickening r₀ K := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, hK.cthickening,
    (cthickening_mono (min_le_left _ _) K).trans hδΩ, fun p hp ↦ ?_⟩
  exact (closure_cCylAt_subset_closedBall p (lt_min hδ one_pos) (min_le_right _ _)).trans
    (closedBall_subset_cthickening hp _)

/-- `parAffine p.1 p.2 r` maps `cCyl 0 0 ρ` into `cCylAt p (r ρ)`. -/
theorem parAffine_mem_cCylAt {p : E d × ℝ} {r ρ : ℝ} (hr : 0 < r) {y : E d × ℝ}
    (hy : y ∈ cCyl 0 0 ρ) : parAffine p.1 p.2 r y ∈ cCylAt p (r * ρ) := by
  rw [cCylAt, ← image_parAffine_cCyl p.1 p.2 hr]
  exact mem_image_of_mem _ hy

end ParabolicBasic
