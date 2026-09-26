/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Iteration.Iterate
public import ParabolicBasic.Schauder.Campanato

/-!
# Interior Schauder theory for `dₜu − lapₓu = H`

This is the `L^∞` (Caffarelli / Wang / Safonov) form of the Campanato iteration:
approximation in the sup norm by caloric functions and caloric polynomials at every point and
every scale. It is **not** Campanato's `L²` integral method. Only *interior* estimates are proved.

## Main results

* `schauder_interior` (J(2)): `H` continuous and locally `α`-Hölder on `U ×ˢ I` ⇒ `IsC21On U I u`,
  `dₜ u − lapₓ u = H`, and `dₜ u`, `gradₓ u`, the spatial Hessian are locally `α`-Hölder.
* `schauder_interior'`: the same on every open box `ball x r ×ˢ Ioo a b ⊆ Ω` of an open `Ω`.
* `locHolder_of_isHeatSolOn` (J(0)): `H` continuous ⇒ `u` locally `α`-Hölder, every `α ∈ (0, 1)`.
* `gradₓ_bound_of_isHeatSolOn` (J(1)): the scaled gradient bound
  `‖gradₓ u p‖ ≤ C (S / r + M r)` on `cCyl p.1 p.2 r`.
* `continuousOn_gradₓ_of_isHeatSolOn`: `gradₓ u` exists and is continuous.

The intermediate `polyApprox_of_isHeatSolOn` produces a `PolyApprox` on every compact set, which
the pointwise Campanato-type characterization of `ParabolicBasic.Schauder.Campanato` turns into
regularity.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Gradient

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Normalization at a point -/

theorem parAffine_zero_eq (p : E d × ℝ) (r : ℝ) : parAffine p.1 p.2 r 0 = p := by
  simp [parAffine]

theorem pdist_parAffine_self (p : E d × ℝ) {r : ℝ} (hr : 0 ≤ r) (y : E d × ℝ) :
    pdist (parAffine p.1 p.2 r y) p = r * pdist y 0 := by
  have := pdist_parAffine p.1 p.2 hr y 0
  rwa [parAffine_zero_eq] at this

theorem parAffine_mem_cCylAt_one {p y : E d × ℝ} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ cCyl (0 : E d) 0 1) : parAffine p.1 p.2 r y ∈ cCylAt p r := by
  simpa using parAffine_mem_cCylAt (p := p) hr hy

/-- Normalization at `p`: `y ↦ u (S_{p,r} y) / λ` solves with source `r² H (S_{p,r} y) / λ` on
`Q₁`, if `u` solves with source `H` on the open `Ω ⊇ cCylAt p r`. -/
theorem IsHeatSolOn.normalize {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {H u : E d × ℝ → ℝ}
    (hu : IsHeatSolOn Ω H u) {p : E d × ℝ} {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hsub : cCylAt p r ⊆ Ω) :
    IsHeatSolOn (cCyl (0 : E d) 0 1) (fun y ↦ r ^ 2 * H (parAffine p.1 p.2 r y) / lam)
      (fun y ↦ u (parAffine p.1 p.2 r y) / lam) := by
  have h := isHeatSolOn_rescale hΩ hu 0 p hr hlam
  simp only [CaloricPoly.eval_zero, sub_zero, CaloricPoly.src_zero] at h
  refine h.mono (isOpen_cCyl 0 0 1) fun y hy ↦ ?_
  have h1 := hsub (parAffine_mem_cCylAt_one hr hy)
  exact h1

/-- Continuity of the normalized function on `closure Q₁`. -/
theorem continuousOn_normalize {K' : Set (E d × ℝ)} {u : E d × ℝ → ℝ} (hu : ContinuousOn u K')
    {p : E d × ℝ} {r : ℝ} (hr : 0 < r) (hsub : closure (cCylAt p r) ⊆ K') (lam : ℝ) :
    ContinuousOn (fun y ↦ u (parAffine p.1 p.2 r y) / lam) (closure (cCyl (0 : E d) 0 1)) := by
  have hmaps : MapsTo (parAffine p.1 p.2 r) (closure (cCyl (0 : E d) 0 1)) K' := by
    intro y hy
    have h1 := image_closure_subset_closure_image (continuous_parAffine p.1 p.2 r)
      (mem_image_of_mem _ hy)
    rw [image_parAffine_cCyl p.1 p.2 hr 1, mul_one] at h1
    exact hsub h1
  exact (hu.comp (continuous_parAffine p.1 p.2 r).continuousOn hmaps).div_const _

/-- Unscaling an expansion at the origin: if `|u (S_{p,r} y)/λ − P y| ≤ A pdist(y, 0)^γ` for
`pdist(y, 0) < 1`, then `|u q − P_{r⁻¹,λ⁻¹}(q − p)| ≤ λ A r^{-γ} pdist(q, p)^γ` for
`pdist(q, p) < r`. -/
theorem abs_sub_rescale_le_of_normalized {u : E d × ℝ → ℝ} {p : E d × ℝ} {r lam A γ : ℝ}
    (hr : 0 < r) (hlam : 0 < lam) {P : CaloricPoly d}
    (h : ∀ y : E d × ℝ, pdist y 0 < 1 →
      |u (parAffine p.1 p.2 r y) / lam - P.eval y| ≤ A * pdist y 0 ^ γ) :
    ∀ q, pdist q p < r →
      |u q - (P.rescale r⁻¹ lam⁻¹).eval (q - p)| ≤ lam * A / r ^ γ * pdist q p ^ γ := by
  intro q hq
  obtain ⟨y, hy⟩ : ∃ y : E d × ℝ, y = (r⁻¹ • (q - p).1, r⁻¹ ^ 2 * (q - p).2) := ⟨_, rfl⟩
  have hSy : parAffine p.1 p.2 r y = q := by
    refine Prod.ext ?_ ?_
    · change p.1 + r • y.1 = q.1
      rw [hy, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, Prod.fst_sub, add_sub_cancel]
    · change p.2 + r ^ 2 * y.2 = q.2
      rw [hy, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul, Prod.snd_sub,
        add_sub_cancel]
  have hpd : pdist q p = r * pdist y 0 := by
    rw [← pdist_parAffine_self p hr.le y, hSy]
  have hy1 : pdist y 0 < 1 := by
    rw [hpd] at hq
    exact lt_of_mul_lt_mul_left (by rwa [mul_one]) hr.le
  have hev : (P.rescale r⁻¹ lam⁻¹).eval (q - p) = lam * P.eval y := by
    rw [CaloricPoly.rescale_eval, ← hy, div_inv_eq_mul, mul_comm (P.eval y)]
  have key := h y hy1
  rw [hSy] at key
  have hne : lam ≠ 0 := hlam.ne'
  have hrγ : 0 < r ^ γ := Real.rpow_pos_of_pos hr γ
  have e : u q - lam * P.eval y = lam * (u q / lam - P.eval y) := by
    rw [mul_sub, mul_div_cancel₀ _ hne]
  rw [hev, e, abs_mul, abs_of_pos hlam, hpd, Real.mul_rpow hr.le (pdist_nonneg _ _)]
  calc lam * |u q / lam - P.eval y| ≤ lam * (A * pdist y 0 ^ γ) := by gcongr
    _ = lam * A / r ^ γ * (r ^ γ * pdist y 0 ^ γ) := by field_simp

/-! ### De-normalization -/

/-- **De-normalization.** Degrees `k ≤ 1`: polynomial approximation of order `k + α` with uniform
constants on every compact `K ⊆ Ω`, with caloric (`src = 0`) polynomials. -/
theorem polyApprox_of_isHeatSolOn {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {α : ℝ}
    (hα : 0 < α ∧ α < 1) {u H : E d × ℝ → ℝ} (hu : ContinuousOn u Ω)
    (hsol : IsHeatSolOn Ω H u) (hH : ContinuousOn H Ω) (k : ℕ) (hk : k ≤ 1)
    {K : Set (E d × ℝ)} (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox k α A ρ₀ u K P ∧ ∀ p ∈ K, (P p).src = 0 := by
  obtain ⟨r₀, hr₀, -, hK'c, hK'Ω, hcyl⟩ := exists_compact_margin hΩ hK hKΩ
  obtain ⟨Su, hSu⟩ := hK'c.exists_bound_of_continuousOn (hu.mono hK'Ω)
  obtain ⟨MH, hMH⟩ := hK'c.exists_bound_of_continuousOn (hH.mono hK'Ω)
  obtain ⟨δ₀, C₁, A, hδ₀, -, hA, hexp⟩ := expansion_at_origin (d := d) k (by omega) hα
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = max Su 0 + r₀ ^ 2 * max MH 0 / δ₀ + 1 := ⟨_, rfl⟩
  have hX : 0 ≤ r₀ ^ 2 * max MH 0 / δ₀ := by positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hSl : max Su 0 ≤ lam := by rw [hlam]; linarith
  have hMl : r₀ ^ 2 * max MH 0 ≤ lam * δ₀ := by
    rw [← div_le_iff₀ hδ₀, hlam]; linarith [le_max_right Su 0]
  have hpt : ∀ p ∈ K, ∃ Pp : CaloricPoly d, Pp.IsDegLE k ∧ Pp.src = 0 ∧ ∀ q, pdist q p < r₀ →
      |u q - Pp.eval (q - p)| ≤ lam * A / r₀ ^ ((k : ℝ) + α) * pdist q p ^ ((k : ℝ) + α) := by
    intro p hp
    have hcl := hcyl p hp
    have hsubΩ : cCylAt p r₀ ⊆ Ω := (subset_closure.trans hcl).trans hK'Ω
    have hv := hsol.normalize hΩ hr₀ hlam0 hsubΩ
    have hvc := continuousOn_normalize (hu.mono hK'Ω) hr₀ hcl lam
    have hmem : ∀ y ∈ cCyl (0 : E d) 0 1, parAffine p.1 p.2 r₀ y ∈ cthickening r₀ K :=
      fun y hy ↦ hcl (subset_closure (parAffine_mem_cCylAt_one hr₀ hy))
    have hv1 : ∀ y ∈ cCyl (0 : E d) 0 1,
        |u (parAffine p.1 p.2 r₀ y) / lam - (0 : CaloricPoly d).eval y| ≤ 1 := by
      intro y hy
      rw [CaloricPoly.eval_zero, sub_zero, abs_div, abs_of_pos hlam0, div_le_one hlam0]
      have h1 := hSu _ (hmem y hy)
      rw [Real.norm_eq_abs] at h1
      linarith [le_max_left Su 0]
    have hvH : ∀ y ∈ cCyl (0 : E d) 0 1,
        |r₀ ^ 2 * H (parAffine p.1 p.2 r₀ y) / lam - 0| ≤ δ₀ * pdist y 0 ^ (0 : ℝ) := by
      intro y hy
      rw [Real.rpow_zero, mul_one, sub_zero, abs_div, abs_mul, abs_of_pos hlam0,
        abs_of_nonneg (sq_nonneg _), div_le_iff₀ hlam0]
      have h1 := hMH _ (hmem y hy)
      rw [Real.norm_eq_abs] at h1
      have h2 : r₀ ^ 2 * |H (parAffine p.1 p.2 r₀ y)| ≤ r₀ ^ 2 * max MH 0 :=
        mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (sq_nonneg _)
      linarith
    have hθ : (k : ℝ) + α - 2 ≤ 0 := by
      have : (k : ℝ) ≤ 1 := by exact_mod_cast hk
      linarith [hα.2]
    obtain ⟨P', hdeg, hsrc, -, happ⟩ := hexp hvc hv (CaloricPoly.isDegLE_zero k)
      CaloricPoly.src_zero hv1 le_rfl hθ hvH
    refine ⟨P'.rescale r₀⁻¹ lam⁻¹, hdeg.rescale _ _, ?_,
      abs_sub_rescale_le_of_normalized hr₀ hlam0 happ⟩
    rw [CaloricPoly.src_rescale, hsrc]
    ring
  choose! P hP using hpt
  exact ⟨lam * A / r₀ ^ ((k : ℝ) + α), r₀, P, hr₀,
    ⟨fun p hp ↦ (hP p hp).1, fun p hp ↦ (hP p hp).2.2⟩, fun p hp ↦ (hP p hp).2.1⟩

/-- **De-normalization.** Degree `2`: polynomial approximation of order `2 + α` with uniform
constants on every compact `K ⊆ Ω`, with `src (P p) = H p`. -/
theorem polyApprox2_of_isHeatSolOn {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {α : ℝ}
    (hα : 0 < α ∧ α < 1) {u H : E d × ℝ → ℝ} (hu : ContinuousOn u Ω)
    (hsol : IsHeatSolOn Ω H u) (hH : ContinuousOn H Ω) (hHα : LocHolderOnPar α H Ω)
    {K : Set (E d × ℝ)} (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P ∧ ∀ p ∈ K, (P p).src = H p := by
  obtain ⟨r₀, hr₀, -, hK'c, hK'Ω, hcyl⟩ := exists_compact_margin hΩ hK hKΩ
  obtain ⟨Su, hSu⟩ := hK'c.exists_bound_of_continuousOn (hu.mono hK'Ω)
  obtain ⟨MH, hMH⟩ := hK'c.exists_bound_of_continuousOn (hH.mono hK'Ω)
  obtain ⟨CH, hCH0, hCH⟩ := hHα.exists_nonneg hK'Ω hK'c
  obtain ⟨δ₀, C₁, A, hδ₀, -, hA, hexp⟩ := expansion_at_origin (d := d) 2 le_rfl hα
  have hr₀α : 0 < r₀ ^ α := Real.rpow_pos_of_pos hr₀ α
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 2 * max Su 0 + 2 * (r₀ ^ 2 * max MH 0) +
      r₀ ^ 2 * r₀ ^ α * CH / δ₀ + 1 := ⟨_, rfl⟩
  have hX : 0 ≤ r₀ ^ 2 * r₀ ^ α * CH / δ₀ := by positivity
  have hMH0 : 0 ≤ r₀ ^ 2 * max MH 0 := by positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hSl : 2 * max Su 0 ≤ lam := by rw [hlam]; linarith
  have hMl : 2 * (r₀ ^ 2 * max MH 0) ≤ lam := by rw [hlam]; linarith [le_max_right Su 0]
  have hCl : r₀ ^ 2 * r₀ ^ α * CH ≤ lam * δ₀ := by
    rw [← div_le_iff₀ hδ₀, hlam]; linarith [le_max_right Su 0]
  have hpt : ∀ p ∈ K, ∃ Pp : CaloricPoly d, Pp.IsDegLE 2 ∧ Pp.src = H p ∧ ∀ q, pdist q p < r₀ →
      |u q - Pp.eval (q - p)| ≤ lam * A / r₀ ^ ((2 : ℕ) + α) * pdist q p ^ ((2 : ℕ) + α) := by
    intro p hp
    have hcl := hcyl p hp
    have hpK' : p ∈ cthickening r₀ K := self_subset_cthickening K hp
    have hsubΩ : cCylAt p r₀ ⊆ Ω := (subset_closure.trans hcl).trans hK'Ω
    have hv := hsol.normalize hΩ hr₀ hlam0 hsubΩ
    have hvc := continuousOn_normalize (hu.mono hK'Ω) hr₀ hcl lam
    have hmem : ∀ y ∈ cCyl (0 : E d) 0 1, parAffine p.1 p.2 r₀ y ∈ cthickening r₀ K :=
      fun y hy ↦ hcl (subset_closure (parAffine_mem_cCylAt_one hr₀ hy))
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = r₀ ^ 2 * H p / lam := ⟨_, rfl⟩
    have hσ1 : |σ| ≤ 1 / 2 := by
      have h1 := hMH _ hpK'
      rw [Real.norm_eq_abs] at h1
      rw [hσ, abs_div, abs_mul, abs_of_pos hlam0, abs_of_nonneg (sq_nonneg _),
        div_le_iff₀ hlam0]
      have h2 : r₀ ^ 2 * |H p| ≤ r₀ ^ 2 * max MH 0 :=
        mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (sq_nonneg _)
      linarith
    obtain ⟨P₀, hP₀⟩ : ∃ P₀ : CaloricPoly d, P₀ = ⟨0, 0, σ, 0, Matrix.isSymm_zero⟩ := ⟨_, rfl⟩
    have hP₀src : P₀.src = σ := by simp [hP₀, CaloricPoly.src]
    have hP₀ev : ∀ y, P₀.eval y = σ * y.2 := fun y ↦ by simp [hP₀, CaloricPoly.eval]
    have hv1 : ∀ y ∈ cCyl (0 : E d) 0 1, |u (parAffine p.1 p.2 r₀ y) / lam - P₀.eval y| ≤ 1 := by
      intro y hy
      have hy2 : |y.2| ≤ 1 := by
        have h := hy.2
        simp only [mem_Ioo, zero_sub, zero_add, one_pow] at h
        exact (abs_lt.2 h).le
      have h1 := hSu _ (hmem y hy)
      rw [Real.norm_eq_abs] at h1
      have h2 : |u (parAffine p.1 p.2 r₀ y) / lam| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hlam0, div_le_iff₀ hlam0]
        linarith [le_max_left Su 0]
      have h3 : |σ * y.2| ≤ 1 / 2 := by
        rw [abs_mul]
        calc |σ| * |y.2| ≤ 1 / 2 * 1 := mul_le_mul hσ1 hy2 (abs_nonneg _) (by norm_num)
          _ = 1 / 2 := mul_one _
      rw [hP₀ev]
      linarith [abs_sub (u (parAffine p.1 p.2 r₀ y) / lam) (σ * y.2)]
    have hvH : ∀ y ∈ cCyl (0 : E d) 0 1,
        |r₀ ^ 2 * H (parAffine p.1 p.2 r₀ y) / lam - σ| ≤ δ₀ * pdist y 0 ^ α := by
      intro y hy
      have h1 := hCH _ (hmem y hy) p hpK'
      rw [pdist_parAffine_self p hr₀.le, Real.mul_rpow hr₀.le (pdist_nonneg _ _)] at h1
      have e : r₀ ^ 2 * H (parAffine p.1 p.2 r₀ y) / lam - σ =
          r₀ ^ 2 * (H (parAffine p.1 p.2 r₀ y) - H p) / lam := by
        rw [hσ]; ring
      rw [e, abs_div, abs_mul, abs_of_pos hlam0, abs_of_nonneg (sq_nonneg _), div_le_iff₀ hlam0]
      have hs : 0 ≤ pdist y 0 ^ α := Real.rpow_nonneg (pdist_nonneg _ _) _
      calc r₀ ^ 2 * |H (parAffine p.1 p.2 r₀ y) - H p|
          ≤ r₀ ^ 2 * (CH * (r₀ ^ α * pdist y 0 ^ α)) := by gcongr
        _ = (r₀ ^ 2 * r₀ ^ α * CH) * pdist y 0 ^ α := by ring
        _ ≤ (lam * δ₀) * pdist y 0 ^ α := by gcongr
        _ = δ₀ * pdist y 0 ^ α * lam := by ring
    obtain ⟨P', -, hsrc, -, happ⟩ := hexp hvc hv trivial hP₀src hv1 hα.1.le
      (by push_cast; linarith) hvH
    refine ⟨P'.rescale r₀⁻¹ lam⁻¹, trivial, ?_,
      abs_sub_rescale_le_of_normalized hr₀ hlam0 happ⟩
    rw [CaloricPoly.src_rescale, hsrc, hσ]
    field_simp
  choose! P hP using hpt
  exact ⟨lam * A / r₀ ^ ((2 : ℕ) + α), r₀, P, hr₀,
    ⟨fun p hp ↦ (hP p hp).1, fun p hp ↦ (hP p hp).2.2⟩, fun p hp ↦ (hP p hp).2.1⟩

/-! ### Main theorems -/

/-- **J(2): interior Schauder estimate.** Let `U ⊆ E d`, `I ⊆ ℝ` be open, `α ∈ (0, 1)`, `u`
continuous on `U ×ˢ I` and a viscosity solution of `dₜu − lapₓu = H` there, with `H` continuous and
locally parabolically `α`-Hölder. Then `u ∈ C^{2,1}` (`IsC21On`), the equation holds pointwise, and
`dₜ u`, every coordinate of `gradₓ u` and every spatial Hessian entry are locally parabolically
`α`-Hölder. -/
theorem schauder_interior {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {u H : E d × ℝ → ℝ}
    (hu : ContinuousOn u (U ×ˢ I)) (hsol : IsHeatSolOn (U ×ˢ I) H u)
    (hH : ContinuousOn H (U ×ˢ I)) (hHα : LocHolderOnPar α H (U ×ˢ I)) :
    IsC21On U I u ∧ (∀ p ∈ U ×ˢ I, dₜ u p - lapₓ u p = H p) ∧
      LocHolderOnPar α (dₜ u) (U ×ˢ I) ∧
      (∀ i, LocHolderOnPar α (fun p ↦ gradₓ u p i) (U ×ˢ I)) ∧
      ∀ i j, LocHolderOnPar α (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (U ×ˢ I) := by
  have h2 : ∀ K ⊆ U ×ˢ I, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P ∧
      ∀ p ∈ K, (P p).src = H p := fun K hK hKc ↦
    polyApprox2_of_isHeatSolOn (hU.prod hI) hα hu hsol hH hHα hK hKc
  have h2' : ∀ K ⊆ U ×ˢ I, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P :=
    fun K hK hKc ↦ by
      obtain ⟨A, ρ₀, P, hρ, hP, -⟩ := h2 K hK hKc
      exact ⟨A, ρ₀, P, hρ, hP⟩
  obtain ⟨hC21, -, hdt, hgrad, hhess⟩ := isC21On_of_polyApprox hU hI hα h2'
  exact ⟨hC21, heat_eq_of_polyApprox hU hI hα h2, hdt, hgrad, hhess⟩

/-- `schauder_interior` on an arbitrary open `Ω`: the conclusions hold on every open box
`ball x r ×ˢ Ioo a b ⊆ Ω`. -/
theorem schauder_interior' {Ω : Set (E d × ℝ)} (_hΩ : IsOpen Ω) {α : ℝ} (hα : 0 < α ∧ α < 1)
    {u H : E d × ℝ → ℝ} (hu : ContinuousOn u Ω) (hsol : IsHeatSolOn Ω H u)
    (hH : ContinuousOn H Ω) (hHα : LocHolderOnPar α H Ω) :
    ∀ (x : E d) (r a b : ℝ), ball x r ×ˢ Ioo a b ⊆ Ω →
      IsC21On (ball x r) (Ioo a b) u ∧
      (∀ p ∈ ball x r ×ˢ Ioo a b, dₜ u p - lapₓ u p = H p) ∧
      LocHolderOnPar α (dₜ u) (ball x r ×ˢ Ioo a b) ∧
      (∀ i, LocHolderOnPar α (fun p ↦ gradₓ u p i) (ball x r ×ˢ Ioo a b)) ∧
      ∀ i j, LocHolderOnPar α (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (ball x r ×ˢ Ioo a b) := by
  intro x r a b hbox
  have hO : IsOpen (ball x r ×ˢ Ioo a b) := isOpen_ball.prod isOpen_Ioo
  exact schauder_interior isOpen_ball isOpen_Ioo hα (hu.mono hbox) (hsol.mono hO hbox)
    (hH.mono hbox) (hHα.mono hbox)

/-- **J(0).** A continuous viscosity solution of `dₜu − lapₓu = H` with `H` continuous on the open
`Ω` is locally parabolically `α`-Hölder for every `α ∈ (0, 1)`. -/
theorem locHolder_of_isHeatSolOn {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {u H : E d × ℝ → ℝ}
    (hu : ContinuousOn u Ω) (hsol : IsHeatSolOn Ω H u) (hH : ContinuousOn H Ω)
    {α : ℝ} (hα : 0 < α ∧ α < 1) : LocHolderOnPar α u Ω := by
  refine (holderOnPar_of_polyApprox0 hΩ hα fun K hKΩ hK ↦ ?_).2
  obtain ⟨A, ρ₀, P, hρ, hP, -⟩ := polyApprox_of_isHeatSolOn hΩ hα hu hsol hH 0 zero_le_one hKΩ hK
  exact ⟨A, ρ₀, P, hρ, hP⟩

/-- **J(1): the scaled interior gradient bound.** There is `C > 0` depending only on `d` such that
for a continuous viscosity solution of `dₜu − lapₓu = H` on `cCyl p.1 p.2 r` (continuous on its
closure) with `|u| ≤ S` and `|H| ≤ M` there, the spatial slice of `u` has a gradient at `p` and
`‖gradₓ u p‖ ≤ C (S / r + M r)`. -/
theorem gradₓ_bound_of_isHeatSolOn :
    ∃ C : ℝ, 0 < C ∧ ∀ {p : E d × ℝ} {r S M : ℝ} {u H : E d × ℝ → ℝ}, 0 < r →
      ContinuousOn u (closure (cCyl p.1 p.2 r)) → IsHeatSolOn (cCyl p.1 p.2 r) H u →
      (∀ q ∈ cCyl p.1 p.2 r, |u q| ≤ S) → (∀ q ∈ cCyl p.1 p.2 r, |H q| ≤ M) →
      HasGradientAt (fun y ↦ u (y, p.2)) (gradₓ u p) p.1 ∧ ‖gradₓ u p‖ ≤ C * (S / r + M * r) := by
  obtain ⟨δ₀, C₁, A, hδ₀, hC₁, hA, hexp⟩ :=
    expansion_at_origin (d := d) 1 (by norm_num) (α := 1 / 2) (by norm_num)
  refine ⟨C₁ * max 1 δ₀⁻¹ + 1, by positivity, fun {p r S M u H} hr hu hsol hS hM ↦ ?_⟩
  have hpmem : p ∈ cCyl p.1 p.2 r := center_mem_cCyl p.1 p.2 hr
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS p hpmem)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM p hpmem)
  have hX : 0 ≤ r ^ 2 * M / δ₀ := by positivity
  -- the expansion at `p`, normalized by `λ = S + r² M / δ₀ + η`
  have key : ∀ η : ℝ, 0 < η → HasGradientAt (fun y ↦ u (y, p.2)) (gradₓ u p) p.1 ∧
      ‖gradₓ u p‖ ≤ C₁ * ((S + r ^ 2 * M / δ₀ + η) / r) := by
    intro η hη
    obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = S + r ^ 2 * M / δ₀ + η := ⟨_, rfl⟩
    have hlam0 : 0 < lam := by rw [hlam]; positivity
    have hSl : S ≤ lam := by rw [hlam]; linarith
    have hMl : r ^ 2 * M ≤ lam * δ₀ := by
      rw [← div_le_iff₀ hδ₀, hlam]; linarith
    have hv := hsol.normalize (isOpen_cCyl p.1 p.2 r) hr hlam0 subset_rfl
    have hvc := continuousOn_normalize hu hr subset_rfl lam
    have hv1 : ∀ y ∈ cCyl (0 : E d) 0 1,
        |u (parAffine p.1 p.2 r y) / lam - (0 : CaloricPoly d).eval y| ≤ 1 := by
      intro y hy
      rw [CaloricPoly.eval_zero, sub_zero, abs_div, abs_of_pos hlam0, div_le_one hlam0]
      exact (hS _ (parAffine_mem_cCylAt_one hr hy)).trans hSl
    have hvH : ∀ y ∈ cCyl (0 : E d) 0 1,
        |r ^ 2 * H (parAffine p.1 p.2 r y) / lam - 0| ≤ δ₀ * pdist y 0 ^ (0 : ℝ) := by
      intro y hy
      rw [Real.rpow_zero, mul_one, sub_zero, abs_div, abs_mul, abs_of_pos hlam0,
        abs_of_nonneg (sq_nonneg _), div_le_iff₀ hlam0]
      have h2 : r ^ 2 * |H (parAffine p.1 p.2 r y)| ≤ r ^ 2 * M :=
        mul_le_mul_of_nonneg_left (hM _ (parAffine_mem_cCylAt_one hr hy)) (sq_nonneg _)
      linarith
    obtain ⟨P', hdeg, -, hcn, happ⟩ := hexp hvc hv (CaloricPoly.isDegLE_zero 1)
      CaloricPoly.src_zero hv1 le_rfl (by norm_num) hvH
    have hPA : PolyApprox 1 (1 / 2) _ r u {p} (fun _ ↦ P'.rescale r⁻¹ lam⁻¹) :=
      ⟨fun _ _ ↦ hdeg.rescale _ _, fun p' hp' q hq ↦ by
        rw [mem_singleton_iff] at hp'
        subst hp'
        exact abs_sub_rescale_le_of_normalized hr hlam0 happ q hq⟩
    obtain ⟨hgrad, hb⟩ := gradₓ_eq_of_polyApprox1 (by norm_num) hr hPA (mem_singleton p)
    refine ⟨hgrad, ?_⟩
    have hbn : ‖P'.b‖ ≤ C₁ := by
      have := P'.norm_b_le_coeffNorm
      have h0 : (0 : CaloricPoly d).coeffNorm = 0 := by simp [CaloricPoly.coeffNorm]
      linarith
    rw [hb, CaloricPoly.rescale_b, norm_smul, inv_div_inv, Real.norm_eq_abs,
      abs_of_pos (div_pos hlam0 hr), ← hlam]
    calc lam / r * ‖P'.b‖ ≤ lam / r * C₁ := by gcongr
      _ = C₁ * (lam / r) := by ring
  refine ⟨(key 1 one_pos).1, ?_⟩
  -- let `η → 0`
  have hc : Continuous (fun η : ℝ ↦ C₁ * ((S + r ^ 2 * M / δ₀ + η) / r)) := by fun_prop
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hle : ‖gradₓ u p‖ ≤ C₁ * ((S + r ^ 2 * M / δ₀ + 0) / r) :=
    ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun η hη ↦ (key η hη).2)
  have e : (S + r ^ 2 * M / δ₀ + 0) / r = S / r + δ₀⁻¹ * (M * r) := by
    rw [add_zero]
    field_simp
  rw [e] at hle
  have hm1 : 1 ≤ max 1 δ₀⁻¹ := le_max_left _ _
  have hm2 : δ₀⁻¹ ≤ max 1 δ₀⁻¹ := le_max_right _ _
  have hSr : 0 ≤ S / r := div_nonneg hS0 hr.le
  have hMr : 0 ≤ M * r := mul_nonneg hM0 hr.le
  have h1 : S / r + δ₀⁻¹ * (M * r) ≤ max 1 δ₀⁻¹ * (S / r + M * r) := by
    rw [mul_add]
    exact add_le_add (le_mul_of_one_le_left hSr hm1) (mul_le_mul_of_nonneg_right hm2 hMr)
  calc ‖gradₓ u p‖ ≤ C₁ * (S / r + δ₀⁻¹ * (M * r)) := hle
    _ ≤ C₁ * (max 1 δ₀⁻¹ * (S / r + M * r)) := by gcongr
    _ ≤ (C₁ * max 1 δ₀⁻¹ + 1) * (S / r + M * r) := by
      rw [← mul_assoc, add_mul, one_mul]
      linarith

/-- **J(1), continuity part.** For a continuous viscosity solution of `dₜu − lapₓu = H` with `H`
continuous on the open `Ω`, the spatial gradient exists at every point and `gradₓ u` is continuous
on `Ω`. -/
theorem continuousOn_gradₓ_of_isHeatSolOn {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {u H : E d × ℝ → ℝ} (hu : ContinuousOn u Ω) (hsol : IsHeatSolOn Ω H u)
    (hH : ContinuousOn H Ω) :
    (∀ p ∈ Ω, HasGradientAt (fun y ↦ u (y, p.2)) (gradₓ u p) p.1) ∧
      ContinuousOn (gradₓ u) Ω := by
  have hα : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by norm_num
  have h := continuousOn_gradₓ_of_polyApprox1 hΩ hα fun K hKΩ hK ↦ by
    obtain ⟨A, ρ₀, P, hρ, hP, -⟩ := polyApprox_of_isHeatSolOn hΩ hα hu hsol hH 1 le_rfl hKΩ hK
    exact ⟨A, ρ₀, P, hρ, hP⟩
  exact ⟨h.2.1, h.2.2.1⟩

end ParabolicBasic
