/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.PolyExtract
public import ParabolicBasic.Defs.Classical

/-!
# The pointwise (sup-norm) Campanato-type characterization

This is the elementary *pointwise sup-norm* characterization of parabolic Hölder classes
by polynomial approximation at every point and every scale, as in Caffarelli–Cabré, L. Wang and
Safonov (the `L^∞` form of the Campanato iteration). It is **not** Campanato's integral
(`L²`) characterization `𝓛^{2,λ} ≅ C^α`.

`PolyApprox k α A ρ₀ u K P`: for every `p ∈ K`, `P p` has degree `≤ k` and
`|u q - (P p).eval (q - p)| ≤ A pdist(q, p)^{k+α}` whenever `pdist q p < ρ₀`.

* (k = 0) `holderOnPar_of_polyApprox0`: `u` continuous and `LocHolderOnPar α u Ω`.
* (k = 1) `continuousOn_gradₓ_of_polyApprox1`: the slice gradient exists, `gradₓ u` is continuous
  and each coordinate is `LocHolderOnPar α`; `gradₓ_eq_of_polyApprox1`: `gradₓ u p = (P p).b`.
* (k = 2) `isC21On_of_polyApprox`: `IsC21On U I u`, identification of all coefficients, and
  `LocHolderOnPar α` of `dₜ u`, of the coordinates of `gradₓ u` and of the Hessian entries;
  `heat_eq_of_polyApprox`: `dₜ u - lapₓ u = H` when `src (P p) = H p`.
-/

@[expose] public section

open Set Filter Topology Asymptotics
open scoped ContDiff Gradient RealInnerProductSpace

namespace ParabolicBasic

variable {d : ℕ}

/-- **Polynomial approximation of order `k + α` on a set**: for every `p ∈ S`, `P p` has parabolic
degree `≤ k`, and `|u q - (P p).eval (q - p)| ≤ A pdist(q, p)^{k+α}` for all `q` with
`pdist q p < ρ₀`. -/
structure PolyApprox (k : ℕ) (α A ρ₀ : ℝ) (u : E d × ℝ → ℝ) (S : Set (E d × ℝ))
    (P : E d × ℝ → CaloricPoly d) : Prop where
  deg : ∀ p ∈ S, (P p).IsDegLE k
  approx : ∀ p ∈ S, ∀ q, pdist q p < ρ₀ →
    |u q - (P p).eval (q - p)| ≤ A * pdist q p ^ ((k : ℝ) + α)

namespace PolyApprox

variable {k : ℕ} {α A ρ₀ : ℝ} {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)}
  {P : E d × ℝ → CaloricPoly d}

theorem mono (h : PolyApprox k α A ρ₀ u S P) {T : Set (E d × ℝ)} (hTS : T ⊆ S) :
    PolyApprox k α A ρ₀ u T P :=
  ⟨fun p hp ↦ h.deg p (hTS hp), fun p hp ↦ h.approx p (hTS hp)⟩

/-- The constant may be taken nonnegative. -/
theorem max_zero (h : PolyApprox k α A ρ₀ u S P) : PolyApprox k α (max A 0) ρ₀ u S P :=
  ⟨h.deg, fun p hp q hq ↦ (h.approx p hp q hq).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (pdist_nonneg _ _) _))⟩

/-- The constant term is the value: `(P p).a = u p`. -/
theorem a_eq (h : PolyApprox k α A ρ₀ u S P) (hα : 0 < α) (hρ : 0 < ρ₀) {p : E d × ℝ}
    (hp : p ∈ S) : (P p).a = u p := by
  have hγ : (0 : ℝ) < (k : ℝ) + α := by positivity
  have h0 := h.approx p hp p (by rw [pdist_self]; exact hρ)
  rw [sub_self, pdist_self, Real.zero_rpow hγ.ne', mul_zero, CaloricPoly.eval_zero_point] at h0
  exact (sub_eq_zero.1 (abs_nonpos_iff.1 h0)).symm

/-- **Consistency**: two approximating fields agree at common points (`k ≤ 2`, `α > 0`). -/
theorem eq_of_polyApprox (h : PolyApprox k α A ρ₀ u S P) {A' ρ₀' : ℝ} {S' : Set (E d × ℝ)}
    {P' : E d × ℝ → CaloricPoly d} (h' : PolyApprox k α A' ρ₀' u S' P') (hk : k ≤ 2)
    (hα : 0 < α) (hρ : 0 < ρ₀) (hρ' : 0 < ρ₀') {p : E d × ℝ} (hp : p ∈ S) (hp' : p ∈ S') :
    P p = P' p := by
  have hd := (h.deg p hp).sub (h'.deg p hp')
  suffices h0 : P p - P' p = 0 by
    have ha := congrArg CaloricPoly.a h0
    have hb := congrArg CaloricPoly.b h0
    have hc := congrArg CaloricPoly.c h0
    have hM := congrArg CaloricPoly.M h0
    simp only [CaloricPoly.sub_a, CaloricPoly.sub_b, CaloricPoly.sub_c, CaloricPoly.sub_M,
      CaloricPoly.zero_a, CaloricPoly.zero_b, CaloricPoly.zero_c, CaloricPoly.zero_M,
      sub_eq_zero] at ha hb hc hM
    exact CaloricPoly.ext ha hb hc hM
  refine CaloricPoly.eq_zero_of_abs_eval_le (A := A + A') hd hk hα (lt_min hρ hρ') fun q hq ↦ ?_
  have hq' : pdist (q + p) p = pdist q 0 := by rw [← pdist_add_right q 0 p, zero_add]
  have e1 := h.approx p hp (q + p) (by rw [hq']; exact hq.trans_le (min_le_left _ _))
  have e2 := h'.approx p hp' (q + p) (by rw [hq']; exact hq.trans_le (min_le_right _ _))
  rw [add_sub_cancel_right, hq'] at e1 e2
  rw [CaloricPoly.eval_sub]
  calc |(P p).eval q - (P' p).eval q|
      ≤ |u (q + p) - (P p).eval q| + |u (q + p) - (P' p).eval q| := by
        have := abs_sub_le ((P p).eval q) (u (q + p)) ((P' p).eval q)
        rwa [abs_sub_comm ((P p).eval q) (u (q + p))] at this
    _ ≤ _ := (add_le_add e1 e2).trans_eq (by ring)

/-- An order-`k+α` approximation on a compact set gives continuity of `u` at points of `S`
within the neighbourhood `pdist < ρ₀` (hence continuity on open sets). -/
theorem continuousAt (h : PolyApprox k α A ρ₀ u S P) (hα : 0 < α) (hρ : 0 < ρ₀) {p : E d × ℝ}
    (hp : p ∈ S) : ContinuousAt u p := by
  have hγ : (0 : ℝ) < (k : ℝ) + α := by positivity
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hcont : Continuous fun q ↦
      A * pdist q p ^ ((k : ℝ) + α) + |(P p).eval (q - p) - (P p).eval 0| :=
    (continuous_const.mul (Continuous.rpow_const (continuous_pdist_left p)
      fun _ ↦ Or.inr hγ.le)).add
      ((((P p).continuous_eval.comp (continuous_id.sub continuous_const)).sub
        continuous_const).abs)
  have hlim : Tendsto (fun q ↦
      A * pdist q p ^ ((k : ℝ) + α) + |(P p).eval (q - p) - (P p).eval 0|) (𝓝 p) (𝓝 0) := by
    simpa [Real.zero_rpow hγ.ne'] using hcont.tendsto p
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  have hev : ∀ᶠ q in 𝓝 p, pdist q p < ρ₀ :=
    ((continuous_pdist_left p).tendsto p).eventually (gt_mem_nhds (by rw [pdist_self]; exact hρ))
  filter_upwards [hev] with q hq
  rw [Real.norm_eq_abs, CaloricPoly.eval_zero_point, h.a_eq hα hρ hp]
  have e := h.approx p hp q hq
  calc |u q - u p| ≤ |u q - (P p).eval (q - p)| + |(P p).eval (q - p) - u p| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- (k = 0, compact form) With `|u| ≤ B` on `S`, `u` is `α`-Hölder on `S` with constant
`max A (2 B ρ₀^{-α})`. -/
theorem holderOnPar0 (h : PolyApprox 0 α A ρ₀ u S P) (hα : 0 < α) (hρ : 0 < ρ₀) {B : ℝ}
    (hB : ∀ p ∈ S, |u p| ≤ B) : HolderOnPar (max A (2 * B * ρ₀ ^ (-α))) α u S := by
  have hk : ∀ p ∈ S, ∀ q, (P p).eval (q - p) = u p := fun p hp q ↦ by
    obtain ⟨hb, hc, hM⟩ := h.deg p hp
    rw [← h.a_eq hα hρ hp]
    simp [CaloricPoly.eval, hb, hc, hM]
  refine HolderOnPar.of_near_far hρ hα.le hB fun p hp q hq _ hpq ↦ ?_
  have e := h.approx q hq p hpq
  rw [hk q hq p] at e
  simpa using e

/-- (k ≥ 1) The slice `u(·, p.2)` has gradient `(P p).b` at `p.1`. -/
theorem hasGradientAt (h : PolyApprox k α A ρ₀ u S P) (hk : 1 ≤ k) (hα : 0 < α) (hρ : 0 < ρ₀)
    {p : E d × ℝ} (hp : p ∈ S) : HasGradientAt (fun y ↦ u (y, p.2)) (P p).b p.1 := by
  have ha := h.a_eq hα hρ hp
  have hβ : 0 < min α 1 := lt_min hα one_pos
  refine hasGradientAt_of_expansion1 (A := max A 0 + 1 / 2 * ‖CaloricPoly.bilin (P p).M‖)
    (lt_min hρ one_pos) hβ fun v hv ↦ ?_
  have hv1 : ‖v‖ < ρ₀ := hv.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ ≤ 1 := (hv.trans_le (min_le_right _ _)).le
  have hpd : pdist (p.1 + v, p.2) p = ‖v‖ := by simp [pdist]
  have e := h.approx p hp (p.1 + v, p.2) (by rw [hpd]; exact hv1)
  have hsub : (p.1 + v, p.2) - p = (v, 0) := by ext <;> simp
  rw [hsub, hpd, CaloricPoly.eval_eq_bilin] at e
  simp only [mul_zero, add_zero] at e
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow1 : ‖v‖ ^ ((k : ℝ) + α) ≤ ‖v‖ ^ (1 + min α 1) :=
    Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hv2 (by positivity)
      (by linarith [min_le_left α 1])
  have hpow2 : ‖v‖ ^ 2 ≤ ‖v‖ ^ (1 + min α 1) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hv2 (by positivity)
      (by linarith [min_le_right α 1])
  have hB : |1 / 2 * CaloricPoly.bilin (P p).M v v| ≤
      1 / 2 * ‖CaloricPoly.bilin (P p).M‖ * ‖v‖ ^ (1 + min α 1) := by
    have := (CaloricPoly.bilin (P p).M).le_opNorm₂ v v
    rw [Real.norm_eq_abs] at this
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
    gcongr
    calc |CaloricPoly.bilin (P p).M v v| ≤ ‖CaloricPoly.bilin (P p).M‖ * ‖v‖ * ‖v‖ := this
      _ = ‖CaloricPoly.bilin (P p).M‖ * ‖v‖ ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hA : A * ‖v‖ ^ ((k : ℝ) + α) ≤ max A 0 * ‖v‖ ^ (1 + min α 1) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)).trans
      (mul_le_mul_of_nonneg_left hpow1 (le_max_right _ _))
  change |u (p.1 + v, p.2) - u (p.1, p.2) - ⟪(P p).b, v⟫| ≤ _
  rw [Prod.mk.eta, ← ha]
  calc |u (p.1 + v, p.2) - (P p).a - ⟪(P p).b, v⟫|
      = |(u (p.1 + v, p.2) - ((P p).a + ⟪(P p).b, v⟫ + 1 / 2 * CaloricPoly.bilin (P p).M v v)) +
          1 / 2 * CaloricPoly.bilin (P p).M v v| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add (e.trans hA) hB
    _ = _ := by ring

/-- (k ≥ 2) The time slice `u(p.1, ·)` has (two-sided) derivative `(P p).c` at `p.2`. -/
theorem hasDerivAt_time (h : PolyApprox k α A ρ₀ u S P) (hk : 2 ≤ k) (hα : 0 < α)
    (hρ : 0 < ρ₀) {p : E d × ℝ} (hp : p ∈ S) : HasDerivAt (fun s ↦ u (p.1, s)) (P p).c p.2 := by
  have ha := h.a_eq hα hρ hp
  refine hasDerivAt_of_expansion1 (A := max A 0) (β := α / 2) (lt_min (pow_pos hρ 2) one_pos)
    (by positivity) fun s hs ↦ ?_
  have hs1 : |s| < ρ₀ ^ 2 := hs.trans_le (min_le_left _ _)
  have hs2 : |s| ≤ 1 := (hs.trans_le (min_le_right _ _)).le
  have hpd : pdist (p.1, p.2 + s) p = Real.sqrt |s| := by simp [pdist]
  have hpdl : Real.sqrt |s| < ρ₀ := by rw [Real.sqrt_lt' hρ]; exact hs1
  have e := h.approx p hp (p.1, p.2 + s) (by rw [hpd]; exact hpdl)
  have hsub : (p.1, p.2 + s) - p = (0, s) := by ext <;> simp
  have hev : (P p).eval (0, s) = (P p).a + (P p).c * s := by simp [CaloricPoly.eval]
  rw [hsub, hpd, hev, ha] at e
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : Real.sqrt |s| ^ ((k : ℝ) + α) ≤ |s| ^ (1 + α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg s)]
    exact Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg s) hs2 (by positivity) (by nlinarith)
  have hA : A * Real.sqrt |s| ^ ((k : ℝ) + α) ≤ max A 0 * |s| ^ (1 + α / 2) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)).trans
      (mul_le_mul_of_nonneg_left hpow (le_max_right _ _))
  change |u (p.1, p.2 + s) - u (p.1, p.2) - (P p).c * s| ≤ _
  rw [Prod.mk.eta]
  calc |u (p.1, p.2 + s) - u p - (P p).c * s| = |u (p.1, p.2 + s) - (u p + (P p).c * s)| := by
        ring_nf
    _ ≤ _ := e.trans hA

end PolyApprox

/-- Continuity from polynomial approximation on every compact subset of an open set (any `k`). -/
theorem continuousOn_of_polyApprox {Ω : Set (E d × ℝ)} {k : ℕ} {α : ℝ}
    (hα : 0 < α) {u : E d × ℝ → ℝ}
    (h : ∀ K ⊆ Ω, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox k α A ρ₀ u K P) :
    ContinuousOn u Ω := by
  intro p hp
  obtain ⟨A, ρ₀, P, hρ, hP⟩ := h {p} (singleton_subset_iff.2 hp) isCompact_singleton
  exact (hP.continuousAt hα hρ (mem_singleton p)).continuousWithinAt

/-- (k = 0) `u` is continuous and locally `α`-Hölder on the open `Ω`. -/
theorem holderOnPar_of_polyApprox0 {Ω : Set (E d × ℝ)} (_hΩ : IsOpen Ω) {α : ℝ}
    (hα : 0 < α ∧ α < 1) {u : E d × ℝ → ℝ}
    (h : ∀ K ⊆ Ω, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 0 α A ρ₀ u K P) :
    ContinuousOn u Ω ∧ LocHolderOnPar α u Ω := by
  have hc := continuousOn_of_polyApprox hα.1 h
  refine ⟨hc, fun K hK hKc ↦ ?_⟩
  obtain ⟨A, ρ₀, P, hρ, hP⟩ := h K hK hKc
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hc.mono hK)
  exact ⟨_, hP.holderOnPar0 hα.1 hρ (B := B) fun p hp ↦ by simpa [Real.norm_eq_abs] using hB p hp⟩

/-- (k = 1, pointwise part) `gradₓ u p = (P p).b`, and the slice has this gradient. -/
theorem gradₓ_eq_of_polyApprox1 {K : Set (E d × ℝ)} {α A ρ₀ : ℝ} {u : E d × ℝ → ℝ}
    {P : E d × ℝ → CaloricPoly d} (hα : 0 < α) (hρ : 0 < ρ₀) (hP : PolyApprox 1 α A ρ₀ u K P)
    {p : E d × ℝ} (hp : p ∈ K) :
    HasGradientAt (fun y ↦ u (y, p.2)) (gradₓ u p) p.1 ∧ gradₓ u p = (P p).b := by
  have hg := hP.hasGradientAt le_rfl hα hρ hp
  have e : gradₓ u p = (P p).b := hg.gradient
  exact ⟨by rw [e]; exact hg, e⟩

/-- The pairwise gradient estimate from two degree-1 expansions (`0 < pdist p q < ρ₀/3`). -/
theorem PolyApprox.gradₓ_near1 {K : Set (E d × ℝ)} {α A ρ₀ : ℝ} {u : E d × ℝ → ℝ}
    {P : E d × ℝ → CaloricPoly d} (hα : 0 < α ∧ α < 1) (hρ : 0 < ρ₀) (hA : 0 ≤ A)
    (hP : PolyApprox 1 α A ρ₀ u K P) {p q : E d × ℝ} (hp : p ∈ K) (hq : q ∈ K)
    (hδ0 : 0 < pdist p q) (hδ : pdist p q < ρ₀ / 3) :
    ‖gradₓ u p - gradₓ u q‖ ≤ 18 * Real.sqrt d * A * pdist p q ^ α ∧
      ∀ i, |gradₓ u p i - gradₓ u q i| ≤ 18 * A * pdist p q ^ α := by
  obtain ⟨-, hbi, hbn, -, -⟩ := CaloricPoly.two_expansions_coeff (by norm_num)
    ⟨hα.1, hα.2.le⟩ hA (hP.approx p hp) (hP.approx q hq) hδ0 hδ
  have hM : (P p).M = 0 := (hP.deg p hp).2
  simp only [hM, map_zero, LinearMap.zero_apply, add_zero, Nat.cast_one,
    add_sub_cancel_left] at hbi hbn
  rw [(gradₓ_eq_of_polyApprox1 hα.1 hρ hP hp).2, (gradₓ_eq_of_polyApprox1 hα.1 hρ hP hq).2]
  exact ⟨hbn, fun i ↦ by simpa using hbi i⟩

/-- (k = 1) On the open `Ω`, `u` is continuous, the slice gradient exists, `gradₓ u` is continuous
and each of its coordinates is locally `α`-Hölder. -/
theorem continuousOn_gradₓ_of_polyApprox1 {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {α : ℝ}
    (hα : 0 < α ∧ α < 1) {u : E d × ℝ → ℝ}
    (h : ∀ K ⊆ Ω, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 1 α A ρ₀ u K P) :
    ContinuousOn u Ω ∧ (∀ p ∈ Ω, HasGradientAt (fun y ↦ u (y, p.2)) (gradₓ u p) p.1) ∧
      ContinuousOn (gradₓ u) Ω ∧ ∀ i, LocHolderOnPar α (fun p ↦ gradₓ u p i) Ω := by
  have hc := continuousOn_of_polyApprox hα.1 h
  have hgrad : ∀ p ∈ Ω, HasGradientAt (fun y ↦ u (y, p.2)) (gradₓ u p) p.1 := fun p hp ↦ by
    obtain ⟨A, ρ₀, P, hρ, hP⟩ := h {p} (singleton_subset_iff.2 hp) isCompact_singleton
    exact (gradₓ_eq_of_polyApprox1 hα.1 hρ hP (mem_singleton p)).1
  have hgc : ContinuousOn (gradₓ u) Ω := by
    intro p hp
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ p hp
    have hK : Metric.closedBall p (r / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (by linarith)).trans hrΩ
    obtain ⟨A, ρ₀, P, hρ, hP⟩ := h _ hK (isCompact_closedBall _ _)
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hpc : Continuous fun q ↦ pdist p q := by
      simpa only [pdist_comm p] using continuous_pdist_left p
    have hlim : Tendsto (fun q ↦ 18 * Real.sqrt d * max A 0 * pdist p q ^ α) (𝓝 p) (𝓝 0) := by
      have hcont : Continuous fun q ↦ 18 * Real.sqrt d * max A 0 * pdist p q ^ α :=
        continuous_const.mul (Continuous.rpow_const hpc fun _ ↦ Or.inr hα.1.le)
      simpa [Real.zero_rpow hα.1.ne'] using hcont.tendsto p
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [Metric.closedBall_mem_nhds p (half_pos hr),
      (hpc.tendsto p).eventually (gt_mem_nhds (by rw [pdist_self]; positivity :
        pdist p p < ρ₀ / 3))] with q hq hqδ
    rcases (pdist_nonneg p q).eq_or_lt with h0 | h0
    · obtain rfl := pdist_eq_zero.1 h0.symm
      simp [Real.zero_rpow hα.1.ne']
    · rw [norm_sub_rev]
      exact (PolyApprox.gradₓ_near1 hα hρ (le_max_right _ _) hP.max_zero
        (Metric.mem_closedBall_self (half_pos hr).le) hq h0 hqδ).1
  refine ⟨hc, hgrad, hgc, fun i K hK hKc ↦ ?_⟩
  obtain ⟨A, ρ₀, P, hρ, hP⟩ := h K hK hKc
  have hci : ContinuousOn (fun p ↦ gradₓ u p i) K :=
    (EuclideanSpace.proj i : E d →L[ℝ] ℝ).continuous.comp_continuousOn (hgc.mono hK)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hci
  exact ⟨_, HolderOnPar.of_near_far (C := 18 * max A 0) (by positivity : 0 < ρ₀ / 3) hα.1.le
    (B := B) (fun p hp ↦ by simpa [Real.norm_eq_abs] using hB p hp)
    fun p hp q hq h0 hδ ↦ (PolyApprox.gradₓ_near1 hα hρ (le_max_right _ _) hP.max_zero
      hp hq h0 hδ).2 i⟩

/-! ### Degree 2 -/

/-- Normed-valued version of `isLittleO_of_abs_le_rpow`. -/
theorem isLittleO_of_norm_le_rpow {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {e : F → G} {A ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (h : ∀ x : F, ‖x‖ < ρ → ‖e x‖ ≤ A * ‖x‖ ^ (1 + β)) : e =o[𝓝 0] fun x ↦ x := by
  rw [← Asymptotics.isLittleO_norm_left]
  exact isLittleO_of_abs_le_rpow hρ hβ fun x hx ↦ by rw [abs_norm]; exact h x hx

/-- Continuity at `p` from a `pdist`-Hölder bound at `p` on a neighbourhood. -/
theorem continuousAt_of_pdist_bound {F : Type*} [NormedAddCommGroup F] {f : E d × ℝ → F}
    {p : E d × ℝ} {N : Set (E d × ℝ)} (hN : N ∈ 𝓝 p) {η C α : ℝ} (hη : 0 < η) (hα : 0 < α)
    (h : ∀ q ∈ N, 0 < pdist p q → pdist p q < η → ‖f p - f q‖ ≤ C * pdist p q ^ α) :
    ContinuousAt f p := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hpc : Continuous fun q ↦ pdist p q := by
    simpa only [pdist_comm p] using continuous_pdist_left p
  have hlim : Tendsto (fun q ↦ max C 0 * pdist p q ^ α) (𝓝 p) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using
      (continuous_const.mul (Continuous.rpow_const hpc fun _ ↦ Or.inr hα.le)).tendsto p
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hN, (hpc.tendsto p).eventually
    (gt_mem_nhds (by rw [pdist_self]; exact hη : pdist p p < η))] with q hq hqη
  rcases (pdist_nonneg p q).eq_or_lt with h0 | h0
  · obtain rfl := pdist_eq_zero.1 h0.symm
    simp [Real.zero_rpow hα.ne']
  · rw [norm_sub_rev]
    exact (h q hq h0 hqη).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (pdist_nonneg _ _) _))

theorem CaloricPoly.norm_toEuclideanLin_le {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm)
    (v : E d) : ‖Matrix.toEuclideanLin M v‖ ≤ (∑ i, ∑ j, |M i j|) * ‖v‖ := by
  set w := Matrix.toEuclideanLin M v
  have h1 : ‖w‖ ^ 2 = CaloricPoly.bilin M v w := by
    rw [← CaloricPoly.inner_toEuclideanLin hM, real_inner_self_eq_norm_sq]
  have h2 : CaloricPoly.bilin M v w ≤ ‖CaloricPoly.bilin M‖ * ‖v‖ * ‖w‖ := by
    have := (CaloricPoly.bilin M).le_opNorm₂ v w
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have h3 := CaloricPoly.norm_bilin_le M
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · refine le_of_mul_le_mul_right ?_ h0
    calc ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
      _ ≤ ‖CaloricPoly.bilin M‖ * ‖v‖ * ‖w‖ := h1 ▸ h2
      _ ≤ (∑ i, ∑ j, |M i j|) * ‖v‖ * ‖w‖ := by gcongr

/-- The spatial Hessian entry `D²ₓu(p)[eᵢ, eⱼ]`. -/
noncomputable abbrev hessEntry (u : E d × ℝ → ℝ) (i j : Fin d) (p : E d × ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

namespace PolyApprox

variable {K : Set (E d × ℝ)} {α A ρ₀ : ℝ} {u : E d × ℝ → ℝ} {P : E d × ℝ → CaloricPoly d}

theorem b_eq_gradₓ (hP : PolyApprox 2 α A ρ₀ u K P) (hα : 0 < α) (hρ : 0 < ρ₀) {p : E d × ℝ}
    (hp : p ∈ K) : (P p).b = gradₓ u p :=
  ((hP.hasGradientAt (by norm_num) hα hρ hp).gradient).symm

theorem c_eq_dₜ (hP : PolyApprox 2 α A ρ₀ u K P) (hα : 0 < α) (hρ : 0 < ρ₀) {p : E d × ℝ}
    (hp : p ∈ K) : (P p).c = dₜ u p :=
  ((hP.hasDerivAt_time le_rfl hα hρ hp).deriv).symm

/-- Near-pair estimates for degree-2 fields (`0 < δ = pdist p q < ρ₀/3`). -/
theorem near2 (hP : PolyApprox 2 α A ρ₀ u K P) (hα : 0 < α ∧ α < 1) (hA : 0 ≤ A)
    {p q : E d × ℝ} (hp : p ∈ K) (hq : q ∈ K) (h0 : 0 < pdist p q) (hδ : pdist p q < ρ₀ / 3) :
    |(P p).c - (P q).c| ≤ 36 * A * pdist p q ^ α ∧
      (∀ i j, |(P p).M i j - (P q).M i j| ≤ 432 * A * pdist p q ^ α) ∧
      ‖(P p).b + Matrix.toEuclideanLin (P p).M (q - p).1 - (P q).b‖ ≤
        18 * Real.sqrt d * A * pdist p q ^ (1 + α) := by
  obtain ⟨-, -, hbn, hcc, hM⟩ := CaloricPoly.two_expansions_coeff le_rfl ⟨hα.1, hα.2.le⟩ hA
    (hP.approx p hp) (hP.approx q hq) h0 hδ
  have e1 : ((2 : ℕ) : ℝ) + α - 2 = α := by push_cast; ring
  have e2 : ((2 : ℕ) : ℝ) + α - 1 = 1 + α := by push_cast; ring
  rw [e1] at hcc hM
  rw [e2] at hbn
  exact ⟨hcc, hM, hbn⟩

end PolyApprox

section Campanato2

variable {Ω : Set (E d × ℝ)} {α : ℝ} {u : E d × ℝ → ℝ}

/-- The second spatial derivative from degree-2 approximation: at every `p ∈ K ⊆ Ω` the
`fderiv` of the slice has derivative `bilin (P p).M` at `p.1`. -/
theorem PolyApprox.hasFDerivAt_fderiv_slice (hΩ : IsOpen Ω) (hα : 0 < α ∧ α < 1)
    (h : ∀ K ⊆ Ω, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P)
    {K : Set (E d × ℝ)} {A ρ₀ : ℝ} {P : E d × ℝ → CaloricPoly d} (hKΩ : K ⊆ Ω) (hρ : 0 < ρ₀)
    (hP : PolyApprox 2 α A ρ₀ u K P) {p : E d × ℝ} (hp : p ∈ K) :
    HasFDerivAt (fderiv ℝ (fun y ↦ u (y, p.2))) (CaloricPoly.bilin (P p).M) p.1 := by
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := Metric.isOpen_iff.1 hΩ p (hKΩ hp)
  set r := r₀ / 2 with hr_def
  have hr : 0 < r := half_pos hr₀
  have hrΩ : Metric.closedBall p r ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hr₀Ω
  obtain ⟨A₀, ρ₁, P₀, hρ₁, hP₀⟩ := h _ hrΩ (isCompact_closedBall _ _)
  have hpK : p ∈ Metric.closedBall p r := Metric.mem_closedBall_self hr.le
  have heq : P p = P₀ p := hP.eq_of_polyApprox hP₀ le_rfl hα.1 hρ hρ₁ hp hpK
  rw [heq]
  have hfd : ∀ y, (y, p.2) ∈ Ω →
      fderiv ℝ (fun z ↦ u (z, p.2)) y = InnerProductSpace.toDual ℝ (E d) (gradₓ u (y, p.2)) := by
    intro y hy
    obtain ⟨A', ρ', P', hρ', hP'⟩ := h {(y, p.2)} (singleton_subset_iff.2 hy) isCompact_singleton
    rw [← hP'.b_eq_gradₓ hα.1 hρ' (mem_singleton _)]
    exact (hP'.hasGradientAt (by norm_num) hα.1 hρ' (mem_singleton _)).hasFDerivAt.fderiv
  have hdual : ∀ v, InnerProductSpace.toDual ℝ (E d) (Matrix.toEuclideanLin (P₀ p).M v) =
      CaloricPoly.bilin (P₀ p).M v := fun v ↦ by
    ext w
    simp [CaloricPoly.inner_toEuclideanLin (P₀ p).symm]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine isLittleO_of_norm_le_rpow (A := 18 * Real.sqrt d * max A₀ 0) (ρ := min r (ρ₁ / 3))
    (lt_min hr (by positivity)) hα.1 fun v hv ↦ ?_
  have hv1 : ‖v‖ < r := hv.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ < ρ₁ / 3 := hv.trans_le (min_le_right _ _)
  have hq : (p.1 + v, p.2) ∈ Metric.closedBall p r := by
    rw [Metric.mem_closedBall, Prod.dist_eq, dist_self, dist_eq_norm, add_sub_cancel_left]
    exact max_le hv1.le hr.le
  have hpΩ : (p.1, p.2) ∈ Ω := by rw [Prod.mk.eta]; exact hKΩ hp
  rw [hfd _ (hrΩ hq), hfd _ hpΩ, Prod.mk.eta, ← hP₀.b_eq_gradₓ hα.1 hρ₁ hq,
    ← hP₀.b_eq_gradₓ hα.1 hρ₁ hpK]
  rcases eq_or_ne v 0 with rfl | hv0
  · simp only [add_zero, Prod.mk.eta, sub_self, map_zero, norm_zero]
    positivity
  have hpq : pdist p (p.1 + v, p.2) = ‖v‖ := by simp [pdist]
  obtain ⟨-, -, hb⟩ := hP₀.max_zero.near2 hα (le_max_right _ _) hpK hq
    (by rw [hpq]; exact norm_pos_iff.2 hv0) (by rw [hpq]; exact hv2)
  have hsub : ((p.1 + v, p.2) - p).1 = v := by simp
  rw [hsub, hpq] at hb
  rw [← hdual v, ← map_sub, ← map_sub, LinearIsometryEquiv.norm_map]
  calc ‖(P₀ (p.1 + v, p.2)).b - (P₀ p).b - Matrix.toEuclideanLin (P₀ p).M v‖
      = ‖(P₀ p).b + Matrix.toEuclideanLin (P₀ p).M v - (P₀ (p.1 + v, p.2)).b‖ := by
        rw [← norm_neg]; congr 1; abel
    _ ≤ _ := hb

/-- The iterated second derivative of the slice from a degree-2 field. -/
theorem PolyApprox.iteratedFDeriv_slice (hΩ : IsOpen Ω) (hα : 0 < α ∧ α < 1)
    (h : ∀ K ⊆ Ω, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P)
    {K : Set (E d × ℝ)} {A ρ₀ : ℝ} {P : E d × ℝ → CaloricPoly d} (hKΩ : K ⊆ Ω) (hρ : 0 < ρ₀)
    (hP : PolyApprox 2 α A ρ₀ u K P) {p : E d × ℝ} (hp : p ∈ K) (m : Fin 2 → E d) :
    iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1 m = CaloricPoly.bilin (P p).M (m 0) (m 1) := by
  rw [iteratedFDeriv_two_apply, (hP.hasFDerivAt_fderiv_slice hΩ hα h hKΩ hρ hp).fderiv]

theorem PolyApprox.M_eq_hessEntry (hΩ : IsOpen Ω) (hα : 0 < α ∧ α < 1)
    (h : ∀ K ⊆ Ω, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P)
    {K : Set (E d × ℝ)} {A ρ₀ : ℝ} {P : E d × ℝ → CaloricPoly d} (hKΩ : K ⊆ Ω) (hρ : 0 < ρ₀)
    (hP : PolyApprox 2 α A ρ₀ u K P) {p : E d × ℝ} (hp : p ∈ K) (i j : Fin d) :
    (P p).M i j = hessEntry u i j p := by
  rw [hessEntry, hP.iteratedFDeriv_slice hΩ hα h hKΩ hρ hp]
  simp [CaloricPoly.bilin_single]

end Campanato2

/-- (k = 2) On `U ×ˢ I` (`U`, `I` open): `IsC21On U I u`; for every set `K` carrying an
approximating field and every `p ∈ K`, the coefficients of `P p` are `u p`, `gradₓ u p`, `dₜ u p`
and the Hessian entries, and `lapₓ u p = tr M`; and `dₜ u`, the coordinates of `gradₓ u` and the
Hessian entries are locally `α`-Hölder. -/
theorem isC21On_of_polyApprox {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {u : E d × ℝ → ℝ}
    (h : ∀ K ⊆ U ×ˢ I, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P) :
    IsC21On U I u ∧
      (∀ K ⊆ U ×ˢ I, ∀ A ρ₀ (P : E d × ℝ → CaloricPoly d), 0 < ρ₀ →
        PolyApprox 2 α A ρ₀ u K P → ∀ p ∈ K,
          (P p).a = u p ∧ (P p).b = gradₓ u p ∧ (P p).c = dₜ u p ∧
          (∀ i j, (P p).M i j = iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
            ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) ∧
          lapₓ u p = Matrix.trace (P p).M) ∧
      LocHolderOnPar α (dₜ u) (U ×ˢ I) ∧
      (∀ i, LocHolderOnPar α (fun p ↦ gradₓ u p i) (U ×ˢ I)) ∧
      ∀ i j, LocHolderOnPar α (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (U ×ˢ I) := by
  set Ω := U ×ˢ I with hΩdef
  have hΩ : IsOpen Ω := hU.prod hI
  have hc := continuousOn_of_polyApprox hα.1 h
  have hfield : ∀ p ∈ Ω, ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u {p} P := fun p hp ↦
    h {p} (singleton_subset_iff.2 hp) isCompact_singleton
  have hnbhd : ∀ p ∈ Ω, ∃ r > 0, Metric.closedBall p r ⊆ Ω := fun p hp ↦ by
    obtain ⟨r, hr, h'⟩ := Metric.isOpen_iff.1 hΩ p hp
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (by linarith)).trans h'⟩
  -- the intrinsic Hessian matrix
  set Hm : E d × ℝ → Matrix (Fin d) (Fin d) ℝ := fun p ↦ Matrix.of fun i j ↦ hessEntry u i j p
    with hHm
  have hPM : ∀ {K A ρ₀} {P : E d × ℝ → CaloricPoly d}, K ⊆ Ω → 0 < ρ₀ →
      PolyApprox 2 α A ρ₀ u K P → ∀ p ∈ K, (P p).M = Hm p := fun hKΩ hρ hP p hp ↦
    Matrix.ext fun i j ↦ hP.M_eq_hessEntry hΩ hα h hKΩ hρ hp i j
  have hDform : ∀ p ∈ Ω, ∀ m : Fin 2 → E d,
      iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1 m = CaloricPoly.bilin (Hm p) (m 0) (m 1) := by
    intro p hp m
    obtain ⟨A, ρ₀, P, hρ, hP⟩ := hfield p hp
    rw [hP.iteratedFDeriv_slice hΩ hα h (singleton_subset_iff.2 hp) hρ (mem_singleton p),
      hPM (singleton_subset_iff.2 hp) hρ hP p (mem_singleton p)]
  -- continuity of the Hessian entries and of `dₜ u`
  have hHc : ∀ i j, ContinuousOn (hessEntry u i j) Ω := fun i j p hp ↦ by
    obtain ⟨r, hr, hrΩ⟩ := hnbhd p hp
    obtain ⟨A₀, ρ₁, P₀, hρ₁, hP₀⟩ := h _ hrΩ (isCompact_closedBall _ _)
    have hpK := Metric.mem_closedBall_self (x := p) hr.le
    refine (continuousAt_of_pdist_bound (Metric.closedBall_mem_nhds p hr)
      (by positivity : (0 : ℝ) < ρ₁ / 3) hα.1 (C := 432 * max A₀ 0)
      fun q hq h0 hδ ↦ ?_).continuousWithinAt
    rw [Real.norm_eq_abs, ← hP₀.M_eq_hessEntry hΩ hα h hrΩ hρ₁ hpK,
      ← hP₀.M_eq_hessEntry hΩ hα h hrΩ hρ₁ hq]
    exact (hP₀.max_zero.near2 hα (le_max_right _ _) hpK hq h0 hδ).2.1 i j
  have hdtc : ContinuousOn (dₜ u) Ω := fun p hp ↦ by
    obtain ⟨r, hr, hrΩ⟩ := hnbhd p hp
    obtain ⟨A₀, ρ₁, P₀, hρ₁, hP₀⟩ := h _ hrΩ (isCompact_closedBall _ _)
    have hpK := Metric.mem_closedBall_self (x := p) hr.le
    refine (continuousAt_of_pdist_bound (Metric.closedBall_mem_nhds p hr)
      (by positivity : (0 : ℝ) < ρ₁ / 3) hα.1 (C := 36 * max A₀ 0)
      fun q hq h0 hδ ↦ ?_).continuousWithinAt
    rw [Real.norm_eq_abs, ← hP₀.c_eq_dₜ hα.1 hρ₁ hpK, ← hP₀.c_eq_dₜ hα.1 hρ₁ hq]
    exact (hP₀.max_zero.near2 hα (le_max_right _ _) hpK hq h0 hδ).1
  -- the gradient near-pair estimate
  have hgnear : ∀ {K A ρ₀} {P : E d × ℝ → CaloricPoly d}, 0 < ρ₀ → 0 ≤ A →
      PolyApprox 2 α A ρ₀ u K P → ∀ p ∈ K, ∀ q ∈ K, 0 < pdist p q →
      pdist p q < min 1 (ρ₀ / 3) →
      ‖gradₓ u p - gradₓ u q‖ ≤ (∑ i, ∑ j, |(P p).M i j| + 18 * Real.sqrt d * A) *
        pdist p q ^ α := by
    intro K A ρ₀ P hρ hA hP p hp q hq h0 hδ
    have hδ1 : pdist p q ≤ 1 := (hδ.trans_le (min_le_left _ _)).le
    obtain ⟨-, -, hb⟩ := hP.near2 hα hA hp hq h0 (hδ.trans_le (min_le_right _ _))
    rw [← hP.b_eq_gradₓ hα.1 hρ hp, ← hP.b_eq_gradₓ hα.1 hρ hq]
    have hS : 0 ≤ ∑ i, ∑ j, |(P p).M i j| := by positivity
    have hMv : ‖Matrix.toEuclideanLin (P p).M (q - p).1‖ ≤
        (∑ i, ∑ j, |(P p).M i j|) * pdist p q :=
      (CaloricPoly.norm_toEuclideanLin_le (P p).symm _).trans
        (mul_le_mul_of_nonneg_left (by rw [pdist_comm]; exact norm_fst_sub_le_pdist q p) hS)
    have hδα : pdist p q ≤ pdist p q ^ α := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' h0.le hδ1 hα.1.le hα.2.le
    have hδ1α : pdist p q ^ (1 + α) ≤ pdist p q ^ α :=
      Real.rpow_le_rpow_of_exponent_ge' h0.le hδ1 hα.1.le (by linarith)
    calc ‖(P p).b - (P q).b‖
        = ‖((P p).b + Matrix.toEuclideanLin (P p).M (q - p).1 - (P q).b) -
            Matrix.toEuclideanLin (P p).M (q - p).1‖ := by congr 1; abel
      _ ≤ ‖(P p).b + Matrix.toEuclideanLin (P p).M (q - p).1 - (P q).b‖ +
            ‖Matrix.toEuclideanLin (P p).M (q - p).1‖ := norm_sub_le _ _
      _ ≤ 18 * Real.sqrt d * A * pdist p q ^ (1 + α) +
            (∑ i, ∑ j, |(P p).M i j|) * pdist p q := add_le_add hb hMv
      _ ≤ 18 * Real.sqrt d * A * pdist p q ^ α + (∑ i, ∑ j, |(P p).M i j|) * pdist p q ^ α := by
          gcongr
      _ = _ := by ring
  have hgc : ContinuousOn (gradₓ u) Ω := fun p hp ↦ by
    obtain ⟨r, hr, hrΩ⟩ := hnbhd p hp
    obtain ⟨A₀, ρ₁, P₀, hρ₁, hP₀⟩ := h _ hrΩ (isCompact_closedBall _ _)
    have hpK := Metric.mem_closedBall_self (x := p) hr.le
    exact (continuousAt_of_pdist_bound (Metric.closedBall_mem_nhds p hr)
      (lt_min one_pos (by positivity) : (0 : ℝ) < min 1 (ρ₁ / 3)) hα.1
      fun q hq h0 hδ ↦ hgnear hρ₁ (le_max_right _ _) hP₀.max_zero p hpK q hq h0 hδ)
      |>.continuousWithinAt
  -- continuity of the Hessian map
  have hDbound : ∀ p ∈ Ω, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ 2 (fun y ↦ u (y, q.2)) q.1 - iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1‖
        ≤ ∑ i, ∑ j, |hessEntry u i j q - hessEntry u i j p| := by
    intro p hp q hq
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
    rw [ContinuousMultilinearMap.sub_apply, hDform q hq m, hDform p hp m,
      ← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply, ← CaloricPoly.bilin_sub,
      Fin.prod_univ_two]
    refine ((CaloricPoly.bilin _).le_opNorm₂ _ _).trans ?_
    rw [mul_assoc]
    gcongr
    refine (CaloricPoly.norm_bilin_le _).trans (le_of_eq ?_)
    simp [hHm]
  have hDc : ContinuousOn (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1) Ω := by
    intro p hp
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hg : Tendsto (fun q ↦ ∑ i, ∑ j, |hessEntry u i j q - hessEntry u i j p|) (𝓝[Ω] p)
        (𝓝 0) := by
      have hij : ∀ i j, Tendsto (fun q ↦ |hessEntry u i j q - hessEntry u i j p|) (𝓝[Ω] p)
          (𝓝 0) := fun i j ↦ by
        simpa using (((hHc i j p hp).sub
          (continuousWithinAt_const (b := hessEntry u i j p))).abs).tendsto
      simpa using tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ hij i j
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun q hq ↦ hDbound p hp q hq) hg
  -- the bilinear Hessian is continuous
  have hbilc : ContinuousOn (fun p ↦ CaloricPoly.bilin (Hm p)) Ω := by
    simp only [CaloricPoly.bilin, hHm, Matrix.of_apply]
    exact continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      (hHc i j).smul continuousOn_const
  -- slices are `C²`
  have hslice : ∀ t ∈ I, ContDiffOn ℝ 2 (fun x ↦ u (x, t)) U := by
    intro t ht
    have hmem : ∀ y ∈ U, (y, t) ∈ Ω := fun y hy ↦ ⟨hy, ht⟩
    have hdiff : DifferentiableOn ℝ (fun x ↦ u (x, t)) U := fun y hy ↦ by
      obtain ⟨A, ρ₀, P, hρ, hP⟩ := hfield _ (hmem y hy)
      exact (hP.hasGradientAt (by norm_num) hα.1 hρ (mem_singleton _)).hasFDerivAt
        |>.differentiableAt.differentiableWithinAt
    have hd2 : ∀ y ∈ U, HasFDerivAt (fderiv ℝ (fun x ↦ u (x, t)))
        (CaloricPoly.bilin (Hm (y, t))) y := fun y hy ↦ by
      obtain ⟨A, ρ₀, P, hρ, hP⟩ := hfield _ (hmem y hy)
      have := hP.hasFDerivAt_fderiv_slice hΩ hα h (singleton_subset_iff.2 (hmem y hy)) hρ
        (mem_singleton _)
      rwa [hPM (singleton_subset_iff.2 (hmem y hy)) hρ hP _ (mem_singleton _)] at this
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fun x ↦ u (x, t))) U := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun y hy ↦ (hd2 y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      rw [contDiffOn_zero]
      refine ContinuousOn.congr (f := fun y ↦ CaloricPoly.bilin (Hm (y, t))) ?_
        fun y hy ↦ (hd2 y hy).fderiv
      exact hbilc.comp (continuous_id.prodMk continuous_const).continuousOn hmem
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hdiff, by simp, h1⟩
  -- identification of the coefficients
  have hident : ∀ K ⊆ U ×ˢ I, ∀ A ρ₀ (P : E d × ℝ → CaloricPoly d), 0 < ρ₀ →
      PolyApprox 2 α A ρ₀ u K P → ∀ p ∈ K,
        (P p).a = u p ∧ (P p).b = gradₓ u p ∧ (P p).c = dₜ u p ∧
        (∀ i j, (P p).M i j = iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) ∧
        lapₓ u p = Matrix.trace (P p).M := by
    intro K hKΩ A ρ₀ P hρ hP p hp
    refine ⟨hP.a_eq hα.1 hρ hp, hP.b_eq_gradₓ hα.1 hρ hp, hP.c_eq_dₜ hα.1 hρ hp,
      fun i j ↦ hP.M_eq_hessEntry hΩ hα h hKΩ hρ hp i j, ?_⟩
    rw [lapₓ, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp only [hP.iteratedFDeriv_slice hΩ hα h hKΩ hρ hp, EuclideanSpace.basisFun_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, CaloricPoly.bilin_single]
    rfl
  refine ⟨⟨hc, hslice, hgc, hDc, fun p hp ↦ ?_, hdtc⟩, hident, ?_, ?_, ?_⟩
  · obtain ⟨A, ρ₀, P, hρ, hP⟩ := hfield p hp
    exact (hP.hasDerivAt_time le_rfl hα.1 hρ (mem_singleton p)).differentiableAt
  · intro K hK hKc
    obtain ⟨A, ρ₀, P, hρ, hP⟩ := h K hK hKc
    obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hdtc.mono hK)
    refine ⟨_, HolderOnPar.of_near_far (C := 36 * max A 0) (by positivity : (0 : ℝ) < ρ₀ / 3)
      hα.1.le (B := B) (fun p hp ↦ by simpa [Real.norm_eq_abs] using hB p hp)
      fun p hp q hq h0 hδ ↦ ?_⟩
    rw [← hP.c_eq_dₜ hα.1 hρ hp, ← hP.c_eq_dₜ hα.1 hρ hq]
    exact (hP.max_zero.near2 hα (le_max_right _ _) hp hq h0 hδ).1
  · intro i K hK hKc
    obtain ⟨A, ρ₀, P, hρ, hP⟩ := h K hK hKc
    have hci : ContinuousOn (fun p ↦ gradₓ u p i) K :=
      (EuclideanSpace.proj i : E d →L[ℝ] ℝ).continuous.comp_continuousOn (hgc.mono hK)
    obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hci
    have hSc : ContinuousOn (fun p ↦ ∑ i, ∑ j, |hessEntry u i j p|) K :=
      continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
        ((hHc i j).mono hK).abs
    obtain ⟨m, hm⟩ := hKc.exists_bound_of_continuousOn hSc
    refine ⟨_, HolderOnPar.of_near_far (C := m + 18 * Real.sqrt d * max A 0)
      (lt_min one_pos (by positivity) : (0 : ℝ) < min 1 (ρ₀ / 3)) hα.1.le (B := B)
      (fun p hp ↦ by simpa [Real.norm_eq_abs] using hB p hp) fun p hp q hq h0 hδ ↦ ?_⟩
    have hg := hgnear hρ (le_max_right _ _) hP.max_zero p hp q hq h0 hδ
    have hSm : ∑ i, ∑ j, |(P p).M i j| ≤ m := by
      have := hm p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      simpa only [hP.M_eq_hessEntry hΩ hα h hK hρ hp] using this
    calc |gradₓ u p i - gradₓ u q i| = ‖(gradₓ u p - gradₓ u q) i‖ := by
          rw [Real.norm_eq_abs, PiLp.sub_apply]
      _ ≤ ‖gradₓ u p - gradₓ u q‖ := PiLp.norm_apply_le _ _
      _ ≤ _ := hg
      _ ≤ _ := by gcongr
  · intro i j K hK hKc
    obtain ⟨A, ρ₀, P, hρ, hP⟩ := h K hK hKc
    obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn ((hHc i j).mono hK)
    refine ⟨_, HolderOnPar.of_near_far (C := 432 * max A 0) (by positivity : (0 : ℝ) < ρ₀ / 3)
      hα.1.le (B := B) (fun p hp ↦ by simpa [Real.norm_eq_abs] using hB p hp)
      fun p hp q hq h0 hδ ↦ ?_⟩
    have e1 := hP.M_eq_hessEntry hΩ hα h hK hρ hp i j
    have e2 := hP.M_eq_hessEntry hΩ hα h hK hρ hq i j
    simp only [hessEntry] at e1 e2
    rw [← e1, ← e2]
    exact (hP.max_zero.near2 hα (le_max_right _ _) hp hq h0 hδ).2.1 i j

/-- **`heat_eq_of_polyApprox`**: if the approximating polynomials have source `H`, then
`dₜ u - lapₓ u = H` on `U ×ˢ I`. -/
theorem heat_eq_of_polyApprox {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {u H : E d × ℝ → ℝ}
    (h : ∀ K ⊆ U ×ˢ I, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P ∧
      ∀ p ∈ K, (P p).src = H p) :
    ∀ p ∈ U ×ˢ I, dₜ u p - lapₓ u p = H p := by
  have h' : ∀ K ⊆ U ×ˢ I, IsCompact K → ∃ A ρ₀ P, 0 < ρ₀ ∧ PolyApprox 2 α A ρ₀ u K P :=
    fun K hK hKc ↦ by
      obtain ⟨A, ρ₀, P, hρ, hP, -⟩ := h K hK hKc
      exact ⟨A, ρ₀, P, hρ, hP⟩
  have hid := (isC21On_of_polyApprox hU hI hα h').2.1
  intro p hp
  obtain ⟨A, ρ₀, P, hρ, hP, hsrc⟩ := h {p} (singleton_subset_iff.2 hp) isCompact_singleton
  obtain ⟨-, -, hc, -, hlap⟩ := hid {p} (singleton_subset_iff.2 hp) A ρ₀ P hρ hP p
    (mem_singleton p)
  rw [← hc, hlap, ← hsrc p (mem_singleton p), CaloricPoly.src]

end ParabolicBasic
