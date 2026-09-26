/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Holder
public import ParabolicBasic.Defs.Parabolic
public import ParabolicBasic.Calculus.Affine
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Parabolic Hölder spaces

* `pdist` (defined in `ParabolicBasic.Defs.Holder`): symmetry, triangle inequality, `mem_cCyl_iff`
  (`q ∈ cCyl x t r ↔ pdist q (x, t) < r`), behaviour under `parAffine`, comparison with the sup
  metric of `E d × ℝ`.
* `cCylAt p r := cCyl p.1 p.2 r`.
* `LocHolderOnPar α φ Ω` (Hölder on every compact subset) and `LocHolder φ Ω`
  (`∃ α ∈ (0, 1)`, `LocHolderOnPar α φ Ω`).
* The Hölder algebra: exponent monotonicity, sums, products, composition
  (`comp_holder`, `comp_lipschitz`, `comp_contDiff`), Lipschitz in `x` and `t` on a box ⇒ Hölder,
  local ⇒ compact (`LocHolderOnPar.of_local`).

All statements hold for every `d`, including `d = 0`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### The parabolic distance -/

/-- The centred parabolic cylinder around the point `p`: `cCyl p.1 p.2 r`. -/
abbrev cCylAt (p : E d × ℝ) (r : ℝ) : Set (E d × ℝ) := cCyl p.1 p.2 r

theorem pdist_comm (p q : E d × ℝ) : pdist p q = pdist q p := by
  simp only [pdist, norm_sub_rev, abs_sub_comm]

theorem pdist_nonneg (p q : E d × ℝ) : 0 ≤ pdist p q :=
  le_max_of_le_left (norm_nonneg _)

@[simp] theorem pdist_self (p : E d × ℝ) : pdist p p = 0 := by
  simp [pdist]

private theorem sqrt_abs_add_le (a b : ℝ) : Real.sqrt |a + b| ≤ Real.sqrt |a| + Real.sqrt |b| := by
  rw [Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt (abs_nonneg _),
    Real.sq_sqrt (abs_nonneg _)]
  have := abs_add_le a b
  have : 0 ≤ 2 * Real.sqrt |a| * Real.sqrt |b| := by positivity
  linarith

theorem pdist_triangle (p q r : E d × ℝ) : pdist p r ≤ pdist p q + pdist q r := by
  unfold pdist
  refine max_le ?_ ?_
  · calc ‖p.1 - r.1‖ ≤ ‖p.1 - q.1‖ + ‖q.1 - r.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc Real.sqrt |p.2 - r.2| = Real.sqrt |(p.2 - q.2) + (q.2 - r.2)| := by ring_nf
      _ ≤ Real.sqrt |p.2 - q.2| + Real.sqrt |q.2 - r.2| := sqrt_abs_add_le _ _
      _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)

/-- The centred cylinder is the open `pdist`-ball (all `r ∈ ℝ`). -/
theorem mem_cCyl_iff {x : E d} {t r : ℝ} {q : E d × ℝ} : q ∈ cCyl x t r ↔ pdist q (x, t) < r := by
  simp only [cCyl, pdist, mem_prod, Metric.mem_ball, dist_eq_norm, mem_Ioo, max_lt_iff]
  by_cases hr : 0 < r
  · rw [Real.sqrt_lt' hr, abs_sub_lt_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  · have : ¬ ‖q.1 - x‖ < r := fun h ↦ hr ((norm_nonneg _).trans_lt h)
    simp [this]

theorem mem_cCylAt_iff {p q : E d × ℝ} {r : ℝ} : q ∈ cCylAt p r ↔ pdist q p < r :=
  mem_cCyl_iff

/-- `pdist` is translation invariant. -/
theorem pdist_sub_right (p q z : E d × ℝ) : pdist (p - z) (q - z) = pdist p q := by
  simp [pdist]

theorem pdist_add_right (p q z : E d × ℝ) : pdist (p + z) (q + z) = pdist p q := by
  simp [pdist]

theorem pdist_sub_eq_pdist_zero (p q : E d × ℝ) : pdist (q - p) 0 = pdist q p := by
  simp [pdist]

theorem norm_fst_sub_le_pdist (p q : E d × ℝ) : ‖p.1 - q.1‖ ≤ pdist p q :=
  le_max_left _ _

theorem dist_fst_le_pdist (p q : E d × ℝ) : dist p.1 q.1 ≤ pdist p q := by
  rw [dist_eq_norm]; exact norm_fst_sub_le_pdist p q

theorem sqrt_abs_snd_sub_le_pdist (p q : E d × ℝ) : Real.sqrt |p.2 - q.2| ≤ pdist p q :=
  le_max_right _ _

theorem abs_snd_sub_le_pdist_sq (p q : E d × ℝ) : |p.2 - q.2| ≤ pdist p q ^ 2 := by
  calc |p.2 - q.2| = Real.sqrt |p.2 - q.2| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_abs_snd_sub_le_pdist p q) 2

/-- The sup-norm distance is controlled by `pdist`. -/
theorem norm_sub_le_max_pdist (p q : E d × ℝ) : ‖p - q‖ ≤ max (pdist p q) (pdist p q ^ 2) := by
  rw [Prod.norm_def]
  exact max_le_max (norm_fst_sub_le_pdist p q) (by
    rw [Prod.snd_sub, Real.norm_eq_abs]; exact abs_snd_sub_le_pdist_sq p q)

/-- Conversely, `pdist p q ≤ max (dist p q) (√(dist p q))`. -/
theorem pdist_le_max_dist (p q : E d × ℝ) : pdist p q ≤ max (dist p q) (Real.sqrt (dist p q)) := by
  have h1 : ‖p.1 - q.1‖ ≤ dist p q := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have h2 : |p.2 - q.2| ≤ dist p q := by
    rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _
  exact max_le_max h1 (Real.sqrt_le_sqrt h2)

/-- Pairs at sup-distance `≥ η` (`η ≤ 1`) are at parabolic distance `≥ η`. -/
theorem le_pdist_of_le_dist {p q : E d × ℝ} {η : ℝ} (hη : η ≤ 1) (h : η ≤ dist p q) :
    η ≤ pdist p q := by
  rcases le_or_gt η 0 with hη0 | hη0
  · exact hη0.trans (pdist_nonneg p q)
  rw [Prod.dist_eq] at h
  rcases le_max_iff.1 h with h | h
  · rw [dist_eq_norm] at h; exact h.trans (norm_fst_sub_le_pdist p q)
  · rw [Real.dist_eq] at h
    refine le_trans ?_ (sqrt_abs_snd_sub_le_pdist p q)
    rw [Real.le_sqrt hη0.le (abs_nonneg _)]
    nlinarith

theorem continuous_pdist :
    Continuous (fun x : (E d × ℝ) × (E d × ℝ) ↦ pdist x.1 x.2) := by
  unfold pdist
  exact (continuous_norm.comp (continuous_fst.fst.sub continuous_snd.fst)).max
    (Real.continuous_sqrt.comp (continuous_abs.comp (continuous_fst.snd.sub continuous_snd.snd)))

theorem continuous_pdist_left (p : E d × ℝ) : Continuous (fun q ↦ pdist q p) := by
  unfold pdist
  exact (continuous_norm.comp (continuous_fst.sub continuous_const)).max
    (Real.continuous_sqrt.comp (continuous_abs.comp (continuous_snd.sub continuous_const)))

/-- `pdist` on a compact set is bounded. -/
theorem exists_pdist_le_of_isCompact {K : Set (E d × ℝ)} (hK : IsCompact K) :
    ∃ D, 0 < D ∧ ∀ p ∈ K, ∀ q ∈ K, pdist p q ≤ D := by
  obtain ⟨B, hB⟩ := ((hK.prod hK).image (continuous_pdist (d := d))).bddAbove
  refine ⟨max B 1, by positivity, fun p hp q hq ↦ ?_⟩
  exact (hB ⟨(p, q), ⟨hp, hq⟩, rfl⟩).trans (le_max_left _ _)

/-- `parAffine` scales `pdist` by `r` (`0 ≤ r`). -/
theorem pdist_parAffine (x₀ : E d) (t₀ : ℝ) {r : ℝ} (hr : 0 ≤ r) (y y' : E d × ℝ) :
    pdist (parAffine x₀ t₀ r y) (parAffine x₀ t₀ r y') = r * pdist y y' := by
  simp only [pdist, parAffine_fst, parAffine_snd, add_sub_add_left_eq_sub, ← smul_sub,
    ← mul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, abs_mul, abs_of_nonneg (sq_nonneg r),
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
  exact (mul_max_of_nonneg _ _ hr).symm

/-- `parAffine x₀ t₀ r` maps `cCyl 0 0 ρ` onto `cCyl x₀ t₀ (r ρ)` (`0 < r`). -/
theorem image_parAffine_cCyl (x₀ : E d) (t₀ : ℝ) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    parAffine x₀ t₀ r '' cCyl 0 0 ρ = cCyl x₀ t₀ (r * ρ) := by
  have h0 : parAffine x₀ t₀ r 0 = (x₀, t₀) := by simp [parAffine]
  ext q
  simp only [mem_image, mem_cCyl_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← h0, pdist_parAffine x₀ t₀ hr.le]
    exact mul_lt_mul_of_pos_left hy hr
  · intro hq
    set y := parAffine (-(r⁻¹ • x₀)) (-(r⁻¹ ^ 2 * t₀)) r⁻¹ q
    have hy : parAffine x₀ t₀ r y = q := parAffine_parAffine_inv hr.ne' x₀ t₀ q
    refine ⟨y, ?_, hy⟩
    rw [← hy, ← h0, pdist_parAffine x₀ t₀ hr.le] at hq
    exact lt_of_mul_lt_mul_left hq hr.le

theorem pdist_eq_zero {p q : E d × ℝ} : pdist p q = 0 ↔ p = q := by
  constructor
  · intro h
    have h1 : ‖p.1 - q.1‖ = 0 := le_antisymm (h ▸ norm_fst_sub_le_pdist p q) (norm_nonneg _)
    have h2 : |p.2 - q.2| = 0 :=
      le_antisymm ((abs_snd_sub_le_pdist_sq p q).trans (by rw [h]; norm_num)) (abs_nonneg _)
    exact Prod.ext (sub_eq_zero.1 (norm_eq_zero.1 h1)) (sub_eq_zero.1 (abs_eq_zero.1 h2))
  · rintro rfl; exact pdist_self p

theorem pdist_pos {p q : E d × ℝ} (h : p ≠ q) : 0 < pdist p q :=
  (pdist_nonneg p q).lt_of_ne' (mt pdist_eq_zero.1 h)

/-! ### Local Hölder classes -/

/-- `φ` is locally parabolically `α`-Hölder on `Ω`: `HolderOnPar` on every compact subset. -/
def LocHolderOnPar (α : ℝ) (φ : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → ∃ C, HolderOnPar C α φ K

/-- `φ` is locally parabolically Hölder on `Ω` for some exponent `α ∈ (0, 1)`. -/
def LocHolder (φ : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Prop :=
  ∃ α ∈ Ioo (0 : ℝ) 1, LocHolderOnPar α φ Ω

/-! ### Hölder algebra on a set -/

/-- `s^α ≤ D^{α-β} s^β` for `0 ≤ s ≤ D`, `0 < β ≤ α`. -/
theorem rpow_le_rpow_sub_mul_rpow {s D α β : ℝ} (hs : 0 ≤ s) (hsD : s ≤ D) (hβ : 0 < β)
    (hβα : β ≤ α) : s ^ α ≤ D ^ (α - β) * s ^ β := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [Real.zero_rpow (hβ.trans_le hβα).ne', Real.zero_rpow hβ.ne', mul_zero]
  · calc s ^ α = s ^ (α - β) * s ^ β := by rw [← Real.rpow_add hs]; ring_nf
      _ ≤ D ^ (α - β) * s ^ β := by
        gcongr

namespace HolderOnPar

variable {C C' α β : ℝ} {φ ψ : E d × ℝ → ℝ} {S T : Set (E d × ℝ)}

theorem mono (h : HolderOnPar C α φ S) (hTS : T ⊆ S) : HolderOnPar C α φ T :=
  fun p hp q hq ↦ h p (hTS hp) q (hTS hq)

theorem mono_const (h : HolderOnPar C α φ S) (hCC' : C ≤ C') : HolderOnPar C' α φ S :=
  fun p hp q hq ↦ (h p hp q hq).trans
    (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (pdist_nonneg p q) _))

/-- A Hölder constant may be taken nonnegative. -/
theorem max_zero (h : HolderOnPar C α φ S) : HolderOnPar (max C 0) α φ S :=
  h.mono_const (le_max_left _ _)

/-- Exponents may shrink on sets of `pdist`-diameter `≤ D`. -/
theorem mono_exponent {D : ℝ} (h : HolderOnPar C α φ S) (hC : 0 ≤ C) (hβ : 0 < β) (hβα : β ≤ α)
    (hD : ∀ p ∈ S, ∀ q ∈ S, pdist p q ≤ D) : HolderOnPar (C * D ^ (α - β)) β φ S := by
  intro p hp q hq
  calc |φ p - φ q| ≤ C * pdist p q ^ α := h p hp q hq
    _ ≤ C * (D ^ (α - β) * pdist p q ^ β) := by
      gcongr
      exact rpow_le_rpow_sub_mul_rpow (pdist_nonneg p q) (hD p hp q hq) hβ hβα
    _ = C * D ^ (α - β) * pdist p q ^ β := by ring

theorem const (c α : ℝ) (S : Set (E d × ℝ)) : HolderOnPar 0 α (fun _ ↦ c) S :=
  fun p _ q _ ↦ by simp

theorem add (hφ : HolderOnPar C α φ S) (hψ : HolderOnPar C' α ψ S) :
    HolderOnPar (C + C') α (fun p ↦ φ p + ψ p) S := by
  intro p hp q hq
  calc |φ p + ψ p - (φ q + ψ q)| = |(φ p - φ q) + (ψ p - ψ q)| := by ring_nf
    _ ≤ |φ p - φ q| + |ψ p - ψ q| := abs_add_le _ _
    _ ≤ C * pdist p q ^ α + C' * pdist p q ^ α := add_le_add (hφ p hp q hq) (hψ p hp q hq)
    _ = (C + C') * pdist p q ^ α := by ring

theorem neg (hφ : HolderOnPar C α φ S) : HolderOnPar C α (fun p ↦ -φ p) S := by
  intro p hp q hq
  rw [neg_sub_neg, abs_sub_comm]
  exact hφ p hp q hq

theorem sub (hφ : HolderOnPar C α φ S) (hψ : HolderOnPar C' α ψ S) :
    HolderOnPar (C + C') α (fun p ↦ φ p - ψ p) S := by
  simpa only [sub_eq_add_neg] using hφ.add hψ.neg

theorem const_mul (hφ : HolderOnPar C α φ S) (c : ℝ) :
    HolderOnPar (|c| * C) α (fun p ↦ c * φ p) S := by
  intro p hp q hq
  rw [← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hφ p hp q hq) (abs_nonneg c)

/-- Products of bounded Hölder functions. -/
theorem mul {B : ℝ} (hφ : HolderOnPar C α φ S) (hψ : HolderOnPar C' α ψ S)
    (hφB : ∀ p ∈ S, |φ p| ≤ B) (hψB : ∀ p ∈ S, |ψ p| ≤ B) :
    HolderOnPar (B * (C + C')) α (fun p ↦ φ p * ψ p) S := by
  intro p hp q hq
  have hB : 0 ≤ B := (abs_nonneg _).trans (hφB p hp)
  have h1 := hφ p hp q hq
  have h2 := hψ p hp q hq
  calc |φ p * ψ p - φ q * ψ q| = |φ p * (ψ p - ψ q) + ψ q * (φ p - φ q)| := by ring_nf
    _ ≤ |φ p| * |ψ p - ψ q| + |ψ q| * |φ p - φ q| := by
      rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ B * (C' * pdist p q ^ α) + B * (C * pdist p q ^ α) := by
      gcongr
      · exact hφB p hp
      · exact hψB q hq
    _ = B * (C + C') * pdist p q ^ α := by ring

/-- A Hölder function on a set of `pdist`-diameter `≤ D` is bounded. -/
theorem abs_le {D : ℝ} (h : HolderOnPar C α φ S) (hC : 0 ≤ C) (hα : 0 ≤ α) {p₀ : E d × ℝ}
    (hp₀ : p₀ ∈ S) (hD : ∀ p ∈ S, ∀ q ∈ S, pdist p q ≤ D) :
    ∀ p ∈ S, |φ p| ≤ |φ p₀| + C * D ^ α := by
  intro p hp
  have h1 := h p hp p₀ hp₀
  have h2 : C * pdist p p₀ ^ α ≤ C * D ^ α := by
    gcongr
    · exact pdist_nonneg _ _
    · exact hD p hp p₀ hp₀
  have h3 : |φ p| ≤ |φ p₀| + |φ p - φ p₀| := by
    calc |φ p| = |φ p₀ + (φ p - φ p₀)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith

/-- Composition: `p ↦ f p.1 (φ p)` for `f` `β`-Hölder in `x` uniformly in `z` and `L`-Lipschitz in
`z`, on a set of `pdist`-diameter `≤ D`. -/
theorem comp_holder {U : Set (E d)} {f : E d → ℝ → ℝ} {K L D : ℝ}
    (hφ : HolderOnPar C α φ S) (hC : 0 ≤ C) (hα : 0 < α) (hβ : 0 < β) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hSU : ∀ p ∈ S, p.1 ∈ U) (hD : ∀ p ∈ S, ∀ q ∈ S, pdist p q ≤ D)
    (hfx : ∀ x ∈ U, ∀ y ∈ U, ∀ z, |f x z - f y z| ≤ K * dist x y ^ β)
    (hfz : ∀ x ∈ U, ∀ z w, |f x z - f x w| ≤ L * |z - w|) :
    HolderOnPar (K * D ^ (β - min α β) + L * C * D ^ (α - min α β)) (min α β)
      (fun p ↦ f p.1 (φ p)) S := by
  intro p hp q hq
  have hγ : 0 < min α β := lt_min hα hβ
  set s := pdist p q
  have hs : 0 ≤ s := pdist_nonneg p q
  have hsD : s ≤ D := hD p hp q hq
  have e1 : |f p.1 (φ p) - f q.1 (φ p)| ≤ K * s ^ β := by
    refine (hfx _ (hSU p hp) _ (hSU q hq) _).trans ?_
    gcongr
    exact dist_fst_le_pdist p q
  have e2 : |f q.1 (φ p) - f q.1 (φ q)| ≤ L * (C * s ^ α) := by
    refine (hfz _ (hSU q hq) _ _).trans ?_
    gcongr
    exact hφ p hp q hq
  have r1 := rpow_le_rpow_sub_mul_rpow hs hsD hγ (min_le_right α β)
  have r2 := rpow_le_rpow_sub_mul_rpow hs hsD hγ (min_le_left α β)
  calc |f p.1 (φ p) - f q.1 (φ q)|
      = |(f p.1 (φ p) - f q.1 (φ p)) + (f q.1 (φ p) - f q.1 (φ q))| := by ring_nf
    _ ≤ |f p.1 (φ p) - f q.1 (φ p)| + |f q.1 (φ p) - f q.1 (φ q)| := abs_add_le _ _
    _ ≤ K * s ^ β + L * (C * s ^ α) := add_le_add e1 e2
    _ ≤ K * (D ^ (β - min α β) * s ^ min α β) + L * (C * (D ^ (α - min α β) * s ^ min α β)) := by
      gcongr
    _ = _ := by ring

/-- The case `β = 1` of `comp_holder`. -/
theorem comp_lipschitz {F : E d × ℝ → ℝ → ℝ} {L D : ℝ} (hφ : HolderOnPar C α φ S)
    (hα : 0 < α ∧ α ≤ 1) (hL : 0 ≤ L) (hD : ∀ p ∈ S, ∀ q ∈ S, pdist p q ≤ D)
    (hF : ∀ p ∈ S, ∀ q ∈ S, ∀ z w, |F p z - F q w| ≤ L * (‖p.1 - q.1‖ + |z - w|)) :
    HolderOnPar (L * (D ^ (1 - α) + C)) α (fun p ↦ F p (φ p)) S := by
  intro p hp q hq
  set s := pdist p q
  have hs : 0 ≤ s := pdist_nonneg p q
  have r1 := rpow_le_rpow_sub_mul_rpow hs (hD p hp q hq) hα.1 hα.2
  rw [Real.rpow_one] at r1
  calc |F p (φ p) - F q (φ q)| ≤ L * (‖p.1 - q.1‖ + |φ p - φ q|) := hF p hp q hq _ _
    _ ≤ L * (D ^ (1 - α) * s ^ α + C * s ^ α) := by
      gcongr
      · exact (norm_fst_sub_le_pdist p q).trans r1
      · exact hφ p hp q hq
    _ = _ := by ring

end HolderOnPar

/-- Lipschitz in `x` and in `t` on a box `B ×ˢ J` of `pdist`-diameter `≤ D` implies `α`-Hölder
(`0 < α ≤ 1`). False for general sets (the corner point is needed). -/
theorem holderOnPar_of_lipschitz {B : Set (E d)} {J : Set ℝ} {φ : E d × ℝ → ℝ} {G At D α : ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hG : 0 ≤ G) (hAt : 0 ≤ At) (hD : 0 < D)
    (hDS : ∀ p ∈ B ×ˢ J, ∀ q ∈ B ×ˢ J, pdist p q ≤ D)
    (hx : ∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ J, |φ (x, t) - φ (y, t)| ≤ G * ‖x - y‖)
    (ht : ∀ y ∈ B, ∀ t ∈ J, ∀ s ∈ J, |φ (y, t) - φ (y, s)| ≤ At * |t - s|) :
    HolderOnPar ((G + At * D) * D ^ (1 - α)) α φ (B ×ˢ J) := by
  rintro ⟨x, t⟩ ⟨hx', ht'⟩ ⟨y, s⟩ ⟨hy', hs'⟩
  set δ := pdist (x, t) (y, s)
  have hδ : 0 ≤ δ := pdist_nonneg _ _
  have hδD : δ ≤ D := hDS _ ⟨hx', ht'⟩ _ ⟨hy', hs'⟩
  have e1 : ‖x - y‖ ≤ δ := norm_fst_sub_le_pdist (x, t) (y, s)
  have e2 : |t - s| ≤ δ ^ 2 := abs_snd_sub_le_pdist_sq (x, t) (y, s)
  have r1 := rpow_le_rpow_sub_mul_rpow hδ hδD hα.1 hα.2
  rw [Real.rpow_one] at r1
  calc |φ (x, t) - φ (y, s)| = |(φ (x, t) - φ (y, t)) + (φ (y, t) - φ (y, s))| := by ring_nf
    _ ≤ |φ (x, t) - φ (y, t)| + |φ (y, t) - φ (y, s)| := abs_add_le _ _
    _ ≤ G * ‖x - y‖ + At * |t - s| := add_le_add (hx x hx' y hy' t ht') (ht y hy' t ht' s hs')
    _ ≤ G * δ + At * (D * δ) := by
      gcongr
      calc |t - s| ≤ δ ^ 2 := e2
        _ = δ * δ := sq δ
        _ ≤ D * δ := by gcongr
    _ = (G + At * D) * δ := by ring
    _ ≤ (G + At * D) * (D ^ (1 - α) * δ ^ α) := by gcongr
    _ = _ := by ring

/-- Near pairs / far pairs: a Hölder bound for pairs at `pdist` distance in `(0, η)` and a sup
bound `|φ| ≤ B` give a global Hölder bound on `S` (`0 ≤ α`). -/
theorem HolderOnPar.of_near_far {φ : E d × ℝ → ℝ} {S : Set (E d × ℝ)} {C η B α : ℝ} (hη : 0 < η)
    (hα : 0 ≤ α) (hB : ∀ p ∈ S, |φ p| ≤ B)
    (hnear : ∀ p ∈ S, ∀ q ∈ S, 0 < pdist p q → pdist p q < η → |φ p - φ q| ≤ C * pdist p q ^ α) :
    HolderOnPar (max C (2 * B * η ^ (-α))) α φ S := by
  intro p hp q hq
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB p hp)
  rcases (pdist_nonneg p q).eq_or_lt with h0 | h0
  · rw [pdist_eq_zero.1 h0.symm, sub_self, abs_zero]
    exact mul_nonneg ((by positivity : (0:ℝ) ≤ 2 * B * η ^ (-α)).trans (le_max_right _ _))
      (Real.rpow_nonneg (pdist_nonneg _ _) _)
  have hpd : 0 ≤ pdist p q ^ α := Real.rpow_nonneg (pdist_nonneg p q) _
  by_cases hnq : pdist p q < η
  · exact (hnear p hp q hq h0 hnq).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpd)
  · push Not at hnq
    have h1 : 1 ≤ η ^ (-α) * pdist p q ^ α := by
      rw [Real.rpow_neg hη.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow hη.le hnq hα
    have h2 : |φ p - φ q| ≤ 2 * B := by
      have := abs_sub (φ p) (φ q)
      linarith [hB p hp, hB q hq]
    calc |φ p - φ q| ≤ 2 * B * (η ^ (-α) * pdist p q ^ α) := by nlinarith
      _ = 2 * B * η ^ (-α) * pdist p q ^ α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpd

/-! ### Local Hölder classes: algebra -/

namespace LocHolderOnPar

variable {α β : ℝ} {φ ψ : E d × ℝ → ℝ} {Ω Ω' : Set (E d × ℝ)}

theorem mono (h : LocHolderOnPar α φ Ω) (hΩ : Ω' ⊆ Ω) : LocHolderOnPar α φ Ω' :=
  fun K hK hKc ↦ h K (hK.trans hΩ) hKc

/-- On a compact set, the Hölder constant may be taken nonnegative. -/
theorem exists_nonneg (h : LocHolderOnPar α φ Ω) {K : Set (E d × ℝ)} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : ∃ C, 0 ≤ C ∧ HolderOnPar C α φ K := by
  obtain ⟨C, hC⟩ := h K hK hKc
  exact ⟨max C 0, le_max_right _ _, hC.max_zero⟩

/-- A locally Hölder function (`0 ≤ α`) is bounded on compact subsets. -/
theorem exists_abs_le (h : LocHolderOnPar α φ Ω) (hα : 0 ≤ α) {K : Set (E d × ℝ)} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : ∃ B, ∀ p ∈ K, |φ p| ≤ B := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨0, by simp⟩
  obtain ⟨C, hC, hCK⟩ := h.exists_nonneg hK hKc
  obtain ⟨D, -, hD⟩ := exists_pdist_le_of_isCompact hKc
  exact ⟨_, hCK.abs_le hC hα hp₀ hD⟩

theorem mono_exponent (h : LocHolderOnPar α φ Ω) (hβ : 0 < β) (hβα : β ≤ α) :
    LocHolderOnPar β φ Ω := by
  intro K hK hKc
  obtain ⟨C, hC, hCK⟩ := h.exists_nonneg hK hKc
  obtain ⟨D, -, hD⟩ := exists_pdist_le_of_isCompact hKc
  exact ⟨_, hCK.mono_exponent hC hβ hβα hD⟩

theorem const (c α : ℝ) (Ω : Set (E d × ℝ)) : LocHolderOnPar α (fun _ ↦ c) Ω :=
  fun K _ _ ↦ ⟨0, HolderOnPar.const c α K⟩

theorem add (hφ : LocHolderOnPar α φ Ω) (hψ : LocHolderOnPar α ψ Ω) :
    LocHolderOnPar α (fun p ↦ φ p + ψ p) Ω := by
  intro K hK hKc
  obtain ⟨C, hC⟩ := hφ K hK hKc
  obtain ⟨C', hC'⟩ := hψ K hK hKc
  exact ⟨_, hC.add hC'⟩

theorem neg (hφ : LocHolderOnPar α φ Ω) : LocHolderOnPar α (fun p ↦ -φ p) Ω := by
  intro K hK hKc
  obtain ⟨C, hC⟩ := hφ K hK hKc
  exact ⟨_, hC.neg⟩

theorem sub (hφ : LocHolderOnPar α φ Ω) (hψ : LocHolderOnPar α ψ Ω) :
    LocHolderOnPar α (fun p ↦ φ p - ψ p) Ω := by
  intro K hK hKc
  obtain ⟨C, hC⟩ := hφ K hK hKc
  obtain ⟨C', hC'⟩ := hψ K hK hKc
  exact ⟨_, hC.sub hC'⟩

theorem const_mul (hφ : LocHolderOnPar α φ Ω) (c : ℝ) :
    LocHolderOnPar α (fun p ↦ c * φ p) Ω := by
  intro K hK hKc
  obtain ⟨C, hC⟩ := hφ K hK hKc
  exact ⟨_, hC.const_mul c⟩

/-- Products: no boundedness hypothesis is needed (Hölder functions are bounded on compacts). -/
theorem mul (hα : 0 ≤ α) (hφ : LocHolderOnPar α φ Ω) (hψ : LocHolderOnPar α ψ Ω) :
    LocHolderOnPar α (fun p ↦ φ p * ψ p) Ω := by
  intro K hK hKc
  obtain ⟨C, hC⟩ := hφ K hK hKc
  obtain ⟨C', hC'⟩ := hψ K hK hKc
  obtain ⟨B, hB⟩ := hφ.exists_abs_le hα hK hKc
  obtain ⟨B', hB'⟩ := hψ.exists_abs_le hα hK hKc
  exact ⟨_, hC.mul hC' (fun p hp ↦ (hB p hp).trans (le_max_left B B'))
    (fun p hp ↦ (hB' p hp).trans (le_max_right B B'))⟩

/-- Composition: if `f` is `β`-Hölder in `x ∈ U` uniformly in `z` and Lipschitz in `z`, and `φ` is
locally `α`-Hölder on `Ω` (with `p.1 ∈ U` on `Ω`), then `p ↦ f p.1 (φ p)` is locally
`min α β`-Hölder on `Ω`. -/
theorem comp_holder {U : Set (E d)} {f : E d → ℝ → ℝ} {K L : ℝ}
    (hφ : LocHolderOnPar α φ Ω) (hα : 0 < α) (hβ : 0 < β) (hΩU : ∀ p ∈ Ω, p.1 ∈ U)
    (hfx : ∀ x ∈ U, ∀ y ∈ U, ∀ z, |f x z - f y z| ≤ K * dist x y ^ β)
    (hfz : ∀ x ∈ U, ∀ z w, |f x z - f x w| ≤ L * |z - w|) :
    LocHolderOnPar (min α β) (fun p ↦ f p.1 (φ p)) Ω := by
  intro S hS hSc
  obtain ⟨C, hC, hCS⟩ := hφ.exists_nonneg hS hSc
  obtain ⟨D, -, hD⟩ := exists_pdist_le_of_isCompact hSc
  refine ⟨_, hCS.comp_holder hC hα hβ (le_max_right K 0) (le_max_right L 0)
    (fun p hp ↦ hΩU p (hS hp)) hD (fun x hx y hy z ↦ (hfx x hx y hy z).trans ?_)
    (fun x hx z w ↦ (hfz x hx z w).trans ?_)⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)

/-- The case `β = 1` of `comp_holder`: composition with `F` Lipschitz in `x` and in `z`. -/
theorem comp_lipschitz {F : E d × ℝ → ℝ → ℝ} {L : ℝ} (hφ : LocHolderOnPar α φ Ω)
    (hα : 0 < α ∧ α ≤ 1)
    (hF : ∀ p ∈ Ω, ∀ q ∈ Ω, ∀ z w, |F p z - F q w| ≤ L * (‖p.1 - q.1‖ + |z - w|)) :
    LocHolderOnPar α (fun p ↦ F p (φ p)) Ω := by
  intro S hS hSc
  obtain ⟨C, hC, hCS⟩ := hφ.exists_nonneg hS hSc
  obtain ⟨D, -, hD⟩ := exists_pdist_le_of_isCompact hSc
  refine ⟨_, hCS.comp_lipschitz hα (le_max_right L 0) hD
    (fun p hp q hq z w ↦ (hF p (hS hp) q (hS hq) z w).trans ?_)⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- Composition with a `C¹` function of `(p, φ p)` (jointly in space, time and value). -/
theorem comp_contDiff {G : E d × ℝ → ℝ → ℝ} (hφ : LocHolderOnPar α φ Ω) (hα : 0 < α ∧ α ≤ 1)
    (hG : ContDiff ℝ 1 (fun z : (E d × ℝ) × ℝ ↦ G z.1 z.2)) :
    LocHolderOnPar α (fun p ↦ G p (φ p)) Ω := by
  intro S hS hSc
  obtain ⟨C, hC, hCS⟩ := hφ.exists_nonneg hS hSc
  obtain ⟨D, hD0, hD⟩ := exists_pdist_le_of_isCompact hSc
  obtain ⟨B, hB⟩ := hφ.exists_abs_le hα.1.le hS hSc
  obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall 0
  obtain ⟨Lnn, hLip⟩ := (ContDiff.locallyLipschitz hG |>.locallyLipschitzOn
    (s := Metric.closedBall 0 (max R B))).exists_lipschitzOnWith_of_compact
      (isCompact_closedBall _ _)
  set L : ℝ := (Lnn : ℝ)
  have hL : 0 ≤ L := Lnn.2
  have hmem : ∀ p ∈ S, (p, φ p) ∈ Metric.closedBall (0 : (E d × ℝ) × ℝ) (max R B) := by
    intro p hp
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le ?_ ?_
    · exact (mem_closedBall_zero_iff.1 (hR hp)).trans (le_max_left _ _)
    · rw [Real.norm_eq_abs]; exact (hB p hp).trans (le_max_right _ _)
  refine ⟨L * ((1 + D) * D ^ (1 - α) + C), fun p hp q hq ↦ ?_⟩
  set s := pdist p q
  have hs : 0 ≤ s := pdist_nonneg p q
  have hsD : s ≤ D := hD p hp q hq
  have r1 := rpow_le_rpow_sub_mul_rpow hs hsD hα.1 hα.2
  rw [Real.rpow_one] at r1
  have hlip := hLip.dist_le_mul _ (hmem p hp) _ (hmem q hq)
  simp only [dist_eq_norm, Real.norm_eq_abs] at hlip
  have hpq : ‖p - q‖ ≤ (1 + D) * s := by
    refine (norm_sub_le_max_pdist p q).trans (max_le ?_ ?_)
    · nlinarith
    · rw [sq]; nlinarith
  have hnorm : ‖(p, φ p) - (q, φ q)‖ ≤ (1 + D) * s + C * s ^ α := by
    rw [Prod.mk_sub_mk, Prod.norm_def, Real.norm_eq_abs]
    refine max_le (hpq.trans (le_add_of_nonneg_right (by positivity))) ?_
    exact (hCS p hp q hq).trans (le_add_of_nonneg_left (by positivity))
  calc |G p (φ p) - G q (φ q)| ≤ L * ‖(p, φ p) - (q, φ q)‖ := hlip
    _ ≤ L * ((1 + D) * (D ^ (1 - α) * s ^ α) + C * s ^ α) := by
      gcongr
      refine hnorm.trans ?_
      gcongr
    _ = _ := by ring

/-- Local Hölder bounds near every point give `LocHolderOnPar` (`φ` continuous on `Ω`, `0 ≤ α`). -/
theorem of_local (hα : 0 ≤ α) (hφ : ContinuousOn φ Ω)
    (h : ∀ p ∈ Ω, ∃ N ∈ 𝓝 p, ∃ C, HolderOnPar C α φ (N ∩ Ω)) : LocHolderOnPar α φ Ω := by
  intro K hK hKc
  choose! N hN C hC using h
  -- open sets `O p ⊆ N p` containing `p`
  have hO : ∀ p ∈ K, ∃ O, O ⊆ N p ∧ IsOpen O ∧ p ∈ O := fun p hp ↦
    mem_nhds_iff.1 (hN p (hK hp))
  choose! O hON hOo hpO using hO
  obtain ⟨t, hcov⟩ := hKc.elim_finite_subcover (fun i : K ↦ O i) (fun i ↦ hOo i i.2)
    (fun p hp ↦ mem_iUnion.2 ⟨⟨p, hp⟩, hpO p hp⟩)
  obtain ⟨δ, hδ, hδcov⟩ := lebesgue_number_lemma_of_metric (c := fun i : t ↦ O i.1) hKc
    (fun i ↦ hOo _ i.1.2) (fun p hp ↦ by
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 (hcov hp)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hpi⟩)
  obtain ⟨S, hS⟩ := hKc.exists_bound_of_continuousOn (hφ.mono hK)
  set η := min δ 1
  have hη : 0 < η := lt_min hδ one_pos
  set C₀ : ℝ := ∑ i ∈ t, max (C i.1) 0
  refine ⟨C₀ + 2 * max S 0 * η ^ (-α), fun p hp q hq ↦ ?_⟩
  have hpd : 0 ≤ pdist p q ^ α := Real.rpow_nonneg (pdist_nonneg p q) _
  have hηS : 0 ≤ 2 * max S 0 * η ^ (-α) := by positivity
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  by_cases hpq : dist q p < δ
  · obtain ⟨⟨i, hi⟩, hball⟩ := hδcov p hp
    have hpi : p ∈ N i ∩ Ω := ⟨hON i i.2 (hball (Metric.mem_ball_self hδ)), hK hp⟩
    have hqi : q ∈ N i ∩ Ω := ⟨hON i i.2 (hball (Metric.mem_ball.2 hpq)), hK hq⟩
    have hCi : C i ≤ C₀ := (le_max_left _ _).trans
      (Finset.single_le_sum (f := fun i : K ↦ max (C i.1) 0) (fun j _ ↦ le_max_right _ _) hi)
    calc |φ p - φ q| ≤ C i * pdist p q ^ α := hC i (hK i.2) p hpi q hqi
      _ ≤ C₀ * pdist p q ^ α := mul_le_mul_of_nonneg_right hCi hpd
      _ ≤ _ := by nlinarith
  · push Not at hpq
    have hηpd : η ≤ pdist p q := le_pdist_of_le_dist (min_le_right _ _)
      ((min_le_left _ _).trans (by rwa [dist_comm]))
    have h1 : 1 ≤ η ^ (-α) * pdist p q ^ α := by
      rw [Real.rpow_neg hη.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow hη.le hηpd hα
    have hφpq : |φ p - φ q| ≤ 2 * max S 0 := by
      have := abs_sub (φ p) (φ q)
      have h1 := (hS p hp).trans (le_max_left S 0)
      have h2 := (hS q hq).trans (le_max_left S 0)
      rw [Real.norm_eq_abs] at h1 h2
      linarith
    calc |φ p - φ q| ≤ 2 * max S 0 * (η ^ (-α) * pdist p q ^ α) := by
          nlinarith [le_max_right S 0]
      _ ≤ _ := by nlinarith

/-- A locally Hölder function (`0 < α`) on an open set is continuous there. -/
theorem continuousOn (h : LocHolderOnPar α φ Ω) (hΩ : IsOpen Ω) (hα : 0 < α) :
    ContinuousOn φ Ω := by
  intro p hp
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ p hp
  have hK : Metric.closedBall p (r / 2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrΩ
  obtain ⟨C, hC⟩ := h _ hK (isCompact_closedBall _ _)
  refine (ContinuousAt.continuousWithinAt ?_)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun q ↦ C * pdist q p ^ α) (𝓝 p) (𝓝 0) := by
    have : ContinuousAt (fun q ↦ C * pdist q p ^ α) p :=
      continuousAt_const.mul (Continuous.rpow_const (continuous_pdist_left p)
        (fun _ ↦ Or.inr hα.le)).continuousAt
    simpa [ContinuousAt, Real.zero_rpow hα.ne'] using this
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [Metric.closedBall_mem_nhds p (half_pos hr)] with q hq
  rw [Real.norm_eq_abs]
  exact hC q hq p (Metric.mem_closedBall_self (half_pos hr).le)

end LocHolderOnPar

/-! ### The existential-exponent class -/

namespace LocHolder

variable {φ ψ : E d × ℝ → ℝ} {Ω Ω' : Set (E d × ℝ)}

theorem mono (h : LocHolder φ Ω) (hΩ : Ω' ⊆ Ω) : LocHolder φ Ω' := by
  obtain ⟨α, hα, h⟩ := h
  exact ⟨α, hα, h.mono hΩ⟩

theorem const (c : ℝ) (Ω : Set (E d × ℝ)) : LocHolder (fun _ ↦ c) Ω :=
  ⟨1 / 2, ⟨by norm_num, by norm_num⟩, LocHolderOnPar.const c _ Ω⟩

/-- Two locally Hölder functions are locally Hölder with a common exponent. -/
theorem common (hφ : LocHolder φ Ω) (hψ : LocHolder ψ Ω) :
    ∃ α ∈ Ioo (0 : ℝ) 1, LocHolderOnPar α φ Ω ∧ LocHolderOnPar α ψ Ω := by
  obtain ⟨α, hα, hφ⟩ := hφ
  obtain ⟨β, hβ, hψ⟩ := hψ
  refine ⟨min α β, ⟨lt_min hα.1 hβ.1, (min_le_left _ _).trans_lt hα.2⟩,
    hφ.mono_exponent (lt_min hα.1 hβ.1) (min_le_left _ _),
    hψ.mono_exponent (lt_min hα.1 hβ.1) (min_le_right _ _)⟩

theorem add (hφ : LocHolder φ Ω) (hψ : LocHolder ψ Ω) : LocHolder (fun p ↦ φ p + ψ p) Ω := by
  obtain ⟨α, hα, h1, h2⟩ := hφ.common hψ
  exact ⟨α, hα, h1.add h2⟩

theorem sub (hφ : LocHolder φ Ω) (hψ : LocHolder ψ Ω) : LocHolder (fun p ↦ φ p - ψ p) Ω := by
  obtain ⟨α, hα, h1, h2⟩ := hφ.common hψ
  exact ⟨α, hα, h1.sub h2⟩

theorem mul (hφ : LocHolder φ Ω) (hψ : LocHolder ψ Ω) : LocHolder (fun p ↦ φ p * ψ p) Ω := by
  obtain ⟨α, hα, h1, h2⟩ := hφ.common hψ
  exact ⟨α, hα, h1.mul hα.1.le h2⟩

theorem comp_contDiff {G : E d × ℝ → ℝ → ℝ} (hφ : LocHolder φ Ω)
    (hG : ContDiff ℝ 1 (fun z : (E d × ℝ) × ℝ ↦ G z.1 z.2)) :
    LocHolder (fun p ↦ G p (φ p)) Ω := by
  obtain ⟨α, hα, h⟩ := hφ
  exact ⟨α, hα, h.comp_contDiff ⟨hα.1, hα.2.le⟩ hG⟩

end LocHolder

end ParabolicBasic
