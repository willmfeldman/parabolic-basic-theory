/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Barriers.Radial
public import ParabolicBasic.Barriers.ExteriorSphere
public import ParabolicBasic.Comparison.Parabolic

/-!
# Lateral and initial heat barriers

Both barriers are *separable*, `w(x, t) = φ x + τ t`, which makes their heat operator explicit
(`dₜ_const_add_mul_sep`, `lapₓ_const_add_mul_sep`). `IsSepBarrier V a b z φ τ` records what the
semilinear construction (`Barriers/Perron.lean`) needs of `w`: regularity, `dₜw - Δₓw ≥ 1` on the
open cylinder, `w(z) = 0` and `w > 0` on the rest of the parabolic boundary.

* Lateral (`isSepBarrier_lateral`), at `z = (ξ, s)`, `ξ ∈ frontier V` with exterior sphere
  `(y, R)`: `φ x = A ((R²)⁻ᵈ - (‖x - y‖²)⁻ᵈ)` (the profile `R^{-k} - ‖x - y‖^{-k}` with `k = 2d`),
  `τ t = (t - s)²`; `Δ(‖x - y‖²)⁻ᵈ = 2d(d + 2)(‖x - y‖²)^{-(d+1)}`.
* Initial (`isSepBarrier_initial`), at `z = (ξ, a)`: `φ x = ‖x - ξ‖²`, `τ t = (2d + 1)(t - a)`;
  `dₜw - Δₓw = (2d + 1) - 2d = 1`, valid for `d = 0`.
-/

@[expose] public section

open Set Metric
open scoped Laplacian ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Separable functions -/

/-- Time derivative of `c + K (φ x + τ t)`. -/
theorem dₜ_const_add_mul_sep (φ : E d → ℝ) {τ : ℝ → ℝ} (c K : ℝ) {p : E d × ℝ}
    (hτ : DifferentiableAt ℝ τ p.2) :
    dₜ (fun q ↦ c + K * (φ q.1 + τ q.2)) p = K * deriv τ p.2 :=
  (((hτ.hasDerivAt.const_add (φ p.1)).const_mul K).const_add c).deriv

/-- Spatial Laplacian of `c + K (φ x + τ t)`. -/
theorem lapₓ_const_add_mul_sep {φ : E d → ℝ} (τ : ℝ → ℝ) (c K : ℝ) {p : E d × ℝ}
    (hφ : ContDiffAt ℝ 2 φ p.1) :
    lapₓ (fun q ↦ c + K * (φ q.1 + τ q.2)) p = K * Δ φ p.1 := by
  have : (fun y : E d ↦ c + K * (φ y + τ p.2)) = fun y ↦ K * φ y + (c + K * τ p.2) := by
    funext y; ring
  simp only [lapₓ]
  rw [this, laplacian_const_mul_add_const hφ]

/-- A separable heat barrier `w(x, t) = φ x + τ t` at `z` for the cylinder `V × (a, b)`
(the hypotheses on `w` of the semilinear barrier construction). -/
structure IsSepBarrier (V : Set (E d)) (a b : ℝ) (z : E d × ℝ) (φ : E d → ℝ) (τ : ℝ → ℝ) :
    Prop where
  continuousOn : ContinuousOn φ (closure V)
  contDiffOn : ContDiffOn ℝ 2 φ V
  contDiff_time : ContDiff ℝ 2 τ
  heat : ∀ p ∈ V ×ˢ Ioo a b, 1 ≤ deriv τ p.2 - Δ φ p.1
  zero : φ z.1 + τ z.2 = 0
  pos : ∀ q ∈ parBdry V a b, q ≠ z → 0 < φ q.1 + τ q.2

theorem IsSepBarrier.nonneg {V : Set (E d)} {a b : ℝ} {z : E d × ℝ} {φ : E d → ℝ} {τ : ℝ → ℝ}
    (hw : IsSepBarrier V a b z φ τ) {q : E d × ℝ} (hq : q ∈ parBdry V a b) :
    0 ≤ φ q.1 + τ q.2 := by
  by_cases h : q = z
  · rw [h, hw.zero]
  · exact (hw.pos q hq h).le

/-! ### The initial barrier -/

/-- **Initial barrier.** `w(x, t) = ‖x - ξ‖² + (2d + 1)(t - a)` is a barrier at `(ξ, a)`, for
every `ξ` and every `d`, including `d = 0`. -/
theorem isSepBarrier_initial (V : Set (E d)) (a b : ℝ) (ξ : E d) :
    IsSepBarrier V a b (ξ, a) (fun x ↦ ‖x - ξ‖ ^ 2) (fun t ↦ (2 * d + 1) * (t - a)) := by
  have hτ : ContDiff ℝ 2 (fun t : ℝ ↦ (2 * d + 1) * (t - a)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  refine ⟨(contDiff_norm_sub_sq ξ (n := 0)).continuous.continuousOn,
    (contDiff_norm_sub_sq ξ).contDiffOn, hτ, fun p _ ↦ ?_, by simp, fun q hq hqz ↦ ?_⟩
  · have hd : deriv (fun t : ℝ ↦ (2 * d + 1) * (t - a)) p.2 = 2 * d + 1 := by
      have := ((hasDerivAt_id' p.2).sub_const a).const_mul ((2 : ℝ) * d + 1)
      exact this.deriv.trans (by ring)
    rw [hd, laplacian_norm_sub_sq, finrank_euclideanSpace_fin]
    linarith
  · have hqa : a ≤ q.2 := by
      rcases hq with ⟨-, hq2⟩ | ⟨-, hq2⟩
      · exact (mem_singleton_iff.1 hq2).ge
      · exact hq2.1
    have hd0 : (0 : ℝ) ≤ 2 * d + 1 := by positivity
    by_cases h1 : q.1 = ξ
    · have h2 : q.2 ≠ a := fun h2 ↦ hqz (Prod.ext h1 h2)
      have : 0 < (2 * (d : ℝ) + 1) * (q.2 - a) :=
        mul_pos (by positivity) (sub_pos.2 (lt_of_le_of_ne hqa (Ne.symm h2)))
      nlinarith [sq_nonneg ‖q.1 - ξ‖]
    · have : 0 < ‖q.1 - ξ‖ ^ 2 := by
        have := norm_pos_iff.2 (sub_ne_zero.2 h1)
        positivity
      have : 0 ≤ (2 * (d : ℝ) + 1) * (q.2 - a) := mul_nonneg hd0 (sub_nonneg.2 hqa)
      linarith

/-! ### The lateral barrier -/

/-- The spatial profile of the lateral barrier, `A ((R²)⁻ᵈ - (‖x - y‖²)⁻ᵈ)`, i.e.
`A (R^{-k} - ‖x - y‖^{-k})` with `k = 2d`. -/
noncomputable def latProfile (y : E d) (R A : ℝ) (x : E d) : ℝ :=
  A * (((R ^ 2)⁻¹) ^ d - ((‖x - y‖ ^ 2)⁻¹) ^ d)

theorem contDiffAt_latProfile {n : WithTop ℕ∞} (y : E d) (R A : ℝ) {x : E d} (hx : x ≠ y) :
    ContDiffAt ℝ n (latProfile y R A) x :=
  contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_inv_norm_sub_sq_pow d hx))

/-- `Δ` of the lateral profile: `-A · 2d(d + 2) (‖x - y‖²)^{-(d+1)}`. -/
theorem laplacian_latProfile (y : E d) (R A : ℝ) {x : E d} (hx : x ≠ y) :
    Δ (latProfile y R A) x = -(A * (2 * d * (d + 2))) * ((‖x - y‖ ^ 2)⁻¹) ^ (d + 1) := by
  have : latProfile y R A = fun x ↦ (-A) * ((‖x - y‖ ^ 2)⁻¹) ^ d + A * ((R ^ 2)⁻¹) ^ d := by
    funext x; simp only [latProfile]; ring
  rw [this, laplacian_const_mul_add_const (contDiffAt_inv_norm_sub_sq_pow d hx),
    laplacian_inv_norm_sub_sq_pow d hx, finrank_euclideanSpace_fin]
  ring

/-- On `closure V`, the exterior sphere `(y, R)` at `ξ` keeps `x` at distance `≥ R` from `y`. -/
theorem le_dist_of_exteriorSphere {V : Set (E d)} {ξ y : E d} {R : ℝ} (hξy : dist ξ y = R)
    (hext : ∀ x ∈ closure V, x ≠ ξ → R < dist x y) {x : E d} (hx : x ∈ closure V) :
    R ≤ dist x y := by
  by_cases h : x = ξ
  · rw [h, hξy]
  · exact (hext x hx h).le

/-- **Lateral barrier.** At `z = (ξ, s)`, `ξ ∈ frontier V` with an exterior sphere,
`s ∈ [a, b]`, `V` bounded, the lateral barrier `A ((R²)⁻ᵈ - (‖x - y‖²)⁻ᵈ) + (t - s)²` (with
`A = (2(b - a) + 1) (D²)^{d+1} / (2d(d + 2))`, `D ≥ sup_{closure V} ‖x - y‖`) is a separable
barrier. Here `d ≥ 1` since `frontier V ≠ ∅`. -/
theorem isSepBarrier_lateral {V : Set (E d)} (hVb : Bornology.IsBounded V) {a b : ℝ}
    {ξ : E d} (hξ : ξ ∈ frontier V) (hext : ExteriorSphereAt V ξ) {s : ℝ} (hs : s ∈ Icc a b) :
    ∃ φ : E d → ℝ, ∃ τ : ℝ → ℝ, IsSepBarrier V a b (ξ, s) φ τ := by
  obtain ⟨y, R, hR, hξy, hext⟩ := hext
  have hd : 0 < d := pos_of_mem_frontier hξ
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  -- a bound `D` for `‖x - y‖` on `closure V`
  obtain ⟨D₀, hD₀⟩ := (hVb.closure.subset_closedBall y)
  set D := max D₀ R with hD
  have hDpos : 0 < D := lt_of_lt_of_le hR (le_max_right _ _)
  have hxD : ∀ x ∈ closure V, dist x y ≤ D := fun x hx ↦
    (mem_closedBall.1 (hD₀ hx)).trans (le_max_left _ _)
  have hxR : ∀ x ∈ closure V, R ≤ dist x y := fun x hx ↦ le_dist_of_exteriorSphere hξy hext hx
  have hxy : ∀ x ∈ closure V, x ≠ y := fun x hx h ↦ by
    have := hxR x hx
    rw [h, dist_self] at this
    linarith
  set A : ℝ := (2 * (b - a) + 1) * ((D ^ 2) ^ (d + 1)) / (2 * d * (d + 2)) with hA
  have hab : a ≤ b := hs.1.trans hs.2
  have hApos : 0 < A := by rw [hA]; positivity
  refine ⟨latProfile y R A, fun t ↦ (t - s) ^ 2, ?_, ?_, ?_, fun p hp ↦ ?_, ?_, fun q hq hqz ↦ ?_⟩
  · exact fun x hx ↦ (contDiffAt_latProfile (n := 0) y R A (hxy x hx)).continuousAt
      |>.continuousWithinAt
  · exact fun x hx ↦ (contDiffAt_latProfile y R A (hxy x (subset_closure hx))).contDiffWithinAt
  · exact (contDiff_id.sub contDiff_const).pow 2
  · -- the heat computation
    have hx := hxy p.1 (subset_closure hp.1)
    have hτ : deriv (fun t : ℝ ↦ (t - s) ^ 2) p.2 = 2 * (p.2 - s) := by
      have := ((hasDerivAt_id' p.2).sub_const s).pow 2
      exact this.deriv.trans (by norm_num)
    rw [hτ, laplacian_latProfile y R A hx]
    set r2 := ‖p.1 - y‖ ^ 2 with hr2
    have hr2pos : 0 < r2 := by
      have := norm_pos_iff.2 (sub_ne_zero.2 hx)
      positivity
    have hr2D : r2 ≤ D ^ 2 := by
      have := hxD p.1 (subset_closure hp.1)
      rw [dist_eq_norm] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hratio : 1 ≤ (D ^ 2) ^ (d + 1) * (r2⁻¹) ^ (d + 1) := by
      rw [← mul_pow]
      exact one_le_pow₀ (by rw [← div_eq_mul_inv, one_le_div hr2pos]; exact hr2D)
    have hkey : A * (2 * d * (d + 2)) * (r2⁻¹) ^ (d + 1) =
        (2 * (b - a) + 1) * ((D ^ 2) ^ (d + 1) * (r2⁻¹) ^ (d + 1)) := by
      rw [hA]; field_simp
    have h1 : -(2 * (b - a)) ≤ 2 * (p.2 - s) := by linarith [hp.2.1, hs.2]
    have h2 : 2 * (b - a) + 1 ≤ A * (2 * d * (d + 2)) * (r2⁻¹) ^ (d + 1) := by
      rw [hkey]
      have : (0 : ℝ) ≤ 2 * (b - a) + 1 := by linarith
      nlinarith
    linarith
  · simp only [latProfile]
    rw [← dist_eq_norm, hξy]
    ring
  · -- positivity away from `z`
    have hq1 : q.1 ∈ closure V := (parBdry_subset_closure V hab hq).1
    have hlat : 0 ≤ latProfile y R A q.1 := by
      simp only [latProfile]
      refine mul_nonneg hApos.le (sub_nonneg.2 (pow_le_pow_left₀ (by positivity) ?_ d))
      rw [← dist_eq_norm]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hR.le (hxR _ hq1) 2)
    by_cases h1 : q.1 = ξ
    · have h2 : q.2 ≠ s := fun h2 ↦ hqz (Prod.ext h1 h2)
      have : 0 < (q.2 - s) ^ 2 := by
        have := sub_ne_zero.2 h2
        positivity
      linarith
    · have hlt : 0 < latProfile y R A q.1 := by
        simp only [latProfile]
        refine mul_pos hApos (sub_pos.2 (pow_lt_pow_left₀ ?_ (by positivity) hd.ne'))
        rw [← dist_eq_norm]
        exact inv_strictAnti₀ (by positivity) (pow_lt_pow_left₀ (hext _ hq1 h1) hR.le two_ne_zero)
      nlinarith [sq_nonneg (q.2 - s)]

end ParabolicBasic
