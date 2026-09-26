/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Viscosity.Basic
public import ParabolicBasic.Viscosity.SliceAux

/-!
# Exponential change of unknown

* `UpperSemicontinuousOn.mul_continuousOn_pos` (and the LSC mirror): a USC function times a
  positive continuous function is USC (a Mathlib gap);
* `IsViscSubOn.exp_change` (and the super mirror): if `u` is a subsolution for `F`, then
  `w := e^{-λt} u` is a subsolution for `F_λ p r := λ r + e^{-λt} F p (e^{λt} r)`;
* `IsViscSubOn.congr_source_graph` (and the super mirror): the source enters only through its
  values on the graph `(p, u p)`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

section Semicontinuity

variable {X : Type*} [TopologicalSpace X]

/-- A USC function times a positive continuous function is USC. -/
theorem UpperSemicontinuousOn.mul_continuousOn_pos {s : Set X} {u c : X → ℝ}
    (hu : UpperSemicontinuousOn u s) (hc : ContinuousOn c s) (hpos : ∀ p ∈ s, 0 < c p) :
    UpperSemicontinuousOn (fun p ↦ c p * u p) s := by
  intro x hx y hy
  have hcx := hpos x hx
  have h1 : u x < y / c x := by rw [lt_div_iff₀ hcx, mul_comm]; exact hy
  obtain ⟨y', h1', h2'⟩ := exists_between h1
  have h3 : c x * y' < y := by rw [lt_div_iff₀ hcx, mul_comm] at h2'; exact h2'
  have hev1 := upperSemicontinuousWithinAt_iff.1 (hu x hx) y' h1'
  have hev2 : ∀ᶠ x' in 𝓝[s] x, c x' * y' < y :=
    ((hc x hx).mul continuousWithinAt_const).eventually (gt_mem_nhds h3)
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with x' h1 h2 hx'
  exact (mul_lt_mul_of_pos_left h1 (hpos x' hx')).trans h2

/-- An LSC function times a positive continuous function is LSC. -/
theorem LowerSemicontinuousOn.mul_continuousOn_pos {s : Set X} {u c : X → ℝ}
    (hu : LowerSemicontinuousOn u s) (hc : ContinuousOn c s) (hpos : ∀ p ∈ s, 0 < c p) :
    LowerSemicontinuousOn (fun p ↦ c p * u p) s := by
  intro x hx y hy
  have hcx := hpos x hx
  have h1 : y / c x < u x := by rw [div_lt_iff₀ hcx, mul_comm]; exact hy
  obtain ⟨y', h1', h2'⟩ := exists_between h1
  have h3 : y < c x * y' := by rw [div_lt_iff₀ hcx, mul_comm] at h1'; exact h1'
  have hev1 := lowerSemicontinuousWithinAt_iff.1 (hu x hx) y' h2'
  have hev2 : ∀ᶠ x' in 𝓝[s] x, y < c x' * y' :=
    ((hc x hx).mul continuousWithinAt_const).eventually (lt_mem_nhds h3)
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with x' h1 h2 hx'
  exact h2.trans (mul_lt_mul_of_pos_left h1 (hpos x' hx'))

end Semicontinuity

variable {d : ℕ}

/-- `dₜ (e^{λt} ψ) = e^{λt} (λ ψ + dₜ ψ)`. -/
theorem dₜ_exp_mul (lam : ℝ) {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (p : E d × ℝ) :
    dₜ (fun q ↦ Real.exp (lam * q.2) * ψ q) p =
      Real.exp (lam * p.2) * (lam * ψ p + dₜ ψ p) := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ ↦ Real.exp (lam * s)) (Real.exp (lam * p.2) * (lam * 1)) p.2 :=
    ((hasDerivAt_id p.2).const_mul lam).exp
  have h2 := ParabolicBasic.hasDerivAt_sliceT hψd p
  have h : HasDerivAt (fun s : ℝ ↦ Real.exp (lam * s) * ψ (p.1, s)) _ p.2 := h1.mul h2
  change deriv (fun s : ℝ ↦ Real.exp (lam * s) * ψ (p.1, s)) p.2 = _
  rw [h.deriv, ParabolicBasic.dₜ_eq_fderiv hψd p]
  simp only [Prod.mk.eta]
  ring

/-- `lapₓ (e^{λt} ψ) = e^{λt} lapₓ ψ`. -/
theorem lapₓ_exp_mul (lam : ℝ) {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (p : E d × ℝ) :
    lapₓ (fun q ↦ Real.exp (lam * q.2) * ψ q) p = Real.exp (lam * p.2) * lapₓ ψ p := by
  change lapₓ (fun q ↦ Real.exp (lam * p.2) * ψ q) p = _
  exact ParabolicBasic.lapₓ_const_mul hψ _ p

theorem contDiff_exp_mul (lam : ℝ) {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    ContDiff ℝ 2 (fun q : E d × ℝ ↦ Real.exp (lam * q.2) * ψ q) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)).mul hψ

theorem exp_mul_exp_neg_mul (lam t x : ℝ) :
    Real.exp (lam * t) * (Real.exp (-(lam * t)) * x) = x := by
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- **Exponential change of unknown.** -/
theorem IsViscSubOn.exp_change {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (lam : ℝ) (hu : IsViscSubOn Ω F u) :
    IsViscSubOn Ω (fun p r ↦ lam * r + Real.exp (-(lam * p.2)) * F p (Real.exp (lam * p.2) * r))
      (fun p ↦ Real.exp (-(lam * p.2)) * u p) := by
  have hexp : Continuous fun p : E d × ℝ ↦ Real.exp (-(lam * p.2)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_snd).neg
  refine ⟨UpperSemicontinuousOn.mul_continuousOn_pos hu.1 hexp.continuousOn
    fun _ _ ↦ Real.exp_pos _, fun ψ hψ p hp ht ↦ ?_⟩
  obtain ⟨-, hψp, hev⟩ := ht
  have hψp' : ψ p = Real.exp (-(lam * p.2)) * u p := hψp
  have htφ : TouchesAbove (fun q ↦ Real.exp (lam * q.2) * ψ q) u Ω p := by
    refine ⟨hp, ?_, ?_⟩
    · simp only [hψp, exp_mul_exp_neg_mul]
    · filter_upwards [hev] with q hq
      have := mul_le_mul_of_nonneg_left hq (Real.exp_pos (lam * q.2)).le
      rwa [exp_mul_exp_neg_mul] at this
  have key := hu.2 _ (contDiff_exp_mul lam hψ) p hp htφ
  rw [dₜ_exp_mul lam hψ, lapₓ_exp_mul lam hψ] at key
  simp only
  rw [exp_mul_exp_neg_mul, ← hψp']
  set e := Real.exp (lam * p.2)
  set e' := Real.exp (-(lam * p.2))
  have hee' : e' * e = 1 := by
    simp only [e, e', ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 := mul_le_mul_of_nonneg_left key (Real.exp_pos (-(lam * p.2))).le
  rw [mul_zero] at h2
  have h3 : e' * (e * (lam * ψ p + dₜ ψ p) - e * lapₓ ψ p + F p (u p)) =
      (e' * e) * (lam * ψ p + dₜ ψ p) - (e' * e) * lapₓ ψ p + e' * F p (u p) := by ring
  rw [h3, hee'] at h2
  linarith

/-- **Exponential change of unknown**, supersolution mirror. -/
theorem IsViscSuperOn.exp_change {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (lam : ℝ) (hu : IsViscSuperOn Ω F u) :
    IsViscSuperOn Ω
      (fun p r ↦ lam * r + Real.exp (-(lam * p.2)) * F p (Real.exp (lam * p.2) * r))
      (fun p ↦ Real.exp (-(lam * p.2)) * u p) := by
  have hexp : Continuous fun p : E d × ℝ ↦ Real.exp (-(lam * p.2)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_snd).neg
  refine ⟨LowerSemicontinuousOn.mul_continuousOn_pos hu.1 hexp.continuousOn
    fun _ _ ↦ Real.exp_pos _, fun ψ hψ p hp ht ↦ ?_⟩
  obtain ⟨-, hψp, hev⟩ := ht
  have hψp' : ψ p = Real.exp (-(lam * p.2)) * u p := hψp
  have htφ : TouchesBelow (fun q ↦ Real.exp (lam * q.2) * ψ q) u Ω p := by
    refine ⟨hp, ?_, ?_⟩
    · simp only [hψp, exp_mul_exp_neg_mul]
    · filter_upwards [hev] with q hq
      have := mul_le_mul_of_nonneg_left hq (Real.exp_pos (lam * q.2)).le
      rwa [exp_mul_exp_neg_mul] at this
  have key := hu.2 _ (contDiff_exp_mul lam hψ) p hp htφ
  rw [dₜ_exp_mul lam hψ, lapₓ_exp_mul lam hψ] at key
  simp only
  rw [exp_mul_exp_neg_mul, ← hψp']
  set e := Real.exp (lam * p.2)
  set e' := Real.exp (-(lam * p.2))
  have hee' : e' * e = 1 := by
    simp only [e, e', ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 := mul_le_mul_of_nonneg_left key (Real.exp_pos (-(lam * p.2))).le
  rw [mul_zero] at h2
  have h3 : e' * (e * (lam * ψ p + dₜ ψ p) - e * lapₓ ψ p + F p (u p)) =
      (e' * e) * (lam * ψ p + dₜ ψ p) - (e' * e) * lapₓ ψ p + e' * F p (u p) := by ring
  rw [h3, hee'] at h2
  linarith

/-- **Graph congruence.** A subsolution only sees the source on its graph. -/
theorem IsViscSubOn.congr_source_graph {Ω : Set (E d × ℝ)} {F F' : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (h : ∀ p ∈ Ω, F' p (u p) = F p (u p)) :
    IsViscSubOn Ω F u ↔ IsViscSubOn Ω F' u :=
  ⟨fun hu ↦ ⟨hu.1, fun ψ hψ p hp ht ↦ by rw [h p hp]; exact hu.2 ψ hψ p hp ht⟩,
    fun hu ↦ ⟨hu.1, fun ψ hψ p hp ht ↦ by rw [← h p hp]; exact hu.2 ψ hψ p hp ht⟩⟩

/-- **Graph congruence**, supersolution mirror. -/
theorem IsViscSuperOn.congr_source_graph {Ω : Set (E d × ℝ)} {F F' : E d × ℝ → ℝ → ℝ}
    {v : E d × ℝ → ℝ} (h : ∀ p ∈ Ω, F' p (v p) = F p (v p)) :
    IsViscSuperOn Ω F v ↔ IsViscSuperOn Ω F' v :=
  ⟨fun hv ↦ ⟨hv.1, fun ψ hψ p hp ht ↦ by rw [h p hp]; exact hv.2 ψ hψ p hp ht⟩,
    fun hv ↦ ⟨hv.1, fun ψ hψ p hp ht ↦ by rw [← h p hp]; exact hv.2 ψ hψ p hp ht⟩⟩

end ParabolicBasic
