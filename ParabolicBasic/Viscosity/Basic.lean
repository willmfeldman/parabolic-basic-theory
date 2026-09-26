/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Viscosity
public import ParabolicBasic.Calculus.Slice

/-!
# Viscosity basics: locality, congruence, monotonicity, negation, max/min

Elementary properties of the standard viscosity notion `IsViscSubOn` / `IsViscSuperOn`,
proved directly in `E d × ℝ`:

* `IsViscSubOn.of_contDiffOn_test`: tests which are only `C²` near the contact point suffice;
* `IsViscSubOn.congr`: only the values on `Ω` matter;
* `IsViscSubOn.mono_source`, `IsViscSubOn.mono_set`, `IsViscSubOn.of_locally`: monotonicity in
  the source and in the set, local-to-global;
* `isViscSubOn_neg_iff`, `isViscSuperOn_neg_iff`: negation exchanges sub- and supersolutions,
  with `F ↦ fun p z ↦ -F p (-z)`;
* `IsViscSubOn.max`, `IsViscSuperOn.min`.

Every supersolution statement is derived from the subsolution statement through the negation
lemma.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Semicontinuity and touching helpers -/

section Helpers

variable {X : Type*} [TopologicalSpace X] {S : Set X} {u v ψ : X → ℝ} {p : X}

theorem upperSemicontinuousOn_iff_lowerSemicontinuousOn_neg :
    UpperSemicontinuousOn u S ↔ LowerSemicontinuousOn (-u) S := by
  simp only [upperSemicontinuousOn_iff, lowerSemicontinuousOn_iff,
    upperSemicontinuousWithinAt_iff, lowerSemicontinuousWithinAt_iff, Pi.neg_apply]
  refine forall₂_congr fun x _ ↦ ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · filter_upwards [h (-y) (by linarith)] with z hz
    linarith
  · filter_upwards [h (-y) (by linarith)] with z hz
    linarith

theorem UpperSemicontinuousOn.congr_eqOn (hu : UpperSemicontinuousOn u S) (h : EqOn u v S) :
    UpperSemicontinuousOn v S := by
  intro x hx y hy
  rw [← h hx] at hy
  filter_upwards [hu x hx y hy, self_mem_nhdsWithin] with z hz hzS
  rwa [← h hzS]

theorem TouchesAbove.congr_eqOn (ht : TouchesAbove ψ u S p) (h : EqOn u v S) :
    TouchesAbove ψ v S p := by
  refine ⟨ht.1, ht.2.1.trans (h ht.1), ?_⟩
  filter_upwards [ht.2.2, self_mem_nhdsWithin] with z hz hzS
  rwa [← h hzS]

theorem touchesBelow_neg_iff :
    TouchesBelow (fun q ↦ -ψ q) (-u) S p ↔ TouchesAbove ψ u S p := by
  simp only [TouchesBelow, TouchesAbove, Pi.neg_apply, neg_inj, neg_le_neg_iff]

theorem touchesAbove_neg_iff :
    TouchesAbove (fun q ↦ -ψ q) (-u) S p ↔ TouchesBelow ψ u S p := by
  simp only [TouchesBelow, TouchesAbove, Pi.neg_apply, neg_inj, neg_le_neg_iff]

theorem touchesAbove_neg_iff' :
    TouchesAbove (fun q ↦ -ψ q) u S p ↔ TouchesBelow ψ (-u) S p := by
  simp only [TouchesBelow, TouchesAbove, Pi.neg_apply, neg_eq_iff_eq_neg, le_neg]

end Helpers

/-! ### Negation -/

/-- Negation exchanges sub- and supersolutions. -/
theorem isViscSubOn_neg_iff {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ} :
    IsViscSubOn Ω F u ↔ IsViscSuperOn Ω (fun p z ↦ -F p (-z)) (-u) := by
  refine ⟨fun ⟨husc, hu⟩ ↦ ⟨upperSemicontinuousOn_iff_lowerSemicontinuousOn_neg.1 husc,
    fun ψ hψ p hp ht ↦ ?_⟩, fun ⟨hlsc, hu⟩ ↦ ⟨?_, fun ψ hψ p hp ht ↦ ?_⟩⟩
  · have := hu (fun q ↦ -ψ q) hψ.neg p hp (touchesAbove_neg_iff'.2 ht)
    rw [dₜ_neg, lapₓ_neg] at this
    simp only [Pi.neg_apply, neg_neg]
    linarith
  · rw [upperSemicontinuousOn_iff_lowerSemicontinuousOn_neg]
    exact hlsc
  · have := hu (fun q ↦ -ψ q) hψ.neg p hp (touchesBelow_neg_iff.2 ht)
    rw [dₜ_neg, lapₓ_neg] at this
    simp only [Pi.neg_apply, neg_neg] at this
    linarith

/-- Negation exchanges sub- and supersolutions, supersolution form. -/
theorem isViscSuperOn_neg_iff {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {v : E d × ℝ → ℝ} :
    IsViscSuperOn Ω F v ↔ IsViscSubOn Ω (fun p z ↦ -F p (-z)) (-v) := by
  rw [isViscSubOn_neg_iff]
  simp only [neg_neg]

/-! ### Locality -/

/-- Tests that are only `C²` near the touching point suffice. -/
theorem IsViscSubOn.of_contDiffOn_test {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsViscSubOn Ω F u) {N : Set (E d × ℝ)} (hN : IsOpen N)
    {p : E d × ℝ} (hpN : p ∈ N) {ψ : E d × ℝ → ℝ} (hψ : ContDiffOn ℝ 2 ψ N)
    (ht : TouchesAbove ψ u Ω p) : dₜ ψ p - lapₓ ψ p + F p (u p) ≤ 0 := by
  obtain ⟨φ, hφ, hφψ⟩ := exists_contDiff_eventuallyEq (n := 2) hN hpN hψ
  have htφ : TouchesAbove φ u Ω p := by
    refine ⟨ht.1, hφψ.eq_of_nhds.trans ht.2.1, ?_⟩
    filter_upwards [ht.2.2, hφψ.filter_mono nhdsWithin_le_nhds] with q hq hq'
    rwa [hq']
  have := hu.2 φ hφ p ht.1 htφ
  rwa [dₜ_congr_nhds hφψ, lapₓ_congr_nhds hφψ] at this

/-- Tests that are only `C²` near the touching point suffice, supersolution mirror. -/
theorem IsViscSuperOn.of_contDiffOn_test {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsViscSuperOn Ω F u) {N : Set (E d × ℝ)} (hN : IsOpen N)
    {p : E d × ℝ} (hpN : p ∈ N) {ψ : E d × ℝ → ℝ} (hψ : ContDiffOn ℝ 2 ψ N)
    (ht : TouchesBelow ψ u Ω p) : 0 ≤ dₜ ψ p - lapₓ ψ p + F p (u p) := by
  have := (isViscSuperOn_neg_iff.1 hu).of_contDiffOn_test hN hpN hψ.neg
    (touchesAbove_neg_iff.2 ht)
  rw [dₜ_neg, lapₓ_neg] at this
  simp only [Pi.neg_apply, neg_neg] at this
  linarith

/-! ### Congruence -/

theorem IsViscSubOn.of_eqOn {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u v : E d × ℝ → ℝ}
    (h : EqOn u v Ω) (hu : IsViscSubOn Ω F u) : IsViscSubOn Ω F v := by
  refine ⟨UpperSemicontinuousOn.congr_eqOn hu.1 h, fun ψ hψ p hp ht ↦ ?_⟩
  have := hu.2 ψ hψ p hp (ht.congr_eqOn h.symm)
  rwa [h hp] at this

/-- The subsolution property depends only on the values on `Ω`. -/
theorem IsViscSubOn.congr {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u v : E d × ℝ → ℝ}
    (h : EqOn u v Ω) : IsViscSubOn Ω F u ↔ IsViscSubOn Ω F v :=
  ⟨IsViscSubOn.of_eqOn h, IsViscSubOn.of_eqOn h.symm⟩

/-- The supersolution property depends only on the values on `Ω`. -/
theorem IsViscSuperOn.congr {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u v : E d × ℝ → ℝ}
    (h : EqOn u v Ω) : IsViscSuperOn Ω F u ↔ IsViscSuperOn Ω F v := by
  rw [isViscSuperOn_neg_iff, isViscSuperOn_neg_iff]
  exact IsViscSubOn.congr fun p hp ↦ by simp [h hp]

/-! ### Monotonicity -/

/-- Lowering the zero-order term preserves subsolutions. -/
theorem IsViscSubOn.mono_source {Ω : Set (E d × ℝ)} {F F' : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hF : ∀ p ∈ Ω, ∀ z, F' p z ≤ F p z) (hu : IsViscSubOn Ω F u) :
    IsViscSubOn Ω F' u :=
  ⟨hu.1, fun ψ hψ p hp ht ↦ by linarith [hu.2 ψ hψ p hp ht, hF p hp (u p)]⟩

/-- Supersolution mirror: raising the zero-order term preserves supersolutions. -/
theorem IsViscSuperOn.mono_source {Ω : Set (E d × ℝ)} {F F' : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hF : ∀ p ∈ Ω, ∀ z, F p z ≤ F' p z) (hu : IsViscSuperOn Ω F u) :
    IsViscSuperOn Ω F' u :=
  ⟨hu.1, fun ψ hψ p hp ht ↦ by linarith [hu.2 ψ hψ p hp ht, hF p hp (u p)]⟩

/-- Restriction to an open subset. -/
theorem IsViscSubOn.mono_set {Ω Ω' : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ' : IsOpen Ω') (h : Ω' ⊆ Ω) (hu : IsViscSubOn Ω F u) :
    IsViscSubOn Ω' F u := by
  refine ⟨hu.1.mono h, fun ψ hψ p hp ht ↦ hu.2 ψ hψ p (h hp) ⟨h hp, ht.2.1, ?_⟩⟩
  have := ht.2.2
  rw [hΩ'.nhdsWithin_eq hp] at this
  exact this.filter_mono nhdsWithin_le_nhds

/-- Restriction to an open subset, supersolution mirror. -/
theorem IsViscSuperOn.mono_set {Ω Ω' : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ' : IsOpen Ω') (h : Ω' ⊆ Ω) (hu : IsViscSuperOn Ω F u) :
    IsViscSuperOn Ω' F u :=
  isViscSuperOn_neg_iff.2 ((isViscSuperOn_neg_iff.1 hu).mono_set hΩ' h)

/-- Local-to-global over an open cover. -/
theorem IsViscSubOn.of_locally {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hΩ : IsOpen Ω) (h : ∀ p ∈ Ω, ∃ O, IsOpen O ∧ p ∈ O ∧ O ⊆ Ω ∧ IsViscSubOn O F u) :
    IsViscSubOn Ω F u := by
  refine ⟨fun p hp ↦ ?_, fun ψ hψ p hp ht ↦ ?_⟩
  · obtain ⟨O, hO, hpO, -, hu⟩ := h p hp
    have := upperSemicontinuousWithinAt_iff.1 (hu.1 p hpO)
    rw [hO.nhdsWithin_eq hpO] at this
    refine upperSemicontinuousWithinAt_iff.2 ?_
    rw [hΩ.nhdsWithin_eq hp]
    exact this
  · obtain ⟨O, hO, hpO, -, hu⟩ := h p hp
    refine hu.2 ψ hψ p hpO ⟨hpO, ht.2.1, ?_⟩
    have := ht.2.2
    rw [hΩ.nhdsWithin_eq hp] at this
    rw [hO.nhdsWithin_eq hpO]
    exact this

/-- Local-to-global over an open cover, supersolution mirror. -/
theorem IsViscSuperOn.of_locally {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hΩ : IsOpen Ω) (h : ∀ p ∈ Ω, ∃ O, IsOpen O ∧ p ∈ O ∧ O ⊆ Ω ∧ IsViscSuperOn O F u) :
    IsViscSuperOn Ω F u := by
  refine isViscSuperOn_neg_iff.2 (IsViscSubOn.of_locally hΩ fun p hp ↦ ?_)
  obtain ⟨O, hO, hpO, hOΩ, hu⟩ := h p hp
  exact ⟨O, hO, hpO, hOΩ, isViscSuperOn_neg_iff.1 hu⟩

/-! ### Maximum and minimum -/

/-- The maximum of two subsolutions is a subsolution. -/
theorem IsViscSubOn.max {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u v : E d × ℝ → ℝ}
    (hu : IsViscSubOn Ω F u) (hv : IsViscSubOn Ω F v) :
    IsViscSubOn Ω F (fun p ↦ max (u p) (v p)) := by
  refine ⟨hu.1.sup hv.1, fun ψ hψ p hp ht ↦ ?_⟩
  beta_reduce
  rcases le_total (v p) (u p) with h | h
  · rw [max_eq_left h]
    refine hu.2 ψ hψ p hp ⟨hp, ht.2.1.trans (max_eq_left h), ?_⟩
    filter_upwards [ht.2.2] with q hq
    exact (le_max_left _ _).trans hq
  · rw [max_eq_right h]
    refine hv.2 ψ hψ p hp ⟨hp, ht.2.1.trans (max_eq_right h), ?_⟩
    filter_upwards [ht.2.2] with q hq
    exact (le_max_right _ _).trans hq

/-- Supersolution mirror: the minimum of two supersolutions is a supersolution. -/
theorem IsViscSuperOn.min {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u v : E d × ℝ → ℝ}
    (hu : IsViscSuperOn Ω F u) (hv : IsViscSuperOn Ω F v) :
    IsViscSuperOn Ω F (fun p ↦ min (u p) (v p)) := by
  have := (isViscSuperOn_neg_iff.1 hu).max (isViscSuperOn_neg_iff.1 hv)
  rw [isViscSuperOn_neg_iff]
  convert this using 1
  funext p
  simp [max_neg_neg]

end ParabolicBasic
