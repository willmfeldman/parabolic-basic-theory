/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Comparison.Parabolic

/-!
# Comparison for continuous viscosity sub/supersolutions

`comparison_usc_lsc_source` with `S = 0` gives `u ≤ v` on `closure V ×ˢ Ico a b`; the top face
`t = b` follows by continuity (the sub/supersolution property is never used at `t = b`).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- If `u ≤ v` on `closure V ×ˢ Ico a b` and both are continuous on `closure V ×ˢ Icc a b`, then
`u ≤ v` on `closure V ×ˢ Icc a b`. -/
theorem le_on_Icc_of_le_on_Ico {V : Set (E d)} {a b : ℝ} (hab : a < b) {u v : E d × ℝ → ℝ}
    (hu : ContinuousOn u (closure V ×ˢ Icc a b)) (hv : ContinuousOn v (closure V ×ˢ Icc a b))
    (h : ∀ p ∈ closure V ×ˢ Ico a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Icc a b, u p ≤ v p := by
  intro p hp
  have hcl : p ∈ closure (closure V ×ˢ Ico a b) := by
    rw [closure_prod_eq, closure_closure, closure_Ico hab.ne]; exact hp
  have hsub : closure V ×ˢ Ico a b ⊆ closure V ×ˢ Icc a b := prod_mono le_rfl Ico_subset_Icc_self
  exact ContinuousWithinAt.closure_le hcl ((hu p hp).mono hsub) ((hv p hp).mono hsub) h

/-- **Comparison for continuous sub/supersolutions.** If `u ≤ v` on the parabolic boundary, then
`u ≤ v` on `closure V ×ˢ Icc a b`. -/
theorem comparison_continuous {V : Set (E d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {a b : ℝ} (hab : a < b) {f : E d → ℝ → ℝ}
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure V, ∀ y ∈ closure V, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure V, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    {u v : E d × ℝ → ℝ} (hu : ContinuousOn u (closure V ×ˢ Icc a b))
    (hv : ContinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsViscSubOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z) u)
    (hsuper : IsViscSuperOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Icc a b, u p ≤ v p := by
  have hF : (fun p z ↦ f p.1 z - (fun _ : E d × ℝ ↦ (0 : ℝ)) p) = fun p z ↦ f p.1 z := by
    funext p z; simp
  refine le_on_Icc_of_le_on_Ico hab hu hv ?_
  exact comparison_usc_lsc_source hV hVb hab hfx hfz continuousOn_const
    hu.upperSemicontinuousOn hv.lowerSemicontinuousOn (by rw [hF]; exact hsub)
    (by rw [hF]; exact hsuper) hbdry

/-- `d = 0` regression: `E 0` is a point, the lateral boundary is empty, and the
equation is the ODE `w' + f(0, w) = 0`. -/
example {V : Set (E 0)} (hV : IsOpen V) (hVb : Bornology.IsBounded V) {a b : ℝ} (hab : a < b)
    {f : E 0 → ℝ → ℝ}
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure V, ∀ y ∈ closure V, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure V, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    {u v : E 0 × ℝ → ℝ} (hu : ContinuousOn u (closure V ×ˢ Icc a b))
    (hv : ContinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsViscSubOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z) u)
    (hsuper : IsViscSuperOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Icc a b, u p ≤ v p :=
  comparison_continuous hV hVb hab hfx hfz hu hv hsub hsuper hbdry

end ParabolicBasic
