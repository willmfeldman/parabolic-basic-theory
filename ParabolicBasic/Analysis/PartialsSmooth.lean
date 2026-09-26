/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.Partials

/-!
# Continuous coordinate partials ⇔ `ContDiffOn`

On an open set `s ⊆ E d × ℝ`:

* `contDiffOn_of_hasPartialsOn`: `HasPartialsOn k f s → ContDiffOn ℝ k f s`;
* `contDiffOn_infty_of_hasPartialsOn`: `(∀ k, HasPartialsOn k f s) → ContDiffOn ℝ ∞ f s`;
* `hasPartialsOn_of_contDiffOn`: the converse; `contDiffOn_iff_hasPartialsOn`.

Since `HasPartialsOn` already asks for Fréchet differentiability of the partials of order `< k`,
no mean-value (telescoping) argument is needed: `Df = ∑ⱼ ∂ⱼf eⱼ*` (`fderiv_eq_sum_partialDeriv`),
and one inducts with `contDiffOn_succ_iff_fderiv_of_isOpen`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ} {f : E d × ℝ → ℝ} {s : Set (E d × ℝ)}

theorem HasPartialsOn.mono {k m : ℕ} (h : HasPartialsOn k f s) (hmk : m ≤ k) :
    HasPartialsOn m f s := fun w hw ↦
  ⟨(h w (hw.trans hmk)).1, fun hw' ↦ (h w (hw.trans hmk)).2 (hw'.trans_le hmk)⟩

/-- If `f` has partials of order `≤ k + 1`, then each `∂ⱼ f` has partials of order `≤ k`. -/
theorem HasPartialsOn.partialDeriv {k : ℕ} (h : HasPartialsOn (k + 1) f s) (j : Fin (d + 1)) :
    HasPartialsOn k (partialDeriv j f) s := by
  intro w hw
  have hw' : (w ++ [j]).length ≤ k + 1 := by simpa using hw
  rw [← iterPartial_concat]
  exact ⟨(h _ hw').1, fun hlt ↦ (h _ hw').2 (by simpa using hlt)⟩

/-- Continuous partials of order `≤ k` (and differentiable ones of order `< k`) on an open set
give `Cᵏ`. -/
theorem contDiffOn_of_hasPartialsOn {k : ℕ} (hs : IsOpen s) (h : HasPartialsOn k f s) :
    ContDiffOn ℝ k f s := by
  induction k generalizing f with
  | zero => simpa using (h [] le_rfl).1
  | succ k ih =>
    have hdiff : ∀ z ∈ s, DifferentiableAt ℝ f z := (h [] (by simp)).2 (by simp)
    rw [Nat.cast_add_one, contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun z hz ↦ (hdiff z hz).differentiableWithinAt, by simp, ?_⟩
    rw [show fderiv ℝ f = fun z ↦ ∑ j, partialDeriv j f z • ecoord d j from
      funext (fderiv_eq_sum_partialDeriv f)]
    exact ContDiffOn.sum fun j _ ↦ (ih (h.partialDeriv j)).smul contDiffOn_const

/-- Continuous partials of every order on an open set give `C^∞`. -/
theorem contDiffOn_infty_of_hasPartialsOn (hs : IsOpen s) (h : ∀ k, HasPartialsOn k f s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_infty.2 fun k ↦ contDiffOn_of_hasPartialsOn hs (h k)

/-- A partial of a `C^{k+1}` function is `Cᵏ` (on an open set). -/
theorem ContDiffOn.partialDeriv {k : WithTop ℕ∞} (hs : IsOpen s) (hf : ContDiffOn ℝ (k + 1) f s)
    (j : Fin (d + 1)) : ContDiffOn ℝ k (partialDeriv j f) s := by
  exact ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1 hf).2.2.clm_apply contDiffOn_const

/-- Every iterated partial of a `C^∞` function is `C^∞` (on an open set). -/
theorem ContDiffOn.iterPartial (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (w : List (Fin (d + 1))) : ContDiffOn ℝ ∞ (iterPartial w f) s := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact ContDiffOn.partialDeriv hs ih j

/-- `Cᵏ` on an open set gives `HasPartialsOn k`. -/
theorem hasPartialsOn_of_contDiffOn {k : ℕ} (hs : IsOpen s) (h : ContDiffOn ℝ k f s) :
    HasPartialsOn k f s := by
  induction k generalizing f with
  | zero =>
    intro w hw
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    exact ⟨by simpa using h.continuousOn, fun h ↦ absurd h (lt_irrefl 0)⟩
  | succ k ih =>
    replace h : ContDiffOn ℝ (k + 1) f s := by exact_mod_cast h
    have hdiff : DifferentiableOn ℝ f s := h.differentiableOn (by simp)
    intro w hw
    rcases List.eq_nil_or_concat' w with rfl | ⟨w', j, rfl⟩
    · exact ⟨h.continuousOn, fun _ z hz ↦ (hdiff z hz).differentiableAt (hs.mem_nhds hz)⟩
    · have := ih (ContDiffOn.partialDeriv hs h j) w' (by simpa using hw)
      rw [iterPartial_concat]
      exact ⟨this.1, fun hlt ↦ this.2 (by simpa using hlt)⟩

theorem contDiffOn_iff_hasPartialsOn {k : ℕ} (hs : IsOpen s) :
    ContDiffOn ℝ k f s ↔ HasPartialsOn k f s :=
  ⟨hasPartialsOn_of_contDiffOn hs, contDiffOn_of_hasPartialsOn hs⟩

/-! ### Sanity checks -/

/-- A polynomial in the time variable has partials of every order, on all of space-time. -/
example (k : ℕ) : HasPartialsOn k (fun z : E d × ℝ ↦ z.2 ^ 2 + 1) univ :=
  hasPartialsOn_of_contDiffOn isOpen_univ
    ((contDiff_snd.pow 2).add contDiff_const).contDiffOn

/-- `contDiffOn_infty_of_hasPartialsOn` recovers smoothness from the partials. -/
example : ContDiffOn ℝ ∞ (fun z : E d × ℝ ↦ z.2 ^ 2 + 1) univ :=
  contDiffOn_infty_of_hasPartialsOn isOpen_univ fun _ ↦
    hasPartialsOn_of_contDiffOn isOpen_univ ((contDiff_snd.pow 2).add contDiff_const).contDiffOn

end ParabolicBasic
