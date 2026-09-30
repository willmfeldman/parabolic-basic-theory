/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Perron.Bump

/-!
# Perron existence on cylinders

Comparison (`comparison_usc_lsc`) is applied to `W^*` (USC subsolution) and `W_*` (LSC
supersolution), which are ordered on the parabolic boundary; so `W_* = W = W^*` in the open
cylinder. The solution is `g` on `Γ` and `W^*` elsewhere. The top face `V × {b}` is excluded.
-/

@[expose] public section

open Set Filter Topology Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- Perron existence for the semilinear Cauchy–Dirichlet problem `dₜu = lapₓu - f(x, u)` in
`V × (a, b)`, `u = g` on `parBdry V a b`, given local barriers at every point of the parabolic
boundary. The solution is continuous on `V × (a, b) ∪ parBdry V a b` (the top face is not claimed).
-/
theorem exists_viscSolution_cyl {V : Set (E d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {a b : ℝ} (hab : a < b) {f : E d → ℝ → ℝ} (hf : SemilinearHyp f (closure V))
    {g : E d × ℝ → ℝ} (hg : ContinuousOn g (parBdry V a b)) (hbar : PerronBarriers V a b f g) :
    ∃ u : E d × ℝ → ℝ, ContinuousOn u (V ×ˢ Ioo a b ∪ parBdry V a b) ∧
      IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) u ∧
      IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) u ∧
      EqOn u g (parBdry V a b) := by
  classical
  /- The degenerate case `V = ∅`: the cylinder and its parabolic boundary are empty. -/
  rcases V.eq_empty_or_nonempty with rfl | hne
  · have hΓ : parBdry (∅ : Set (E d)) a b = ∅ := by simp [parBdry]
    refine ⟨g, by simp [hΓ], ⟨fun p hp ↦ by simp at hp, fun _ _ p hp ↦ by simp at hp⟩,
      ⟨fun p hp ↦ by simp at hp, fun _ _ p hp ↦ by simp at hp⟩, fun _ _ ↦ rfl⟩
  have H : PerronHyp V a b f g := ⟨hV, hVb, hne, hab, hf, hbar⟩
  set Wu := perronUpper V a b f g with hWu_def
  set Wl := perronLower V a b f g with hWl_def
  /- Step 5: comparison of `W^*` and `W_*`. -/
  have heq : ∀ q ∈ V ×ˢ Ioo a b, Wl q = Wu q := fun q hq ↦
    le_antisymm (H.perronLower_le_perronUpper hq)
      (comparison_usc_lsc hV hVb hab hf H.upperSemicontinuousOn_perronUpper
        H.lowerSemicontinuousOn_perronLower H.isViscSubOn_perronUpper
        H.isViscSuperOn_perronLower
        (fun p hp ↦ (H.perronUpper_le_g hp).trans (H.g_le_perronLower hp)) q
        ⟨subset_closure hq.1, hq.2.1.le, hq.2.2⟩)
  /- The solution: `g` on `Γ`, `W^*` elsewhere. -/
  set u : E d × ℝ → ℝ := fun p ↦ if p ∈ parBdry V a b then g p else Wu p with hu_def
  have huΩ : EqOn u Wu (V ×ˢ Ioo a b) := fun p hp ↦
    ite_eq_right fun h ↦ notMem_cyl_of_mem_parBdry hV h hp
  have huΩ' : EqOn u Wl (V ×ˢ Ioo a b) := fun p hp ↦ (huΩ hp).trans (heq p hp).symm
  refine ⟨u, ?_, (IsViscSubOn.congr huΩ).2 H.isViscSubOn_perronUpper,
    (IsViscSuperOn.congr huΩ').2 H.isViscSuperOn_perronLower, fun p hp ↦ ite_eq_left hp⟩
  /- Continuity on `Ω ∪ Γ`. -/
  intro z hz
  have hzcl : z ∈ closure V ×ˢ Icc a b :=
    hz.elim (fun h ↦ H.cyl_subset h) (fun h ↦ H.parBdry_subset h)
  have hbounds : Wu z ≤ u z ∧ u z ≤ Wl z := by
    rcases hz with hz | hz
    · rw [huΩ hz, heq z hz]
      exact ⟨le_rfl, le_rfl⟩
    · rw [show u z = g z from ite_eq_left hz]
      exact ⟨H.perronUpper_le_g hz, H.g_le_perronLower hz⟩
  refine ContinuousWithinAt.union ?_ ?_
  · rw [ContinuousWithinAt, tendsto_order]
    constructor
    · intro y hy
      filter_upwards [nhdsWithin_mono _ H.cyl_subset
        (H.lowerSemicontinuousOn_perronLower z hzcl y (hy.trans_le hbounds.2)),
        self_mem_nhdsWithin] with q hq hqΩ
      rw [huΩ' hqΩ]
      exact hq
    · intro y hy
      filter_upwards [nhdsWithin_mono _ H.cyl_subset
        (H.upperSemicontinuousOn_perronUpper z hzcl y (hbounds.1.trans_lt hy)),
        self_mem_nhdsWithin] with q hq hqΩ
      rw [huΩ hqΩ]
      exact hq
  · rcases hz with hz | hz
    · have hΓc : IsClosed (parBdry V a b) :=
        (isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Icc)
      refine continuousWithinAt_of_notMem_closure ?_
      rw [hΓc.closure_eq]
      exact fun h ↦ notMem_cyl_of_mem_parBdry hV h hz
    · exact (hg z hz).congr (fun q hq ↦ ite_eq_left hq) (ite_eq_left hz)

end ParabolicBasic
