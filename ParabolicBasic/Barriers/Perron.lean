/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Barriers.Heat
public import ParabolicBasic.Classical.ToViscosity
public import ParabolicBasic.Perron.Class

/-!
# Perron barriers

From a separable heat barrier `w = φ x + τ t` at `z ∈ Γ = parBdry V a b` (`IsSepBarrier`) and
`ε > 0`: with `M_f` the bound of `f`, `M_g` that of `g` on the compact `Γ`, `δ` from the continuity
of `g` at `z`, `c_δ = min_{Γ \ B(z, δ)} w > 0` and `K = max(M_f, 2 M_g / c_δ)`,
`U = g z + ε + K w` is an upper and `L = g z - ε - K w` a lower barrier
(`exists_upper_barrier`, `exists_lower_barrier`).

Assembly: at `z = (ξ, a)` use the initial barrier, at `z ∈ frontier V × [a, b]` the lateral one
(`perronBarriers_of_exteriorSphere`); balls (`perronBarriers_ball`, all `d`, including `d = 0`) and
bounded `C²` domains (`perronBarriers_of_hasC2Boundary`).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped Laplacian ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- The parabolic boundary of a bounded cylinder is compact. -/
theorem isCompact_parBdry {V : Set (E d)} (hVb : Bornology.IsBounded V) {a b : ℝ} (hab : a ≤ b) :
    IsCompact (parBdry V a b) :=
  (hVb.isCompact_closure.prod isCompact_Icc).of_isClosed_subset
    ((isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Icc))
    (parBdry_subset_closure V hab)

section Semilinear

variable {V : Set (E d)} {a b : ℝ} {f : E d → ℝ → ℝ} {g : E d × ℝ → ℝ} {z : E d × ℝ}
  {φ : E d → ℝ} {τ : ℝ → ℝ}

theorem IsSepBarrier.continuousOn_cyl (hw : IsSepBarrier V a b z φ τ) :
    ContinuousOn (fun q : E d × ℝ ↦ φ q.1 + τ q.2) (closure V ×ˢ Icc a b) :=
  (hw.continuousOn.comp continuousOn_fst fun _ hq ↦ hq.1).add
    (hw.contDiff_time.continuous.comp continuous_snd).continuousOn

theorem IsSepBarrier.contDiffOn_cyl (hw : IsSepBarrier V a b z φ τ) :
    ContDiffOn ℝ 2 (fun q : E d × ℝ ↦ φ q.1 + τ q.2) (V ×ˢ Ioo a b) :=
  (hw.contDiffOn.comp contDiffOn_fst fun _ hq ↦ hq.1).add
    (hw.contDiff_time.comp contDiff_snd).contDiffOn

/-- The constant `K` of the barrier construction: `K ≥ M_f` and `|g q - g z| ≤ ε + K w q` on `Γ`. -/
theorem IsSepBarrier.exists_const (hw : IsSepBarrier V a b z φ τ)
    (hVb : Bornology.IsBounded V) (hab : a ≤ b) (hf : SemilinearHyp f (closure V))
    (hg : ContinuousOn g (parBdry V a b)) (hz : z ∈ parBdry V a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ closure V, ∀ r, |f x r| ≤ K) ∧
      ∀ q ∈ parBdry V a b, |g q - g z| ≤ ε + K * (φ q.1 + τ q.2) := by
  set w : E d × ℝ → ℝ := fun q ↦ φ q.1 + τ q.2 with hwdef
  have hΓ := isCompact_parBdry hVb hab (V := V)
  obtain ⟨Mf₀, hMf₀⟩ := hf.bounded
  obtain ⟨Mg₀, hMg₀⟩ := hΓ.exists_bound_of_continuousOn hg
  set Mf := max Mf₀ 0
  set Mg := max Mg₀ 0
  have hMf : 0 ≤ Mf := le_max_right _ _
  have hMg : 0 ≤ Mg := le_max_right _ _
  have hgM : ∀ q ∈ parBdry V a b, |g q| ≤ Mg := fun q hq ↦
    (Real.norm_eq_abs (g q) ▸ hMg₀ q hq).trans (le_max_left _ _)
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousWithinAt_iff.1 (hg z hz) ε hε
  -- `c_δ`
  obtain ⟨c, hc, hcw⟩ : ∃ c > 0, ∀ q ∈ parBdry V a b, δ ≤ dist q z → c ≤ w q := by
    set S := parBdry V a b ∩ {q | δ ≤ dist q z}
    rcases S.eq_empty_or_nonempty with hS | hS
    · refine ⟨1, one_pos, fun q hq hqδ ↦ ?_⟩
      exact absurd (show q ∈ S from ⟨hq, hqδ⟩) (hS ▸ notMem_empty q)
    · have hSc : IsCompact S :=
        hΓ.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
      obtain ⟨q₀, hq₀, hmin⟩ := hSc.exists_isMinOn hS
        ((hw.continuousOn_cyl.mono (parBdry_subset_closure V hab)).mono inter_subset_left)
      have hq₀z : q₀ ≠ z := fun h ↦ by
        have := hq₀.2
        rw [mem_ofPred_eq, h, dist_self] at this
        linarith
      exact ⟨w q₀, hw.pos q₀ hq₀.1 hq₀z, fun q hq hqδ ↦ hmin ⟨hq, hqδ⟩⟩
  refine ⟨max Mf (2 * Mg / c), le_max_of_le_left hMf, fun x hx r ↦
    (hMf₀ x hx r).trans ((le_max_left _ _).trans (le_max_left _ _)), fun q hq ↦ ?_⟩
  have hK0 : 0 ≤ max Mf (2 * Mg / c) := le_max_of_le_left hMf
  have hwq : 0 ≤ w q := hw.nonneg hq
  by_cases hqδ : dist q z < δ
  · have := hgδ hq hqδ
    rw [Real.dist_eq] at this
    have : 0 ≤ max Mf (2 * Mg / c) * w q := mul_nonneg hK0 hwq
    linarith
  · have hcq := hcw q hq (not_lt.1 hqδ)
    have h1 : 2 * Mg ≤ max Mf (2 * Mg / c) * w q := calc
      2 * Mg = 2 * Mg / c * c := by field_simp
      _ ≤ max Mf (2 * Mg / c) * w q :=
        mul_le_mul (le_max_right _ _) hcq hc.le hK0
    have h2 : |g q - g z| ≤ 2 * Mg := (abs_sub _ _).trans (by linarith [hgM q hq, hgM z hz])
    linarith

/-- `U = g z + ε + K w` is an upper barrier at `z`. -/
theorem IsSepBarrier.exists_upper_barrier (hw : IsSepBarrier V a b z φ τ) (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hab : a ≤ b) (hf : SemilinearHyp f (closure V))
    (hg : ContinuousOn g (parBdry V a b)) (hz : z ∈ parBdry V a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : E d × ℝ → ℝ,
      ContinuousOn U (closure V ×ˢ Icc a b) ∧ IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) U ∧
      (∀ q ∈ parBdry V a b, g q ≤ U q) ∧ U z ≤ g z + ε := by
  obtain ⟨K, hK0, hfK, hgK⟩ := hw.exists_const hVb hab hf hg hz hε
  refine ⟨fun q ↦ (g z + ε) + K * (φ q.1 + τ q.2),
    continuousOn_const.add (continuousOn_const.mul hw.continuousOn_cyl),
    isViscSuperOn_of_contDiffOn (hV.prod isOpen_Ioo)
      (contDiffOn_const.add (contDiffOn_const.mul hw.contDiffOn_cyl)) fun p hp ↦ ?_,
    fun q hq ↦ ?_, ?_⟩
  · rw [dₜ_const_add_mul_sep φ _ _ ((hw.contDiff_time.differentiable two_ne_zero) p.2),
      lapₓ_const_add_mul_sep τ _ _ (hw.contDiffOn.contDiffAt (hV.mem_nhds hp.1))]
    have h1 := mul_le_mul_of_nonneg_left (hw.heat p hp) hK0
    have h2 := (abs_le.1 (hfK p.1 (subset_closure hp.1) ((g z + ε) + K * (φ p.1 + τ p.2)))).1
    nlinarith
  · have := (abs_le.1 (hgK q hq)).2
    linarith
  · simp only [hw.zero, mul_zero, add_zero, le_refl]

/-- `L = g z - ε - K w` is a lower barrier at `z`. -/
theorem IsSepBarrier.exists_lower_barrier (hw : IsSepBarrier V a b z φ τ) (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hab : a ≤ b) (hf : SemilinearHyp f (closure V))
    (hg : ContinuousOn g (parBdry V a b)) (hz : z ∈ parBdry V a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : E d × ℝ → ℝ,
      ContinuousOn L (closure V ×ˢ Icc a b) ∧ IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) L ∧
      (∀ q ∈ parBdry V a b, L q ≤ g q) ∧ g z - ε ≤ L z := by
  obtain ⟨K, hK0, hfK, hgK⟩ := hw.exists_const hVb hab hf hg hz hε
  refine ⟨fun q ↦ (g z - ε) + (-K) * (φ q.1 + τ q.2),
    continuousOn_const.add (continuousOn_const.mul hw.continuousOn_cyl),
    isViscSubOn_of_contDiffOn (hV.prod isOpen_Ioo)
      (contDiffOn_const.add (contDiffOn_const.mul hw.contDiffOn_cyl)) fun p hp ↦ ?_,
    fun q hq ↦ ?_, ?_⟩
  · rw [dₜ_const_add_mul_sep φ _ _ ((hw.contDiff_time.differentiable two_ne_zero) p.2),
      lapₓ_const_add_mul_sep τ _ _ (hw.contDiffOn.contDiffAt (hV.mem_nhds hp.1))]
    have h1 := mul_le_mul_of_nonneg_left (hw.heat p hp) hK0
    have h2 := (abs_le.1 (hfK p.1 (subset_closure hp.1) ((g z - ε) + (-K) * (φ p.1 + τ p.2)))).2
    nlinarith
  · have := (abs_le.1 (hgK q hq)).1
    linarith
  · simp only [hw.zero, mul_zero, add_zero, le_refl]

end Semilinear

/-! ### Assembly -/

/-- Separable barriers at every point of the parabolic boundary give `PerronBarriers`. -/
theorem perronBarriers_of_isSepBarrier {V : Set (E d)} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) {a b : ℝ} (hab : a ≤ b) {f : E d → ℝ → ℝ}
    (hf : SemilinearHyp f (closure V)) {g : E d × ℝ → ℝ} (hg : ContinuousOn g (parBdry V a b))
    (hw : ∀ z ∈ parBdry V a b, ∃ φ : E d → ℝ, ∃ τ : ℝ → ℝ, IsSepBarrier V a b z φ τ) :
    PerronBarriers V a b f g where
  upper z hz _ hε :=
    let ⟨_, _, hzw⟩ := hw z hz
    hzw.exists_upper_barrier hV hVb hab hf hg hz hε
  lower z hz _ hε :=
    let ⟨_, _, hzw⟩ := hw z hz
    hzw.exists_lower_barrier hV hVb hab hf hg hz hε

/-- A bounded open `V` with an exterior sphere at every frontier point
admits Perron barriers for every semilinear `f` and continuous boundary data `g`. -/
theorem perronBarriers_of_exteriorSphere {V : Set (E d)} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) {a b : ℝ} (hab : a < b) {f : E d → ℝ → ℝ}
    (hf : SemilinearHyp f (closure V)) {g : E d × ℝ → ℝ} (hg : ContinuousOn g (parBdry V a b))
    (hext : ∀ ξ ∈ frontier V, ExteriorSphereAt V ξ) : PerronBarriers V a b f g := by
  refine perronBarriers_of_isSepBarrier hV hVb hab.le hf hg fun z hz ↦ ?_
  rcases hz with ⟨-, hz2⟩ | ⟨hz1, hz2⟩
  · rw [mem_singleton_iff] at hz2
    have hz' : z = (z.1, a) := Prod.ext rfl hz2
    rw [hz']
    exact ⟨_, _, isSepBarrier_initial V a b z.1⟩
  · exact isSepBarrier_lateral hVb hz1 (hext z.1 hz1) hz2

/-- **Perron barriers for balls** (all `d`, including `d = 0`). -/
theorem perronBarriers_ball (x₀ : E d) {ρ : ℝ} (_hρ : 0 < ρ) {a b : ℝ} (hab : a < b)
    {f : E d → ℝ → ℝ} (hf : SemilinearHyp f (closure (ball x₀ ρ))) {g : E d × ℝ → ℝ}
    (hg : ContinuousOn g (parBdry (ball x₀ ρ) a b)) : PerronBarriers (ball x₀ ρ) a b f g :=
  perronBarriers_of_exteriorSphere isOpen_ball isBounded_ball hab hf hg
    fun _ hξ ↦ exteriorSphereAt_ball x₀ hξ

/-- **Perron barriers for bounded `C²` domains.** -/
theorem perronBarriers_of_hasC2Boundary {U : Set (E d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hC2 : HasC2Boundary U) {a b : ℝ} (hab : a < b)
    {f : E d → ℝ → ℝ} (hf : SemilinearHyp f (closure U)) {g : E d × ℝ → ℝ}
    (hg : ContinuousOn g (parBdry U a b)) : PerronBarriers U a b f g :=
  perronBarriers_of_exteriorSphere hU hUb hab hf hg
    fun _ hξ ↦ exteriorSphereAt_of_hasC2Boundary hC2 hξ

/-- `d = 0` sanity check: `E 0` is a point, the lateral boundary is empty, and only the
initial barrier is used. -/
example (x₀ : E 0) {a b : ℝ} (hab : a < b) {g : E 0 × ℝ → ℝ}
    (hg : ContinuousOn g (parBdry (ball x₀ 1) a b)) :
    PerronBarriers (ball x₀ 1) a b (fun _ _ ↦ 0) g :=
  perronBarriers_ball x₀ one_pos hab (SemilinearHyp.zero _) hg

end ParabolicBasic
