/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Comparison.Parabolic
public import ParabolicBasic.Perron.Envelope

/-!
# Perron's method: barriers, the Perron class, the a priori bound

Notation: `Ω = V ×ˢ Ioo a b`, `Ω̄ = closure V ×ˢ Icc a b`, `Γ = parBdry V a b`,
`F p r = f p.1 r` (the equation is `dₜu - lapₓu + f(x, u) = 0`).

* `PerronBarriers V a b f g`: local upper and lower barriers at every point of `Γ` (constructed
  in `ParabolicBasic.Barriers.Perron`).
* `perronClass V a b f g`: the functions that are USC on `Ω̄`, subsolutions on `Ω` and `≤ g` on
  `Γ`. There is no upper barrier in the class: boundedness comes from comparison (Step 1), which is
  what makes the bump step comparison-free.
* `perronSup V a b f g q = sup_{w ∈ 𝒫} w q`, used only for `q ∈ Ω`.

We do **not** use `ViscositySolns`' Perron theorem.
-/

@[expose] public section

open Set Filter Topology Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- Perron barriers. At every point `z` of the parabolic boundary and for every `ε > 0` there
are an upper barrier `U` (continuous on the closed cylinder, a supersolution in `V × (a, b)`,
`≥ g` on `Γ`, `≤ g z + ε` at `z`) and a lower barrier `L` (mirror). -/
structure PerronBarriers (V : Set (E d)) (a b : ℝ) (f : E d → ℝ → ℝ) (g : E d × ℝ → ℝ) :
    Prop where
  upper : ∀ z ∈ parBdry V a b, ∀ ε > 0, ∃ U : E d × ℝ → ℝ,
    ContinuousOn U (closure V ×ˢ Icc a b) ∧ IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) U ∧
    (∀ q ∈ parBdry V a b, g q ≤ U q) ∧ U z ≤ g z + ε
  lower : ∀ z ∈ parBdry V a b, ∀ ε > 0, ∃ L : E d × ℝ → ℝ,
    ContinuousOn L (closure V ×ˢ Icc a b) ∧ IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) L ∧
    (∀ q ∈ parBdry V a b, L q ≤ g q) ∧ g z - ε ≤ L z

/-- The Perron class: USC on the closed cylinder, subsolutions in the open cylinder, `≤ g` on the
parabolic boundary. -/
def perronClass (V : Set (E d)) (a b : ℝ) (f : E d → ℝ → ℝ) (g : E d × ℝ → ℝ) :
    Set (E d × ℝ → ℝ) :=
  {w | UpperSemicontinuousOn w (closure V ×ˢ Icc a b) ∧
    IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) w ∧ ∀ q ∈ parBdry V a b, w q ≤ g q}

/-- The Perron supremum `W q = sup_{w ∈ 𝒫} w q` (only used for `q ∈ V ×ˢ Ioo a b`, where the family
is bounded above by Step 1). -/
noncomputable def perronSup (V : Set (E d)) (a b : ℝ) (f : E d → ℝ → ℝ) (g : E d × ℝ → ℝ)
    (q : E d × ℝ) : ℝ :=
  sSup ((fun w : E d × ℝ → ℝ ↦ w q) '' perronClass V a b f g)

/-- The standing hypotheses of Perron's method, bundled for internal use: `V` open, bounded and
nonempty, `a < b`, `SemilinearHyp f (closure V)`, and barriers. -/
structure PerronHyp (V : Set (E d)) (a b : ℝ) (f : E d → ℝ → ℝ) (g : E d × ℝ → ℝ) : Prop where
  isOpen : IsOpen V
  isBounded : Bornology.IsBounded V
  nonempty : V.Nonempty
  lt : a < b
  semilinear : SemilinearHyp f (closure V)
  barriers : PerronBarriers V a b f g

/-! ### Cylinder geometry -/

/-- The parabolic boundary does not meet the open cylinder. -/
theorem notMem_cyl_of_mem_parBdry {V : Set (E d)} (hV : IsOpen V) {a b : ℝ} {p : E d × ℝ}
    (hp : p ∈ parBdry V a b) : p ∉ V ×ˢ Ioo a b := by
  rintro ⟨hp1, hp2⟩
  rcases hp with ⟨-, hpa⟩ | ⟨hpf, -⟩
  · rw [mem_singleton_iff] at hpa
    exact (lt_irrefl a) (hpa ▸ hp2.1)
  · rw [hV.frontier_eq] at hpf
    exact hpf.2 hp1

namespace PerronHyp

variable {V : Set (E d)} {a b : ℝ} {f : E d → ℝ → ℝ} {g : E d × ℝ → ℝ}

theorem isOpen_cyl (H : PerronHyp V a b f g) : IsOpen (V ×ˢ Ioo a b) :=
  H.isOpen.prod isOpen_Ioo

theorem closure_cyl (H : PerronHyp V a b f g) :
    closure (V ×ˢ Ioo a b) = closure V ×ˢ Icc a b :=
  closure_prod_Ioo_eq V H.lt

theorem cyl_subset (H : PerronHyp V a b f g) : V ×ˢ Ioo a b ⊆ closure V ×ˢ Icc a b :=
  H.closure_cyl ▸ subset_closure

theorem isCompact_closedCyl (H : PerronHyp V a b f g) : IsCompact (closure V ×ˢ Icc a b) :=
  H.isBounded.isCompact_closure.prod isCompact_Icc

theorem parBdry_subset (H : PerronHyp V a b f g) : parBdry V a b ⊆ closure V ×ˢ Icc a b :=
  parBdry_subset_closure V H.lt.le

theorem parBdry_nonempty (H : PerronHyp V a b f g) : (parBdry V a b).Nonempty :=
  let ⟨x, hx⟩ := H.nonempty
  ⟨(x, a), Or.inl ⟨subset_closure hx, rfl⟩⟩

/-! ### Step 0: the class is nonempty -/

/-- A continuous subsolution below `g` on `Γ` (e.g. a lower barrier) lies in the Perron class. -/
theorem mem_perronClass {L : E d × ℝ → ℝ} (hL : ContinuousOn L (closure V ×ˢ Icc a b))
    (hsub : IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) L)
    (hLg : ∀ q ∈ parBdry V a b, L q ≤ g q) : L ∈ perronClass V a b f g :=
  ⟨hL.upperSemicontinuousOn, hsub, hLg⟩

/-- Some lower barrier. -/
theorem exists_lower (H : PerronHyp V a b f g) : ∃ L : E d × ℝ → ℝ,
    ContinuousOn L (closure V ×ˢ Icc a b) ∧ IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) L ∧
    ∀ q ∈ parBdry V a b, L q ≤ g q := by
  obtain ⟨z, hz⟩ := H.parBdry_nonempty
  obtain ⟨L, hL, hsub, hLg, -⟩ := H.barriers.lower z hz 1 one_pos
  exact ⟨L, hL, hsub, hLg⟩

/-- Some upper barrier. -/
theorem exists_upper (H : PerronHyp V a b f g) : ∃ U : E d × ℝ → ℝ,
    ContinuousOn U (closure V ×ˢ Icc a b) ∧ IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) U ∧
    ∀ q ∈ parBdry V a b, g q ≤ U q := by
  obtain ⟨z, hz⟩ := H.parBdry_nonempty
  obtain ⟨U, hU, hsup, hgU, -⟩ := H.barriers.upper z hz 1 one_pos
  exact ⟨U, hU, hsup, hgU⟩

theorem perronClass_nonempty (H : PerronHyp V a b f g) : (perronClass V a b f g).Nonempty :=
  let ⟨L, hL, hsub, hLg⟩ := H.exists_lower
  ⟨L, mem_perronClass hL hsub hLg⟩

/-! ### Step 1: the a priori bound (comparison) -/

/-- Every member of the Perron class lies below every continuous supersolution that is `≥ g` on
`Γ` (by comparison). -/
theorem le_of_mem_perronClass (H : PerronHyp V a b f g) {w : E d × ℝ → ℝ}
    (hw : w ∈ perronClass V a b f g) {U : E d × ℝ → ℝ}
    (hU : ContinuousOn U (closure V ×ˢ Icc a b))
    (hsup : IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) U)
    (hgU : ∀ q ∈ parBdry V a b, g q ≤ U q) {q : E d × ℝ} (hq : q ∈ V ×ˢ Ioo a b) :
    w q ≤ U q :=
  comparison_usc_lsc H.isOpen H.isBounded H.lt H.semilinear hw.1 hU.lowerSemicontinuousOn
    hw.2.1 hsup (fun p hp ↦ (hw.2.2 p hp).trans (hgU p hp)) q
    ⟨subset_closure hq.1, hq.2.1.le, hq.2.2⟩

theorem bddAbove (H : PerronHyp V a b f g) {q : E d × ℝ} (hq : q ∈ V ×ˢ Ioo a b) :
    BddAbove ((fun w : E d × ℝ → ℝ ↦ w q) '' perronClass V a b f g) := by
  obtain ⟨U, hU, hsup, hgU⟩ := H.exists_upper
  exact ⟨U q, by rintro _ ⟨w, hw, rfl⟩; exact H.le_of_mem_perronClass hw hU hsup hgU hq⟩

theorem le_perronSup (H : PerronHyp V a b f g) {w : E d × ℝ → ℝ}
    (hw : w ∈ perronClass V a b f g) {q : E d × ℝ} (hq : q ∈ V ×ˢ Ioo a b) :
    w q ≤ perronSup V a b f g q :=
  le_csSup (H.bddAbove hq) ⟨w, hw, rfl⟩

theorem perronSup_le (H : PerronHyp V a b f g) {U : E d × ℝ → ℝ}
    (hU : ContinuousOn U (closure V ×ˢ Icc a b))
    (hsup : IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) U)
    (hgU : ∀ q ∈ parBdry V a b, g q ≤ U q) {q : E d × ℝ} (hq : q ∈ V ×ˢ Ioo a b) :
    perronSup V a b f g q ≤ U q :=
  csSup_le (H.perronClass_nonempty.image _)
    (by rintro _ ⟨w, hw, rfl⟩; exact H.le_of_mem_perronClass hw hU hsup hgU hq)

/-- Approximation of `W q` from below by members of the Perron class. -/
theorem exists_lt_perronSup (H : PerronHyp V a b f g) {q : E d × ℝ} {y : ℝ}
    (hy : y < perronSup V a b f g q) : ∃ w ∈ perronClass V a b f g, y < w q := by
  obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (H.perronClass_nonempty.image _) hy
  exact ⟨w, hw, hlt⟩

/-- Global two-sided bounds for `W` on the open cylinder. -/
theorem exists_bounds (H : PerronHyp V a b f g) : ∃ m M : ℝ,
    (∀ q ∈ V ×ˢ Ioo a b, m ≤ perronSup V a b f g q) ∧
    (∀ q ∈ V ×ˢ Ioo a b, perronSup V a b f g q ≤ M) := by
  obtain ⟨U, hU, hsup, hgU⟩ := H.exists_upper
  obtain ⟨L, hL, hsub, hLg⟩ := H.exists_lower
  obtain ⟨CU, hCU⟩ := H.isCompact_closedCyl.exists_bound_of_continuousOn hU
  obtain ⟨CL, hCL⟩ := H.isCompact_closedCyl.exists_bound_of_continuousOn hL
  refine ⟨-CL, CU, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · have h1 := H.le_perronSup (mem_perronClass hL hsub hLg) hq
    have h2 := neg_abs_le (L q)
    have h3 := hCL q (H.cyl_subset hq)
    rw [Real.norm_eq_abs] at h3
    linarith
  · have h1 := H.perronSup_le hU hsup hgU hq
    have h2 := le_abs_self (U q)
    have h3 := hCU q (H.cyl_subset hq)
    rw [Real.norm_eq_abs] at h3
    linarith

end PerronHyp

end ParabolicBasic
