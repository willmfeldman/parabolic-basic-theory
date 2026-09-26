/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Semilinear.ExistenceBasic
public import ParabolicBasic.Perron.Existence
public import ParabolicBasic.Barriers.Perron
public import ParabolicBasic.Viscosity.Basic

/-!
# Semilinear existence: truncated problems and gluing

For `U` open, bounded, with `C²` boundary, `f` satisfying `SemilinearHyp f (closure U)` and `g`
continuous on `closure U`:

* `exists_truncSol`: Perron's method with the `C²` barriers solves the Cauchy–Dirichlet problem
  on each truncated cylinder `U × (0, b)`, with data `G p = g p.1` on `parBdry U 0 b`;
* `eqOn_of_truncSol`: two such truncated solutions agree on `closure U × [0, b')` for every
  `b'` below both final times (viscosity comparison, applied twice);
* `exists_viscSolution_semilinear_Ioi`: gluing `u p := sol ⌊p.2⌋₊ p` gives a viscosity solution
  on `U × (0, ∞)`, continuous on `closure U × [0, ∞)`, attaining the data.

Gluing is done by comparison of viscosity solutions *before* any regularity is known
(`semilinear_unique` is about classical solutions and does not apply here).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- The properties of a solution of the truncated Cauchy–Dirichlet problem on `U × (0, b)` with
time-independent data `g` (the output of Perron's method). -/
def IsTruncSol (U : Set (E d)) (f : E d → ℝ → ℝ) (g : E d → ℝ) (b : ℝ) (v : E d × ℝ → ℝ) :
    Prop :=
  ContinuousOn v (U ×ˢ Ioo 0 b ∪ parBdry U 0 b) ∧
    IsViscSubOn (U ×ˢ Ioo 0 b) (fun p r ↦ f p.1 r) v ∧
    IsViscSuperOn (U ×ˢ Ioo 0 b) (fun p r ↦ f p.1 r) v ∧
    EqOn v (fun p ↦ g p.1) (parBdry U 0 b)

/-- **Truncation.** The truncated problems are solvable (Perron + `C²` barriers). -/
theorem exists_truncSol {U : Set (E d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hC2 : HasC2Boundary U) {f : E d → ℝ → ℝ} (hf : SemilinearHyp f (closure U))
    {g : E d → ℝ} (hg : ContinuousOn g (closure U)) {b : ℝ} (hb : 0 < b) :
    ∃ v, IsTruncSol U f g b v := by
  have hG : ContinuousOn (fun p : E d × ℝ ↦ g p.1) (parBdry U 0 b) :=
    hg.comp continuousOn_fst fun p hp ↦ (parBdry_subset_closure U hb.le hp).1
  exact exists_viscSolution_cyl hU hUb hb hf hG
    (perronBarriers_of_hasC2Boundary hU hUb hC2 hb hf hG)

/-- One half of the consistency: comparison of two truncated solutions below both final times. -/
theorem le_of_truncSol {U : Set (E d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : E d → ℝ → ℝ} (hf : SemilinearHyp f (closure U)) {g : E d → ℝ} {b₁ b₂ b' : ℝ}
    (hb' : 0 < b') (h₁ : b' < b₁) (h₂ : b' < b₂) {v w : E d × ℝ → ℝ}
    (hv : IsTruncSol U f g b₁ v) (hw : IsTruncSol U f g b₂ w) :
    ∀ p ∈ closure U ×ˢ Ico 0 b', v p ≤ w p := by
  have hsub : ∀ {b}, b' < b → closure U ×ˢ Icc 0 b' ⊆ U ×ˢ Ioo 0 b ∪ parBdry U 0 b :=
    fun hb ↦ (prod_mono subset_rfl (Icc_subset_Ico_right hb)).trans
      (closure_prod_Ico_subset hU _)
  have hO : IsOpen (U ×ˢ Ioo (0 : ℝ) b') := hU.prod isOpen_Ioo
  refine comparison_usc_lsc hU hUb hb' hf ((hv.1.mono (hsub h₁)).upperSemicontinuousOn)
    ((hw.1.mono (hsub h₂)).lowerSemicontinuousOn)
    (hv.2.1.mono_set hO (prod_mono subset_rfl (Ioo_subset_Ioo_right h₁.le)))
    (hw.2.2.1.mono_set hO (prod_mono subset_rfl (Ioo_subset_Ioo_right h₂.le))) fun p hp ↦ ?_
  rw [hv.2.2.2 (parBdry_subset_parBdry U 0 h₁.le hp),
    hw.2.2.2 (parBdry_subset_parBdry U 0 h₂.le hp)]

/-- **Gluing, consistency.** Two truncated solutions agree on `closure U × [0, b)` whenever
`b` is at most both final times. -/
theorem eqOn_of_truncSol {U : Set (E d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : E d → ℝ → ℝ} (hf : SemilinearHyp f (closure U)) {g : E d → ℝ} {b₁ b₂ b : ℝ}
    (h₁ : b ≤ b₁) (h₂ : b ≤ b₂) {v w : E d × ℝ → ℝ}
    (hv : IsTruncSol U f g b₁ v) (hw : IsTruncSol U f g b₂ w) :
    EqOn v w (closure U ×ˢ Ico 0 b) := by
  intro p hp
  set b' := (p.2 + b) / 2 with hb'_def
  have hp2 := hp.2
  have hb'0 : 0 < b' := by rw [hb'_def]; linarith [hp2.1, hp2.2]
  have hb'b : b' < b := by rw [hb'_def]; linarith [hp2.2]
  have hp' : p ∈ closure U ×ˢ Ico 0 b' := ⟨hp.1, hp2.1, by rw [hb'_def]; linarith [hp2.2]⟩
  exact le_antisymm
    (le_of_truncSol hU hUb hf hb'0 (hb'b.trans_le h₁) (hb'b.trans_le h₂) hv hw p hp')
    (le_of_truncSol hU hUb hf hb'0 (hb'b.trans_le h₂) (hb'b.trans_le h₁) hw hv p hp')

/-- **Viscosity existence on `U × (0, ∞)`.** For `U` open, bounded, with `C²` boundary,
`SemilinearHyp f (closure U)` and `g` continuous on `closure U`, there is `u`, continuous on
`closure U × [0, ∞)`, a viscosity solution of `dₜu = lapₓu − f(x, u)` on `U × (0, ∞)`, with `u = g`
on `closure U × {0}` and on `frontier U × [0, ∞)`. -/
theorem exists_viscSolution_semilinear_Ioi {U : Set (E d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hC2 : HasC2Boundary U) {f : E d → ℝ → ℝ}
    (hf : SemilinearHyp f (closure U)) {g : E d → ℝ} (hg : ContinuousOn g (closure U)) :
    ∃ u : E d × ℝ → ℝ, ContinuousOn u (closure U ×ˢ Ici 0) ∧
      IsViscSolOn (U ×ˢ Ioi 0) (fun p z ↦ f p.1 z) u ∧
      (∀ x ∈ closure U, u (x, 0) = g x) ∧ ∀ x ∈ frontier U, ∀ t : ℝ, 0 ≤ t → u (x, t) = g x := by
  -- truncation: the truncated solutions `sol n` on `U × (0, n + 1)`
  choose sol hsol using fun n : ℕ ↦
    exists_truncSol hU hUb hC2 hf hg (b := (n : ℝ) + 1) (by positivity)
  -- gluing: the glued function
  set u : E d × ℝ → ℝ := fun p ↦ sol ⌊p.2⌋₊ p with hu_def
  have hglue : ∀ n : ℕ, EqOn u (sol n) (closure U ×ˢ Ico 0 ((n : ℝ) + 1)) := by
    intro n q hq
    have hq0 : 0 ≤ q.2 := hq.2.1
    have hN : ⌊q.2⌋₊ ≤ n := by
      have : ⌊q.2⌋₊ < n + 1 := (Nat.floor_lt hq0).2 (by exact_mod_cast hq.2.2)
      omega
    exact eqOn_of_truncSol hU hUb hf (b := (⌊q.2⌋₊ : ℝ) + 1) le_rfl
      (by exact_mod_cast Nat.add_le_add_right hN 1) (hsol _) (hsol n)
      ⟨hq.1, hq0, Nat.lt_floor_add_one _⟩
  have hsub : ∀ n : ℕ, closure U ×ˢ Ico 0 ((n : ℝ) + 1) ⊆
      U ×ˢ Ioo 0 ((n : ℝ) + 1) ∪ parBdry U 0 ((n : ℝ) + 1) :=
    fun n ↦ closure_prod_Ico_subset hU _
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · -- continuity on `closure U × [0, ∞)`
    intro p hp
    set n := ⌊p.2⌋₊
    have hpn : p.2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmem : closure U ×ˢ Ico 0 ((n : ℝ) + 1) ∈ 𝓝[closure U ×ˢ Ici 0] p :=
      mem_nhdsWithin.2 ⟨{q | q.2 < (n : ℝ) + 1}, isOpen_lt continuous_snd continuous_const, hpn,
        fun q hq ↦ ⟨hq.2.1, hq.2.2, hq.1⟩⟩
    have hpI : p ∈ closure U ×ˢ Ico 0 ((n : ℝ) + 1) := ⟨hp.1, hp.2, hpn⟩
    have hc : ContinuousWithinAt (sol n) (closure U ×ˢ Ico 0 ((n : ℝ) + 1)) p :=
      ((hsol n).1.mono (hsub n)) p hpI
    exact (hc.congr (hglue n) (hglue n hpI)).mono_of_mem_nhdsWithin hmem
  · -- viscosity solution on `U × (0, ∞)`, locally equal to `sol n`
    have hΩ : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
    have hloc : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), ∃ n : ℕ, p ∈ U ×ˢ Ioo 0 ((n : ℝ) + 1) ∧
        U ×ˢ Ioo 0 ((n : ℝ) + 1) ⊆ U ×ˢ Ioi 0 ∧ EqOn u (sol n) (U ×ˢ Ioo 0 ((n : ℝ) + 1)) :=
      fun p hp ↦ ⟨⌊p.2⌋₊, ⟨hp.1, hp.2, Nat.lt_floor_add_one _⟩,
        prod_mono subset_rfl Ioo_subset_Ioi_self,
        fun q hq ↦ hglue _ ⟨subset_closure hq.1, hq.2.1.le, hq.2.2⟩⟩
    refine ⟨IsViscSubOn.of_locally hΩ fun p hp ↦ ?_, IsViscSuperOn.of_locally hΩ fun p hp ↦ ?_⟩
    · obtain ⟨n, hpn, hsubn, heq⟩ := hloc p hp
      exact ⟨_, hU.prod isOpen_Ioo, hpn, hsubn, (IsViscSubOn.congr heq).2 (hsol n).2.1⟩
    · obtain ⟨n, hpn, hsubn, heq⟩ := hloc p hp
      exact ⟨_, hU.prod isOpen_Ioo, hpn, hsubn, (IsViscSuperOn.congr heq).2 (hsol n).2.2.1⟩
  · -- initial data
    intro x hx
    have h0 : ((x, (0 : ℝ)) : E d × ℝ) ∈ parBdry U 0 (((0 : ℕ) : ℝ) + 1) :=
      Or.inl ⟨hx, rfl⟩
    simpa [hu_def] using (hsol 0).2.2.2 h0
  · -- lateral data
    intro x hx t ht
    have hmem : ((x, t) : E d × ℝ) ∈ parBdry U 0 ((⌊t⌋₊ : ℝ) + 1) :=
      Or.inr ⟨hx, ht, (Nat.lt_floor_add_one t).le⟩
    exact (hsol ⌊t⌋₊).2.2.2 hmem

/-- The whole space has `C²` boundary (`ρ ≡ -1`; the frontier is empty). -/
theorem hasC2Boundary_univ : HasC2Boundary (univ : Set (E d)) :=
  ⟨fun _ ↦ -1, contDiff_const, by ext; simp, by simp⟩

/-- `d = 0` regression check: on `E 0` (a point), `U = univ` is bounded with `C²` boundary, and the
existence theorem applies to arbitrary data `g` (continuous, `E 0` being a point). -/
example {f : E 0 → ℝ → ℝ} (hf : SemilinearHyp f (closure univ)) (g : E 0 → ℝ) :
    ∃ u : E 0 × ℝ → ℝ, ContinuousOn u (closure univ ×ˢ Ici 0) ∧
      IsViscSolOn (univ ×ˢ Ioi 0) (fun p z ↦ f p.1 z) u ∧
      (∀ x ∈ closure univ, u (x, 0) = g x) ∧
      ∀ x ∈ frontier (univ : Set (E 0)), ∀ t : ℝ, 0 ≤ t → u (x, t) = g x :=
  exists_viscSolution_semilinear_Ioi isOpen_univ
    ((Bornology.isBounded_singleton (x := 0)).subset fun x _ ↦ Subsingleton.elim x 0)
    hasC2Boundary_univ hf (continuous_of_discreteTopology (f := g)).continuousOn

end ParabolicBasic
