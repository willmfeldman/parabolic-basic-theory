/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Perron.Existence
public import ParabolicBasic.Barriers.Perron
public import ParabolicBasic.Caloric.Regularity
public import ParabolicBasic.Comparison.Continuous
public import ParabolicBasic.Comparison.SemilinearHyp
public import ParabolicBasic.Classical.ToViscosity

/-!
# The heat Dirichlet problem on ball cylinders

Given continuous data `g` on the parabolic boundary `Γ = parBdry (ball x₀ ρ) a b`, we extend it
in time by `g̃ (x, t) = g (x, min t b)` (no Tietze extension), solve the Perron problem for
the heat equation on the longer cylinder `ball x₀ ρ ×ˢ Ioo a (b + 1)` (with exterior-sphere
barriers), upgrade the viscosity solution to a smooth caloric function, and restrict to
`closedBall x₀ ρ ×ˢ Icc a b`. The resulting solution is smooth across the top face `t = b`.

## Main results

* `caloric_dirichlet_ball_ext`: the extended-in-time solution.
* `abs_le_of_isSmoothCaloricOn_ball`: the maximum-principle bound.
* `caloric_dirichlet_cCyl`: the centred-cylinder form used by the Schauder iteration.

The main theorem `caloric_dirichlet_ball` lives in `ParabolicBasic.MainTheorems` and is proved
from `caloric_dirichlet_ball_ext`.

Everything holds for all `d`, including `d = 0`, where the lateral boundary is empty.
-/

@[expose] public section

open Set Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Step 1: extending the data in time -/

/-- The time-truncated data `(x, t) ↦ g (x, min t b)` is continuous on the parabolic boundary
of any longer cylinder `V × (a, b']`. -/
theorem continuousOn_parBdry_min {V : Set (E d)} {a b b' : ℝ} (hab : a ≤ b)
    {g : E d × ℝ → ℝ} (hg : ContinuousOn g (parBdry V a b)) :
    ContinuousOn (fun p : E d × ℝ ↦ g (p.1, min p.2 b)) (parBdry V a b') := by
  have hmaps : MapsTo (fun p : E d × ℝ ↦ (p.1, min p.2 b)) (parBdry V a b') (parBdry V a b) := by
    rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
    · simp only [mem_singleton_iff] at ht
      subst ht
      exact Or.inl ⟨hx, by simp [min_eq_left hab]⟩
    · exact Or.inr ⟨hx, le_min ht.1 hab, min_le_right _ _⟩
  exact hg.comp (continuous_fst.prodMk (continuous_snd.min continuous_const)).continuousOn hmaps

/-- On the original parabolic boundary the time-truncated data agrees with `g`. -/
theorem parBdry_min_eq {V : Set (E d)} {a b : ℝ} (hab : a ≤ b) {g : E d × ℝ → ℝ} :
    EqOn (fun p : E d × ℝ ↦ g (p.1, min p.2 b)) g (parBdry V a b) := by
  rintro ⟨x, t⟩ (⟨_, ht⟩ | ⟨_, ht⟩)
  · simp only [mem_singleton_iff] at ht
    subst ht
    simp [min_eq_left hab]
  · simp [min_eq_left ht.2]

/-- Parabolic boundaries grow with the final time. -/
theorem parBdry_mono_right {V : Set (E d)} {a b b' : ℝ} (hbb' : b ≤ b') :
    parBdry V a b ⊆ parBdry V a b' :=
  union_subset_union_right _ (prod_mono subset_rfl (Icc_subset_Icc_right hbb'))

/-! ### Step 4: the restriction set lemma -/

/-- The closed cylinder `closedBall x₀ ρ × [a, b]` lies in the open cylinder over a longer time
interval together with its parabolic boundary. -/
theorem closedBall_prod_Icc_subset (x₀ : E d) {ρ : ℝ} (hρ : 0 < ρ) {a b b' : ℝ} (hbb' : b < b') :
    closedBall x₀ ρ ×ˢ Icc a b ⊆ ball x₀ ρ ×ˢ Ioo a b' ∪ parBdry (ball x₀ ρ) a b' := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  rw [parBdry, closure_ball x₀ hρ.ne', frontier_ball x₀ hρ.ne']
  rcases eq_or_lt_of_le ht.1 with hta | hta
  · exact Or.inr (Or.inl ⟨hx, hta.symm⟩)
  rcases eq_or_lt_of_le (mem_closedBall.1 hx) with hxρ | hxρ
  · exact Or.inr (Or.inr ⟨hxρ, ht.1, ht.2.trans hbb'.le⟩)
  · exact Or.inl ⟨hxρ, hta, ht.2.trans_lt hbb'⟩

/-! ### Steps 2–4: assembly -/

/-- The heat Dirichlet problem on a ball cylinder, with a solution that is smooth caloric on the
extended cylinder `ball x₀ ρ × (a, b + 1)`. -/
theorem caloric_dirichlet_ball_ext (x₀ : E d) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (hab : a < b)
    {g : E d × ℝ → ℝ} (hg : ContinuousOn g (parBdry (ball x₀ ρ) a b)) :
    ∃ h : E d × ℝ → ℝ, ContinuousOn h (closedBall x₀ ρ ×ˢ Icc a b) ∧
      IsSmoothCaloricOn (ball x₀ ρ ×ˢ Ioo a (b + 1)) h ∧ EqOn h g (parBdry (ball x₀ ρ) a b) := by
  have hbb' : b < b + 1 := lt_add_one b
  have hab' : a < b + 1 := hab.trans hbb'
  have hg' := continuousOn_parBdry_min (b' := b + 1) hab.le hg
  obtain ⟨u, hu, hsub, hsuper, hug⟩ :=
    exists_viscSolution_cyl isOpen_ball isBounded_ball hab' (SemilinearHyp.zero _) hg'
      (perronBarriers_ball x₀ hρ hab' (SemilinearHyp.zero _) hg')
  have hcal : IsSmoothCaloricOn (ball x₀ ρ ×ˢ Ioo a (b + 1)) u :=
    isSmoothCaloricOn_of_isVisc (isOpen_ball.prod isOpen_Ioo) (hu.mono subset_union_left)
      hsub hsuper
  refine ⟨u, hu.mono (closedBall_prod_Icc_subset x₀ hρ hbb'), hcal, fun p hp ↦ ?_⟩
  rw [hug (parBdry_mono_right hbb'.le hp)]
  exact parBdry_min_eq hab.le hp

/-! ### The maximum-principle bound -/

/-- A function continuous on `closedBall x₀ ρ × [a, b]` and smooth caloric on the open cylinder is
bounded in absolute value by any bound of its parabolic-boundary values. Proof: comparison with the
caloric constants `±M`. -/
theorem abs_le_of_isSmoothCaloricOn_ball (x₀ : E d) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (hab : a < b)
    {h : E d × ℝ → ℝ} (hc : ContinuousOn h (closedBall x₀ ρ ×ˢ Icc a b))
    (hcal : IsSmoothCaloricOn (ball x₀ ρ ×ˢ Ioo a b) h) {M : ℝ}
    (hM : ∀ q ∈ parBdry (ball x₀ ρ) a b, |h q| ≤ M) :
    ∀ q ∈ closedBall x₀ ρ ×ˢ Icc a b, |h q| ≤ M := by
  have hO : IsOpen (ball x₀ ρ ×ˢ Ioo a b) := isOpen_ball.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 h (ball x₀ ρ ×ˢ Ioo a b) :=
    hcal.1.of_le (WithTop.coe_le_coe.2 le_top)
  have hsub : IsViscSubOn (ball x₀ ρ ×ˢ Ioo a b) (fun _ _ ↦ 0) h :=
    isViscSubOn_of_contDiffOn hO h2 fun p hp ↦ by rw [hcal.2 p hp]; simp
  have hsuper : IsViscSuperOn (ball x₀ ρ ×ˢ Ioo a b) (fun _ _ ↦ 0) h :=
    isViscSuperOn_of_contDiffOn hO h2 fun p hp ↦ by rw [hcal.2 p hp]; simp
  have hconst_sub (c : ℝ) : IsViscSubOn (ball x₀ ρ ×ˢ Ioo a b) (fun _ _ ↦ 0)
      (fun _ ↦ c) :=
    isViscSubOn_of_contDiffOn hO contDiffOn_const fun p _ ↦ by simp [dₜ, lapₓ]
  have hconst_super (c : ℝ) : IsViscSuperOn (ball x₀ ρ ×ˢ Ioo a b) (fun _ _ ↦ 0)
      (fun _ ↦ c) :=
    isViscSuperOn_of_contDiffOn hO contDiffOn_const fun p _ ↦ by simp [dₜ, lapₓ]
  have hf := SemilinearHyp.zero (closure (ball x₀ ρ))
  have hc' : ContinuousOn h (closure (ball x₀ ρ) ×ˢ Icc a b) := by
    rwa [closure_ball x₀ hρ.ne']
  have hup := comparison_continuous (f := fun _ _ ↦ 0) isOpen_ball isBounded_ball hab
    hf.holder_x hf.lip_z hc' continuousOn_const hsub (hconst_super M)
    fun p hp ↦ (abs_le.1 (hM p hp)).2
  have hlo := comparison_continuous (f := fun _ _ ↦ 0) isOpen_ball isBounded_ball hab
    hf.holder_x hf.lip_z continuousOn_const hc' (hconst_sub (-M)) hsuper
    fun p hp ↦ (abs_le.1 (hM p hp)).1
  intro q hq
  rw [← closure_ball x₀ hρ.ne'] at hq
  exact abs_le.2 ⟨hlo q hq, hup q hq⟩

/-! ### The centred-cylinder form (for the Schauder iteration) -/

/-- The heat Dirichlet problem on the centred cylinder
`cCyl x₀ t₀ r = ball x₀ r × (t₀ - r², t₀ + r²)`, with the maximum-principle bound. -/
theorem caloric_dirichlet_cCyl (x₀ : E d) (t₀ : ℝ) {r : ℝ} (hr : 0 < r) {g : E d × ℝ → ℝ}
    (hg : ContinuousOn g (parBdry (ball x₀ r) (t₀ - r ^ 2) (t₀ + r ^ 2))) {M : ℝ}
    (hM : ∀ q ∈ parBdry (ball x₀ r) (t₀ - r ^ 2) (t₀ + r ^ 2), |g q| ≤ M) :
    ∃ h : E d × ℝ → ℝ, ContinuousOn h (closedBall x₀ r ×ˢ Icc (t₀ - r ^ 2) (t₀ + r ^ 2)) ∧
      IsSmoothCaloricOn (cCyl x₀ t₀ r) h ∧
      EqOn h g (parBdry (ball x₀ r) (t₀ - r ^ 2) (t₀ + r ^ 2)) ∧
      ∀ q ∈ closedBall x₀ r ×ˢ Icc (t₀ - r ^ 2) (t₀ + r ^ 2), |h q| ≤ M := by
  have hab : t₀ - r ^ 2 < t₀ + r ^ 2 := by nlinarith [pow_pos hr 2]
  obtain ⟨h, hc, hcal, heq⟩ := caloric_dirichlet_ball_ext x₀ hr hab hg
  have hsub : cCyl x₀ t₀ r ⊆ ball x₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2 + 1) :=
    prod_mono subset_rfl (Ioo_subset_Ioo_right (by linarith))
  have hcal' : IsSmoothCaloricOn (cCyl x₀ t₀ r) h :=
    ⟨hcal.1.mono hsub, fun p hp ↦ hcal.2 p (hsub hp)⟩
  refine ⟨h, hc, hcal', heq, abs_le_of_isSmoothCaloricOn_ball x₀ hr hab hc hcal' ?_⟩
  intro q hq
  rw [heq hq]
  exact hM q hq

/-! ### `d = 0` regression -/

/-- For `d = 0` the ball is the whole (one-point) space, so the parabolic boundary is only the
initial face. -/
theorem parBdry_ball_eq_of_zero (x₀ : E 0) {ρ : ℝ} (hρ : 0 < ρ) (a b : ℝ) :
    parBdry (ball x₀ ρ) a b = univ ×ˢ {a} := by
  have hball : ball x₀ ρ = univ :=
    eq_univ_of_forall fun y ↦ by simpa [Subsingleton.elim y x₀] using hρ
  simp [parBdry, hball]

/-- `d = 0` regression: the assembly needs no `1 ≤ d`. -/
example (x₀ : E 0) {g : E 0 × ℝ → ℝ} (hg : ContinuousOn g (parBdry (ball x₀ 1) 0 1)) :
    ∃ h : E 0 × ℝ → ℝ, ContinuousOn h (closedBall x₀ 1 ×ˢ Icc 0 1) ∧
      IsSmoothCaloricOn (ball x₀ 1 ×ˢ Ioo 0 (1 + 1)) h ∧ EqOn h g (parBdry (ball x₀ 1) 0 1) :=
  caloric_dirichlet_ball_ext x₀ one_pos zero_lt_one hg

/-- `d = 0` regression for the centred form. -/
example (x₀ : E 0) {g : E 0 × ℝ → ℝ}
    (hg : ContinuousOn g (parBdry (ball x₀ 1) (0 - 1 ^ 2) (0 + 1 ^ 2)))
    (hM : ∀ q ∈ parBdry (ball x₀ 1) (0 - 1 ^ 2) (0 + 1 ^ 2), |g q| ≤ 1) :
    ∃ h : E 0 × ℝ → ℝ, ContinuousOn h (closedBall x₀ 1 ×ˢ Icc (0 - 1 ^ 2) (0 + 1 ^ 2)) ∧
      IsSmoothCaloricOn (cCyl x₀ 0 1) h ∧
      EqOn h g (parBdry (ball x₀ 1) (0 - 1 ^ 2) (0 + 1 ^ 2)) ∧
      ∀ q ∈ closedBall x₀ 1 ×ˢ Icc (0 - 1 ^ 2) (0 + 1 ^ 2), |h q| ≤ 1 :=
  caloric_dirichlet_cCyl x₀ 0 one_pos hg hM

end ParabolicBasic
