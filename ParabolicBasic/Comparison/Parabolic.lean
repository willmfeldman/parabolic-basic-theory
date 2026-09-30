/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Parabolic
public import ParabolicBasic.Defs.Viscosity
public import ParabolicBasic.Defs.Semilinear
public import ParabolicBasic.Comparison.SemilinearHyp
public import ParabolicBasic.Comparison.ExpChange
public import ParabolicBasic.Comparison.Frontier
public import ParabolicBasic.Viscosity.Invariance

/-!
# Comparison for USC/LSC viscosity sub/supersolutions

The proof:

1. change of unknown `w = e^{-λt} u` with `λ = L + 1` (`Comparison/ExpChange.lean`);
2. the clamped operator `clampOp` (globally proper with slope `1`, globally continuous, below the
   true operator on the closed cylinder, with a modulus uniform in `r ≤ M`);
3. the top penalty `w - η / (b' - t)`, redefined to a constant on `t ≥ b'`, which kills the top
   face of the cylinder `V × (a, b')`;
4. `comparison_frontier` (via `ViscositySolns`) on `V × (a, b')`, then `η → 0` and `b' → b`.

The top face `t = b` is never tested: the conclusion holds on `closure V ×ˢ Ico a b`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Cylinder geometry -/

/-- The closure of the open cylinder `V × (a, b)`. -/
theorem closure_prod_Ioo_eq (V : Set (E d)) {a b : ℝ} (hab : a < b) :
    closure (V ×ˢ Ioo a b) = closure V ×ˢ Icc a b := by
  rw [closure_prod_eq, closure_Ioo hab.ne]

/-- The frontier of the open cylinder `V × (a, b)` is the parabolic boundary plus the top face. -/
theorem frontier_prod_Ioo_subset (V : Set (E d)) (a b : ℝ) :
    frontier (V ×ˢ Ioo a b) ⊆ parBdry V a b ∪ closure V ×ˢ {b} := by
  rcases lt_or_ge a b with hab | hab
  · rw [frontier_prod_eq, frontier_Ioo hab, closure_Ioo hab.ne]
    rintro p (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
    · rcases hp2 with hp2 | hp2
      · exact Or.inl (Or.inl ⟨hp1, hp2⟩)
      · exact Or.inr ⟨hp1, hp2⟩
    · exact Or.inl (Or.inr ⟨hp1, hp2⟩)
  · rw [Ioo_eq_empty (not_lt.2 hab), prod_empty, frontier_empty]
    exact empty_subset _

/-- The parabolic boundary grows with the final time. -/
theorem parBdry_subset_parBdry (V : Set (E d)) (a : ℝ) {b' b : ℝ} (hb : b' ≤ b) :
    parBdry V a b' ⊆ parBdry V a b := by
  rintro p (hp | ⟨hp1, hp2⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨hp1, hp2.1, hp2.2.trans hb⟩

/-- The parabolic boundary lies in the closed cylinder. -/
theorem parBdry_subset_closure (V : Set (E d)) {a b : ℝ} (hab : a ≤ b) :
    parBdry V a b ⊆ closure V ×ˢ Icc a b := by
  rintro p (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
  · rw [mem_singleton_iff] at hp2
    exact ⟨hp1, by rw [hp2]; exact ⟨le_rfl, hab⟩⟩
  · exact ⟨frontier_subset_closure hp1, hp2⟩

/-- A point of `closure V × [a, b)` outside the open cylinder lies on the parabolic boundary. -/
theorem mem_parBdry_of_notMem {V : Set (E d)} (hV : IsOpen V) {a b : ℝ} {p : E d × ℝ}
    (hp : p ∈ closure V ×ˢ Ico a b) (hpQ : p ∉ V ×ˢ Ioo a b) : p ∈ parBdry V a b := by
  by_cases hp1 : p.1 ∈ V
  · have hp2 : p.2 = a := by
      by_contra h
      exact hpQ ⟨hp1, lt_of_le_of_ne hp.2.1 (Ne.symm h), hp.2.2⟩
    exact Or.inl ⟨hp.1, hp2⟩
  · refine Or.inr ⟨?_, hp.2.1, hp.2.2.le⟩
    rw [hV.frontier_eq]
    exact ⟨hp.1, hp1⟩

/-! ### The clamped operator -/

/-- The clamped operator:
`G p r = λ r + L min(r + K, 0) + e^{-λt} (g(x, e^{λt} max(r, -K)) - S p)`. -/
noncomputable def clampOp (g : E d → ℝ → ℝ) (S : E d × ℝ → ℝ) (lam L K : ℝ) (p : E d × ℝ)
    (r : ℝ) : ℝ :=
  lam * r + L * min (r + K) 0 +
    Real.exp (-(lam * p.2)) * (g p.1 (Real.exp (lam * p.2) * max r (-K)) - S p)

/-- **(G1)** Uniform slope `1`, globally in `p`. -/
theorem clampOp_slope {g : E d → ℝ → ℝ} {S : E d × ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x z w, |g x z - g x w| ≤ L * |z - w|) (K : ℝ) (p : E d × ℝ) {r s : ℝ}
    (hrs : r ≤ s) :
    clampOp g S (L + 1) L K p r + 1 * (s - r) ≤ clampOp g S (L + 1) L K p s := by
  unfold clampOp
  set e := Real.exp ((L + 1) * p.2) with he
  set e' := Real.exp (-((L + 1) * p.2)) with he'
  have hepos : 0 < e := Real.exp_pos _
  have he'pos : 0 < e' := Real.exp_pos _
  have hee' : e' * e = 1 := by rw [he, he', ← Real.exp_add]; simp
  have hm0 : max r (-K) ≤ max s (-K) := max_le_max hrs le_rfl
  have hm1 : max s (-K) - max r (-K) ≤ s - r := by
    rcases le_total s (-K) with h | h
    · rw [max_eq_right h, max_eq_right (hrs.trans h)]; linarith
    · rw [max_eq_left h]
      rcases le_total r (-K) with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']
  have hmin : min (r + K) 0 ≤ min (s + K) 0 := min_le_min (by linarith) le_rfl
  have hgl := hg p.1 (e * max s (-K)) (e * max r (-K))
  rw [← mul_sub, abs_mul, abs_of_pos hepos, abs_of_nonneg (sub_nonneg.2 hm0)] at hgl
  have hgl' : -(L * (e * (max s (-K) - max r (-K)))) ≤
      g p.1 (e * max s (-K)) - g p.1 (e * max r (-K)) := (abs_le.1 hgl).1
  have key : -(L * (max s (-K) - max r (-K))) ≤
      e' * (g p.1 (e * max s (-K)) - g p.1 (e * max r (-K))) := by
    have := mul_le_mul_of_nonneg_left hgl' he'pos.le
    calc -(L * (max s (-K) - max r (-K)))
        = e' * -(L * (e * (max s (-K) - max r (-K)))) := by
          rw [show e' * -(L * (e * (max s (-K) - max r (-K)))) =
            -(L * ((e' * e) * (max s (-K) - max r (-K)))) by ring, hee', one_mul]
      _ ≤ _ := this
  have hLm : L * (max s (-K) - max r (-K)) ≤ L * (s - r) := mul_le_mul_of_nonneg_left hm1 hL
  have hLmin : L * min (r + K) 0 ≤ L * min (s + K) 0 := mul_le_mul_of_nonneg_left hmin hL
  nlinarith

/-- **(G2)** Global joint continuity. -/
theorem continuous_clampOp {g : E d → ℝ → ℝ} {S : E d × ℝ → ℝ}
    (hg : Continuous fun q : E d × ℝ ↦ g q.1 q.2) (hS : Continuous S) (lam L K : ℝ) :
    Continuous fun q : (E d × ℝ) × ℝ ↦ clampOp g S lam L K q.1 q.2 := by
  unfold clampOp
  have ht : Continuous fun q : (E d × ℝ) × ℝ ↦ q.1.2 := continuous_snd.comp continuous_fst
  have hgc : Continuous fun q : (E d × ℝ) × ℝ ↦
      g q.1.1 (Real.exp (lam * q.1.2) * max q.2 (-K)) :=
    hg.comp ((continuous_fst.comp continuous_fst).prodMk
      ((Real.continuous_exp.comp (continuous_const.mul ht)).mul
        (continuous_snd.max continuous_const)))
  exact ((continuous_const.mul continuous_snd).add
    (continuous_const.mul ((continuous_snd.add continuous_const).min continuous_const))).add
    ((Real.continuous_exp.comp (continuous_const.mul ht).neg).mul
      (hgc.sub (hS.comp continuous_fst)))

/-- **(G3)** Below the true (transformed) operator, with equality for `r ≥ -K`. -/
theorem clampOp_le {g f : E d → ℝ → ℝ} {S' S : E d × ℝ → ℝ} {lam L K : ℝ} {p : E d × ℝ}
    (hL : ∀ z w, |f p.1 z - f p.1 w| ≤ L * |z - w|) (hg : ∀ z, g p.1 z = f p.1 z)
    (hS : S' p = S p) (r : ℝ) :
    clampOp g S' lam L K p r ≤
      lam * r + Real.exp (-(lam * p.2)) * (f p.1 (Real.exp (lam * p.2) * r) - S p) := by
  unfold clampOp
  rw [hg, hS]
  set e := Real.exp (lam * p.2) with he
  set e' := Real.exp (-(lam * p.2)) with he'
  have hepos : 0 < e := Real.exp_pos _
  have he'pos : 0 < e' := Real.exp_pos _
  have hee' : e' * e = 1 := by rw [he, he', ← Real.exp_add]; simp
  rcases le_total (-K) r with h | h
  · rw [max_eq_left h, min_eq_right (by linarith)]
    simp
  · rw [max_eq_right h, min_eq_left (by linarith)]
    have h1 := hL (e * r) (e * -K)
    rw [← mul_sub, abs_mul, abs_of_pos hepos, abs_of_nonpos (show r - -K ≤ 0 by linarith)] at h1
    have h2 : f p.1 (e * -K) + L * (e * (r + K)) ≤ f p.1 (e * r) := by
      have := (abs_le.1 h1).1
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 he'pos.le
    have h4 : e' * (L * (e * (r + K))) = L * (r + K) := by
      rw [show e' * (L * (e * (r + K))) = L * ((e' * e) * (r + K)) by ring, hee', one_mul]
    nlinarith

theorem clampOp_eq {g f : E d → ℝ → ℝ} {S' S : E d × ℝ → ℝ} {lam L K : ℝ} {p : E d × ℝ}
    (hg : ∀ z, g p.1 z = f p.1 z) (hS : S' p = S p) {r : ℝ} (hr : -K ≤ r) :
    clampOp g S' lam L K p r =
      lam * r + Real.exp (-(lam * p.2)) * (f p.1 (Real.exp (lam * p.2) * r) - S p) := by
  unfold clampOp
  rw [hg, hS, max_eq_left hr, min_eq_right (by linarith)]
  simp

/-- **(G4)** A monotone comparison modulus on a compact set, uniform in `r ≤ M`. -/
theorem exists_modulus_clampOp {g : E d → ℝ → ℝ} {S : E d × ℝ → ℝ}
    (hg : Continuous fun q : E d × ℝ ↦ g q.1 q.2) (hS : Continuous S) (lam L : ℝ) {K M : ℝ}
    (hKM : -K ≤ M) {C : Set (E d × ℝ)} (hC : IsCompact C) :
    ∃ ρ : ℝ → ℝ, ViscositySolns.ComparisonModulus ρ ∧ Monotone ρ ∧
      ∀ p ∈ C, ∀ q ∈ C, ∀ r ≤ M, clampOp g S lam L K q r - clampOp g S lam L K p r ≤
        ρ (dist p q) := by
  set h : E d × ℝ → ℝ → ℝ := fun p m ↦
    Real.exp (-(lam * p.2)) * (g p.1 (Real.exp (lam * p.2) * m) - S p) with hh
  have hcont : Continuous fun q : (E d × ℝ) × ℝ ↦ h q.1 q.2 := by
    have ht : Continuous fun q : (E d × ℝ) × ℝ ↦ q.1.2 := continuous_snd.comp continuous_fst
    exact (Real.continuous_exp.comp (continuous_const.mul ht).neg).mul
      ((hg.comp ((continuous_fst.comp continuous_fst).prodMk
        ((Real.continuous_exp.comp (continuous_const.mul ht)).mul continuous_snd))).sub
        (hS.comp continuous_fst))
  obtain ⟨ρ, hρ, hρm, hρb⟩ :=
    exists_comparisonModulus_of_isCompact hC isCompact_Icc (g := h) hcont.continuousOn
  refine ⟨ρ, hρ, hρm, fun p hp q hq r hr ↦ ?_⟩
  have hm : max r (-K) ∈ Icc (-K) M := ⟨le_max_right _ _, max_le hr hKM⟩
  have := hρb p hp q hq _ hm
  have heq : clampOp g S lam L K q r - clampOp g S lam L K p r =
      h q (max r (-K)) - h p (max r (-K)) := by
    simp only [clampOp, hh]; ring
  rw [heq]
  exact (le_abs_self _).trans this

/-! ### The top penalty -/

/-- The top-penalized function `w - η / (b' - t)` for `t < b'`, and the constant `c` for
`t ≥ b'`. -/
noncomputable def topPenalty (w : E d × ℝ → ℝ) (b' η c : ℝ) (p : E d × ℝ) : ℝ :=
  if p.2 < b' then w p - η / (b' - p.2) else c

/-- The penalized function is USC wherever `w` is USC and bounded above by `M ≥ c`. -/
theorem upperSemicontinuousOn_topPenalty {w : E d × ℝ → ℝ} {s : Set (E d × ℝ)} {b' η c M : ℝ}
    (hη : 0 < η) (hcM : c ≤ M) (hw : UpperSemicontinuousOn w s) (hwM : ∀ p ∈ s, w p ≤ M) :
    UpperSemicontinuousOn (topPenalty w b' η c) s := by
  intro p hp
  by_cases hpb : p.2 < b'
  · -- near `p`, the penalized function is `w + φ` with `φ` continuous
    have hφ : ContinuousAt (fun q : E d × ℝ ↦ -(η / (b' - q.2))) p :=
      (continuousAt_const.div (continuousAt_const.sub continuous_snd.continuousAt)
        (sub_pos.2 hpb).ne').neg
    have hsum : UpperSemicontinuousWithinAt (fun q ↦ w q + -(η / (b' - q.2))) s p :=
      UpperSemicontinuousWithinAt.add (hw p hp)
        hφ.continuousWithinAt.upperSemicontinuousWithinAt
    refine hsum.congr_of_eventuallyEq hp ?_
    have hopen : {q : E d × ℝ | q.2 < b'} ∈ 𝓝[s] p :=
      mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_snd continuous_const).mem_nhds hpb)
    filter_upwards [hopen] with q hq
    simp only [topPenalty, ite_eq_left hq]
    ring
  · intro y hy
    simp only [topPenalty, ite_eq_right hpb] at hy
    set θ := η / (M - c + 1) with hθ
    have hθpos : 0 < θ := div_pos hη (by linarith)
    have hnear : {q : E d × ℝ | b' - θ < q.2} ∈ 𝓝[s] p :=
      mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const continuous_snd).mem_nhds
        (by simp only [mem_ofPred_eq]; linarith [not_lt.1 hpb]))
    filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqs
    unfold topPenalty
    split_ifs with hqb
    · have hδ : 0 < b' - q.2 := sub_pos.2 hqb
      have hlt : M - c + 1 < η / (b' - q.2) := by
        rw [lt_div_iff₀ hδ]
        have : (M - c + 1) * θ = η := by
          rw [hθ, mul_div_cancel₀ _ (by linarith : M - c + 1 ≠ 0)]
        nlinarith
      linarith [hwM q hqs]
    · exact hy

/-- The penalized function is a subsolution on `V × (a, b')` whenever `w` is and `G` is
nondecreasing in `r`. -/
theorem isViscSubOn_topPenalty {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {b' η c : ℝ}
    (hΩb : ∀ p ∈ Ω, p.2 < b') (hη : 0 ≤ η) {G : E d × ℝ → ℝ → ℝ}
    (hG : ∀ p, Monotone (G p)) {w : E d × ℝ → ℝ} (hw : IsViscSubOn Ω G w) :
    IsViscSubOn Ω G (topPenalty w b' η c) := by
  set φ : E d × ℝ → ℝ := fun q ↦ -(η / (b' - q.2)) with hφdef
  have hφ : ContDiffOn ℝ 2 φ Ω := by
    refine (contDiffOn_const.div (contDiffOn_const.sub contDiff_snd.contDiffOn)
      fun q hq ↦ (sub_pos.2 (hΩb q hq)).ne').neg
  have h1 := hw.add_contDiff hΩ hφ
  have hdt : ∀ p ∈ Ω, dₜ φ p ≤ 0 := by
    intro p hp
    have hδ : b' - p.2 ≠ 0 := (sub_pos.2 (hΩb p hp)).ne'
    have hder : HasDerivAt (fun s : ℝ ↦ -(η / (b' - s))) (-((0 * (b' - p.2) - η * (0 - 1)) /
        (b' - p.2) ^ 2)) p.2 :=
      ((hasDerivAt_const p.2 η).div ((hasDerivAt_const p.2 b').sub (hasDerivAt_id p.2)) hδ).neg
    change deriv (fun s : ℝ ↦ -(η / (b' - s))) p.2 ≤ 0
    rw [hder.deriv]
    have : 0 ≤ (0 * (b' - p.2) - η * (0 - 1)) / (b' - p.2) ^ 2 := by
      apply div_nonneg _ (sq_nonneg _); linarith
    linarith
  have hlap : ∀ p, lapₓ φ p = 0 := by
    intro p
    change Δ (fun _ : E d ↦ -(η / (b' - p.2))) p.1 = 0
    simp
  have h2 : IsViscSubOn Ω G (fun p ↦ w p + φ p) := by
    refine h1.mono_source fun p hp z ↦ ?_
    rw [hlap p]
    have hmono : G p z ≤ G p (z - φ p) := hG p (by
      simp only [hφdef]
      have : 0 ≤ η / (b' - p.2) := div_nonneg hη (sub_pos.2 (hΩb p hp)).le
      linarith)
    linarith [hdt p hp]
  refine (IsViscSubOn.congr fun p hp ↦ ?_).1 h2
  simp only [topPenalty, ite_eq_left (hΩb p hp), hφdef, sub_eq_add_neg]

/-! ### The comparison theorem -/

/-- **Comparison with a source `S`.** A USC subsolution and an LSC supersolution of
`dₜu - lapₓu + f(x, u) - S = 0` on `V × (a, b)`, ordered on the parabolic boundary, are ordered on
`closure V ×ˢ Ico a b`. -/
theorem comparison_usc_lsc_source {V : Set (E d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {a b : ℝ} (_hab : a < b) {f : E d → ℝ → ℝ}
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ closure V, ∀ y ∈ closure V, ∀ z,
      |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ closure V, ∀ z w, |f x z - f x w| ≤ L * |z - w|)
    {S : E d × ℝ → ℝ} (hS : ContinuousOn S (closure V ×ˢ Icc a b))
    {u v : E d × ℝ → ℝ} (husc : UpperSemicontinuousOn u (closure V ×ˢ Icc a b))
    (hvlsc : LowerSemicontinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsViscSubOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z - S p) u)
    (hsuper : IsViscSuperOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z - S p) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Ico a b, u p ≤ v p := by
  intro p₀ hp₀
  by_cases hp₀Q : p₀ ∉ V ×ˢ Ioo a b
  · exact hbdry p₀ (mem_parBdry_of_notMem hV hp₀ hp₀Q)
  rw [not_not] at hp₀Q
  -- Step 1: data, extensions, constants
  set Qc : Set (E d × ℝ) := closure V ×ˢ Icc a b with hQc
  have hQcc : IsCompact Qc := hVb.isCompact_closure.prod isCompact_Icc
  have hQcne : Qc.Nonempty := ⟨p₀, subset_closure hp₀Q.1, hp₀Q.2.1.le, hp₀Q.2.2.le⟩
  have hQsub : V ×ˢ Ioo a b ⊆ Qc :=
    prod_mono subset_closure Ioo_subset_Icc_self
  obtain ⟨g, hgf, -, ⟨L, hL0, hL⟩, hgc⟩ := exists_holderLip_extension hfx hfz
  obtain ⟨S', hS'c, hS'S⟩ :=
    exists_continuous_eqOn_of_continuousOn (isClosed_closure.prod isClosed_Icc) hS
  set lam : ℝ := L + 1 with hlam
  set wu : E d × ℝ → ℝ := fun p ↦ Real.exp (-(lam * p.2)) * u p with hwu
  set wv : E d × ℝ → ℝ := fun p ↦ Real.exp (-(lam * p.2)) * v p with hwv
  have hexpc : ContinuousOn (fun p : E d × ℝ ↦ Real.exp (-(lam * p.2))) Qc :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd).neg).continuousOn
  have hwuusc : UpperSemicontinuousOn wu Qc :=
    UpperSemicontinuousOn.mul_continuousOn_pos husc hexpc fun _ _ ↦ Real.exp_pos _
  have hwvlsc : LowerSemicontinuousOn wv Qc :=
    LowerSemicontinuousOn.mul_continuousOn_pos hvlsc hexpc fun _ _ ↦ Real.exp_pos _
  obtain ⟨pmin, -, hpmin⟩ := hwvlsc.exists_isMinOn hQcne hQcc
  obtain ⟨pmax, -, hpmax⟩ := hwuusc.exists_isMaxOn hQcne hQcc
  set K : ℝ := |wv pmin| + 1 with hK
  set M : ℝ := max (wu pmax) (-K) with hM
  have hwvK : ∀ p ∈ Qc, -K < wv p := fun p hp ↦ by
    have := hpmin hp
    simp only [mem_ofPred_eq] at this
    linarith [neg_abs_le (wv pmin)]
  have hwuM : ∀ p ∈ Qc, wu p ≤ M := fun p hp ↦ (hpmax hp).trans (le_max_left _ _)
  have hKM : -K ≤ M := le_max_right _ _
  set G := clampOp g S' lam L K with hG
  have hG1 : ∀ p r s, r ≤ s → G p r + 1 * (s - r) ≤ G p s :=
    fun p r s hrs ↦ clampOp_slope hL0 hL K p hrs
  have hGmono : ∀ p, Monotone (G p) := fun p r s hrs ↦ by
    have := hG1 p r s hrs; nlinarith
  have hGc : Continuous fun q : (E d × ℝ) × ℝ ↦ G q.1 q.2 := continuous_clampOp hgc hS'c _ _ _
  obtain ⟨ρ, hρ, hρm, hρb⟩ := exists_modulus_clampOp hgc hS'c lam L hKM hQcc
  have hfL : ∀ p ∈ Qc, ∀ z w, |f p.1 z - f p.1 w| ≤ L * |z - w| := fun p hp z w ↦ by
    rw [← hgf p.1 hp.1 z, ← hgf p.1 hp.1 w]; exact hL _ _ _
  -- Step 2: the transformed functions solve the clamped equation on `Q`
  have hwu_sub : IsViscSubOn (V ×ˢ Ioo a b) G wu :=
    (hsub.exp_change lam).mono_source fun p hp z ↦
      clampOp_le (hfL p (hQsub hp)) (hgf p.1 (hQsub hp).1) (hS'S (hQsub hp)) z
  have hwv_super : IsViscSuperOn (V ×ˢ Ioo a b) G wv :=
    (IsViscSuperOn.congr_source_graph fun p hp ↦
      clampOp_eq (hgf p.1 (hQsub hp).1) (hS'S (hQsub hp)) (hwvK p (hQsub hp)).le).1
      (hsuper.exp_change lam)
  -- Step 3: comparison below `b'`, for every `η > 0`
  have step3 : ∀ b', a < b' → b' ≤ b → ∀ η, 0 < η →
      ∀ p ∈ V ×ˢ Ioo a b', topPenalty wu b' η (-K) p ≤ wv p := by
    intro b' hab' hb'b η hη
    have hQ'sub : V ×ˢ Ioo a b' ⊆ V ×ˢ Ioo a b := prod_mono le_rfl (Ioo_subset_Ioo_right hb'b)
    have hQ'o : IsOpen (V ×ˢ Ioo a b') := hV.prod isOpen_Ioo
    have hclQ' : closure (V ×ˢ Ioo a b') ⊆ Qc := by
      rw [closure_prod_Ioo_eq V hab']
      exact prod_mono le_rfl (Icc_subset_Icc_right hb'b)
    refine comparison_frontier hQ'o (hVb.prod (Metric.isBounded_Ioo a b')) one_pos hG1 hGc
      ⟨ρ, hρ, hρm, fun p hp q hq r hr ↦ hρb p (hQsub (hQ'sub hp)) q (hQsub (hQ'sub hq)) r hr⟩
      (upperSemicontinuousOn_topPenalty hη hKM (hwuusc.mono hclQ')
        fun p hp ↦ hwuM p (hclQ' hp))
      (hwvlsc.mono hclQ') (fun p hp ↦ ?_)
      (isViscSubOn_topPenalty hQ'o (fun p hp ↦ hp.2.2) hη.le hGmono
        (hwu_sub.mono_set hQ'o hQ'sub))
      (hwv_super.mono_set hQ'o hQ'sub) (fun p hp ↦ ?_)
    · -- `topPenalty ≤ M` on `Q'`
      unfold topPenalty
      rw [ite_eq_left hp.2.2]
      have : 0 ≤ η / (b' - p.2) := div_nonneg hη.le (sub_pos.2 hp.2.2).le
      linarith [hwuM p (hQsub (hQ'sub hp))]
    · -- the frontier
      have hpc : p ∈ Qc := hclQ' (frontier_subset_closure hp)
      unfold topPenalty
      split_ifs with hpb
      · have hpΓ : p ∈ parBdry V a b := by
          rcases frontier_prod_Ioo_subset V a b' hp with h | h
          · exact parBdry_subset_parBdry V a hb'b h
          · exact absurd h.2 (by rw [mem_singleton_iff]; exact hpb.ne)
        have huv := hbdry p hpΓ
        have h1 : wu p ≤ wv p := mul_le_mul_of_nonneg_left huv (Real.exp_pos _).le
        have : 0 ≤ η / (b' - p.2) := div_nonneg hη.le (sub_pos.2 hpb).le
        linarith
      · exact (hwvK p hpc).le
  -- Step 4: `η → 0`
  set b' : ℝ := (p₀.2 + b) / 2 with hb'
  have hpb' : p₀.2 < b' := by rw [hb']; linarith [hp₀Q.2.2]
  have hab' : a < b' := hp₀Q.2.1.trans hpb'
  have hb'b : b' ≤ b := by rw [hb']; linarith [hp₀Q.2.2]
  have hp₀' : p₀ ∈ V ×ˢ Ioo a b' := ⟨hp₀Q.1, hp₀Q.2.1, hpb'⟩
  have hδ : 0 < b' - p₀.2 := sub_pos.2 hpb'
  have hw : wu p₀ ≤ wv p₀ := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have := step3 b' hab' hb'b (ε * (b' - p₀.2)) (mul_pos hε hδ) p₀ hp₀'
    simp only [topPenalty, ite_eq_left hpb'] at this
    rw [mul_div_assoc, div_self hδ.ne', mul_one] at this
    linarith
  exact le_of_mul_le_mul_left hw (Real.exp_pos _)

/-- Comparison for USC/LSC sub/supersolutions under `SemilinearHyp`. Boundedness of `u` above and
`v` below is automatic. The top face `t = b` is not claimed. -/
theorem comparison_usc_lsc {V : Set (E d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {a b : ℝ} (hab : a < b) {f : E d → ℝ → ℝ} (hf : SemilinearHyp f (closure V))
    {u v : E d × ℝ → ℝ} (husc : UpperSemicontinuousOn u (closure V ×ˢ Icc a b))
    (hvlsc : LowerSemicontinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsViscSubOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) u)
    (hsuper : IsViscSuperOn (V ×ˢ Ioo a b) (fun p r ↦ f p.1 r) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Ico a b, u p ≤ v p := by
  have hF : (fun p z ↦ f p.1 z - (fun _ : E d × ℝ ↦ (0 : ℝ)) p) = fun p r ↦ f p.1 r := by
    funext p z; simp
  exact comparison_usc_lsc_source hV hVb hab hf.holder_x hf.lip_z continuousOn_const husc hvlsc
    (by rw [hF]; exact hsub) (by rw [hF]; exact hsuper) hbdry

end ParabolicBasic
