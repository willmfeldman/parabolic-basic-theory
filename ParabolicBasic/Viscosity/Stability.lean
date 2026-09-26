/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Viscosity.Basic
public import ParabolicBasic.Viscosity.SliceAux

/-!
# Stability of viscosity solutions under locally uniform limits

Stability with varying sources: if `un n` are subsolutions for `Fn n` on the open set `Ω`,
`un n → u` locally uniformly on `Ω` with `u` USC, and `Fn n → F` locally uniformly on `Ω × ℝ` with
`F` continuous there, then `u` is a subsolution for `F`.

The proof is elementary (no transport): strictify the test with the quartic `ViscAux.quartic p`,
take maxima `P n` of `un n - ψ'` on a compact ball `K` around `p`; the two-sided estimate of Step 3
gives `P n → p` and `un n (P n) → u p` along the whole sequence, and one passes to the limit in the
test inequalities at `P n`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

theorem TendstoLocallyUniformlyOn.neg_real {ι α : Type*} [TopologicalSpace α] {F : ι → α → ℝ}
    {f : α → ℝ} {l : Filter ι} {s : Set α} (h : TendstoLocallyUniformlyOn F f l s) :
    TendstoLocallyUniformlyOn (fun n x ↦ -F n x) (fun x ↦ -f x) l s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at h ⊢
  intro ε hε x hx
  obtain ⟨t, ht, H⟩ := h ε hε x hx
  exact ⟨t, ht, H.mono fun n hn y hy ↦ by rw [dist_neg_neg]; exact hn y hy⟩

/-- Stability of subsolutions (varying zero-order term). -/
theorem IsViscSubOn.of_tendstoLocallyUniformlyOn {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {F : E d × ℝ → ℝ → ℝ} {Fn : ℕ → E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    {un : ℕ → E d × ℝ → ℝ}
    (hsub : ∀ᶠ n in atTop, IsViscSubOn Ω (Fn n) (un n))
    (hu : TendstoLocallyUniformlyOn un u atTop Ω) (husc : UpperSemicontinuousOn u Ω)
    (hF : TendstoLocallyUniformlyOn (fun n (q : (E d × ℝ) × ℝ) ↦ Fn n q.1 q.2)
      (fun q ↦ F q.1 q.2) atTop (Ω ×ˢ univ))
    (hFc : ContinuousOn (fun q : (E d × ℝ) × ℝ ↦ F q.1 q.2) (Ω ×ˢ univ)) :
    IsViscSubOn Ω F u := by
  refine ⟨husc, fun ψ hψ p hp ht ↦ ?_⟩
  /- Step 1: strictification. -/
  set ψ' : E d × ℝ → ℝ := fun q ↦ ψ q + ViscAux.quartic p q with hψ'_def
  have hσc : ContDiff ℝ 2 (ViscAux.quartic p) := ViscAux.contDiff_quartic p
  have hψ'c : ContDiff ℝ 2 ψ' := hψ.add hσc
  have hdt : dₜ ψ' p = dₜ ψ p := by
    rw [dₜ_add (hψ.differentiable two_ne_zero) (hσc.differentiable two_ne_zero),
      ViscAux.dₜ_quartic, add_zero]
  have hlap : lapₓ ψ' p = lapₓ ψ p := by
    rw [lapₓ_add hψ hσc, ViscAux.lapₓ_quartic, add_zero]
  have hψ'p : ψ' p = u p := by simp [ψ', ht.2.1]
  /- Step 2: a compact neighbourhood. -/
  have hle : ∀ᶠ q in 𝓝 p, q ∈ Ω ∧ u q ≤ ψ q := by
    have := ht.2.2
    rw [hΩ.nhdsWithin_eq hp] at this
    filter_upwards [this, hΩ.mem_nhds hp] with q h1 h2 using ⟨h2, h1⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hle
  set ρ := ε₀ / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  set K := closedBall p ρ with hK_def
  have hKsub : K ⊆ ball p ε₀ := closedBall_subset_ball (by linarith)
  have hpK : p ∈ K := mem_closedBall_self hρ.le
  have hKΩ : K ⊆ Ω := fun q hq ↦ (hball (hKsub hq)).1
  have hstrict : ∀ q ∈ K, u q - ψ' q ≤ -ViscAux.quartic p q := fun q hq ↦ by
    have := (hball (hKsub hq)).2
    simp only [ψ']
    linarith
  have hK : IsCompact K := isCompact_closedBall p ρ
  have hUK : TendstoUniformlyOn un u atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hu K hKΩ hK
  /- Step 3: maxima and their convergence. -/
  have hex : ∀ n, ∃ pn ∈ K, IsViscSubOn Ω (Fn n) (un n) →
      IsMaxOn (fun q ↦ un n q - ψ' q) K pn := by
    intro n
    by_cases hn : IsViscSubOn Ω (Fn n) (un n)
    · have husc' : UpperSemicontinuousOn (fun q ↦ un n q + -ψ' q) K :=
        UpperSemicontinuousOn.add (hn.1.mono hKΩ)
          hψ'c.continuous.neg.continuousOn.upperSemicontinuousOn
      simp only [← sub_eq_add_neg] at husc'
      obtain ⟨a, ha, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨p, hpK⟩ hK husc'
      exact ⟨a, ha, fun _ ↦ hmax⟩
    · exact ⟨p, hpK, fun h ↦ absurd h hn⟩
  choose P hPK hPmax using hex
  have hest : ∀ ε > 0, ∀ᶠ n in atTop,
      -ε < un n (P n) - ψ' (P n) ∧ un n (P n) - ψ' (P n) < ε - ViscAux.quartic p (P n) := by
    intro ε hε
    filter_upwards [hsub, Metric.tendstoUniformlyOn_iff.1 hUK ε hε] with n hn hunif
    have hmax : un n p - ψ' p ≤ un n (P n) - ψ' (P n) := hPmax n hn hpK
    have h1 := abs_lt.1 (Real.dist_eq _ _ ▸ hunif p hpK)
    have h2 := abs_lt.1 (Real.dist_eq _ _ ▸ hunif (P n) (hPK n))
    have h3 := hstrict (P n) (hPK n)
    constructor <;> linarith
  have hPlim : Tendsto P atTop (𝓝 p) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hest (ε ^ 4 / 2) (by positivity)] with n hn
    have h4 : dist (P n) p ^ 4 < ε ^ 4 := by
      have := ViscAux.dist_pow_four_le_quartic p (P n)
      have := hn.1
      have := hn.2
      nlinarith [pow_pos hε 4]
    exact lt_of_pow_lt_pow_left₀ 4 hε.le h4
  have ha : Tendsto (fun n ↦ un n (P n) - ψ' (P n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hest ε hε] with n hn
    have := ViscAux.quartic_nonneg p (P n)
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hn.1, hn.2]
  have hun : Tendsto (fun n ↦ un n (P n)) atTop (𝓝 (u p)) := by
    have := ha.add ((hψ'c.continuous.tendsto p).comp hPlim)
    rw [zero_add, hψ'p] at this
    refine this.congr fun n ↦ ?_
    simp
  /- Step 4: the test inequalities at `P n`. -/
  have hineq : ∀ᶠ n in atTop,
      dₜ ψ' (P n) - lapₓ ψ' (P n) + Fn n (P n) (un n (P n)) ≤ 0 := by
    filter_upwards [hsub, hPlim.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))]
      with n hn hPn
    have htouch : TouchesAbove (fun q ↦ ψ' q + (un n (P n) - ψ' (P n))) (un n) Ω (P n) := by
      refine ⟨hKΩ (hPK n), by ring, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hPn)] with q hq
      have := hPmax n hn (ball_subset_closedBall hq)
      simp only [mem_setOf_eq] at this
      linarith
    have := hn.2 _ (hψ'c.add contDiff_const) (P n) (hKΩ (hPK n)) htouch
    rwa [dₜ_add_const, lapₓ_add_const] at this
  /- Step 5: the limit. -/
  have hpΩ : (p, u p) ∈ Ω ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  have h3 : Tendsto (fun n ↦ Fn n (P n) (un n (P n))) atTop (𝓝 (F p (u p))) := by
    refine hF.tendsto_comp (hFc _ hpΩ) hpΩ (g := fun n ↦ (P n, un n (P n))) ?_
    refine tendsto_nhdsWithin_iff.2 ⟨hPlim.prodMk_nhds hun, ?_⟩
    filter_upwards [hPlim.eventually (hΩ.mem_nhds hp)] with n hn using ⟨hn, mem_univ _⟩
  have hlim : Tendsto (fun n ↦ dₜ ψ' (P n) - lapₓ ψ' (P n) + Fn n (P n) (un n (P n))) atTop
      (𝓝 (dₜ ψ' p - lapₓ ψ' p + F p (u p))) := by
    have h1 := ((continuous_dₜ (hψ'c.of_le (by norm_num))).tendsto p).comp hPlim
    have h2 := ((continuous_lapₓ hψ'c).tendsto p).comp hPlim
    exact (h1.sub h2).add h3
  have := le_of_tendsto hlim hineq
  rwa [hdt, hlap] at this

/-- Stability of supersolutions (through `isViscSuperOn_neg_iff`). -/
theorem IsViscSuperOn.of_tendstoLocallyUniformlyOn {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {F : E d × ℝ → ℝ → ℝ} {Fn : ℕ → E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    {un : ℕ → E d × ℝ → ℝ}
    (hsuper : ∀ᶠ n in atTop, IsViscSuperOn Ω (Fn n) (un n))
    (hu : TendstoLocallyUniformlyOn un u atTop Ω) (hlsc : LowerSemicontinuousOn u Ω)
    (hF : TendstoLocallyUniformlyOn (fun n (q : (E d × ℝ) × ℝ) ↦ Fn n q.1 q.2)
      (fun q ↦ F q.1 q.2) atTop (Ω ×ˢ univ))
    (hFc : ContinuousOn (fun q : (E d × ℝ) × ℝ ↦ F q.1 q.2) (Ω ×ˢ univ)) :
    IsViscSuperOn Ω F u := by
  rw [isViscSuperOn_neg_iff]
  have hg : MapsTo (fun q : (E d × ℝ) × ℝ ↦ (q.1, -q.2)) (Ω ×ˢ univ) (Ω ×ˢ univ) :=
    fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have hgc : ContinuousOn (fun q : (E d × ℝ) × ℝ ↦ (q.1, -q.2)) (Ω ×ˢ univ) :=
    (continuous_fst.prodMk continuous_snd.neg).continuousOn
  refine IsViscSubOn.of_tendstoLocallyUniformlyOn (Fn := fun n p z ↦ -Fn n p (-z))
    (un := fun n ↦ -un n) hΩ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hsuper] with n hn using isViscSuperOn_neg_iff.1 hn
  · exact TendstoLocallyUniformlyOn.neg_real hu
  · rw [upperSemicontinuousOn_iff_lowerSemicontinuousOn_neg, neg_neg]
    exact hlsc
  · exact TendstoLocallyUniformlyOn.neg_real (hF.comp _ hg hgc)
  · exact (hFc.comp hgc hg).neg

end ParabolicBasic
