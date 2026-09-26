/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Caloric.Bernstein
public import ParabolicBasic.Analysis.UniformLimitDerivs

/-!
# Locally uniform limits of smooth caloric functions

* `IsSmoothCaloricOn.of_tendstoLocallyUniformlyOn`: if `vₙ` are smooth caloric on an open `O` and
  `vₙ → u` locally uniformly on `O`, then `u` is smooth caloric on `O`;
* `IsSmoothCaloricOn.tendstoLocallyUniformlyOn_iterPartial`: moreover `∂^w vₙ → ∂^w u` locally
  uniformly on `O`, for every word `w`.

Proof: around `p ∈ O` take a sup-ball `N = B(p, r)` with `K' = B̄(p, 2r) ⊆ O` containing
`closedParCyl q r` for all `q ∈ N`. `vₙ - vₘ` is smooth caloric, so Bernstein's bounds of all
orders (`IsSmoothCaloricOn.abs_iterPartial_le`) give
`sup_N |∂^w vₙ - ∂^w vₘ| ≤ C r^{-|w|ₚ} sup_{K'} |vₙ - vₘ| → 0`; the Cauchy variant
(`contDiffOn_infty_of_uniformCauchySeqOn_partials`) gives smoothness and the convergence of the
partials, and the equation `∂_last = ∑ᵢ ∂ᵢ∂ᵢ` passes to the limit pointwise.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Uniformity

namespace ParabolicBasic

variable {d : ℕ}

/-- Around each point `p` of an open set there is `r > 0` with `B̄(p, 2r) ⊆ O` (sup metric) and
`closedParCyl q r ⊆ B̄(p, 2r)` for every `q ∈ B(p, r)`. -/
theorem exists_closedParCyl_subset_closedBall {O : Set (E d × ℝ)} (hO : IsOpen O)
    {p : E d × ℝ} (hp : p ∈ O) :
    ∃ r > 0, closedBall p (2 * r) ⊆ O ∧
      ∀ q ∈ ball p r, closedParCyl q.1 q.2 r ⊆ closedBall p (2 * r) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO p hp
  have hr : 0 < min (ε / 3) 1 := lt_min (by positivity) one_pos
  set r := min (ε / 3) 1 with hrdef
  have hr1 : r ≤ ε / 3 := min_le_left _ _
  have hr2 : r ≤ 1 := min_le_right _ _
  refine ⟨r, hr, (closedBall_subset_ball (by linarith)).trans hball, ?_⟩
  intro q hq y hy
  rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq
  obtain ⟨hy1, hy2, hy3⟩ := hy
  rw [mem_closedBall, Prod.dist_eq, max_le_iff]
  constructor
  · have := dist_triangle y.1 q.1 p.1
    rw [mem_closedBall] at hy1
    linarith [hq.1]
  · rw [Real.dist_eq] at hq ⊢
    have hr' : r ^ 2 ≤ r := by nlinarith
    rw [abs_le]
    obtain ⟨hq2l, hq2r⟩ := abs_lt.1 hq.2
    constructor <;> linarith

/-- A locally uniform limit of smooth caloric functions on an open set is `C^∞`, and all partials
converge locally uniformly. -/
theorem IsSmoothCaloricOn.contDiffOn_and_tendstoLocallyUniformlyOn_iterPartial {ι : Type*}
    {l : Filter ι} [l.NeBot] {O : Set (E d × ℝ)} (hO : IsOpen O) {v : ι → E d × ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hv : ∀ n, IsSmoothCaloricOn O (v n))
    (hlim : TendstoLocallyUniformlyOn v u l O) :
    ContDiffOn ℝ ∞ u O ∧ ∀ w : List (Fin (d + 1)),
      TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (v n)) (iterPartial w u) l O := by
  refine contDiffOn_infty_of_uniformCauchySeqOn_partials hO (fun n ↦ (hv n).1)
    (fun x hx ↦ hlim.tendsto_at hx) ?_
  intro w p hp
  obtain ⟨r, hr, hK, hN⟩ := exists_closedParCyl_subset_closedBall hO hp
  obtain ⟨C, hC0, hC⟩ := IsSmoothCaloricOn.abs_iterPartial_le (d := d) w
  refine ⟨ball p r, ball_mem_nhds p hr, ?_⟩
  have hunif : TendstoUniformlyOn v u l (closedBall p (2 * r)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1 hlim _ hK (isCompact_closedBall p _)
  have hcauchy := hunif.uniformCauchySeqOn
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  have hrk : 0 < r ^ parOrder w := pow_pos hr _
  set δ := ε * r ^ parOrder w / (C + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hev := hcauchy {x | dist x.1 x.2 < δ} (Metric.dist_mem_uniformity hδ)
  filter_upwards [hev] with m hm q hq
  apply hεU
  have hqO : q ∈ O := hK (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith)) hq)
  have hsubK := hN q hq
  have hdiff := (hv m.1).sub hO (hv m.2)
  have hb := hC (x₀ := q.1) (t₀ := q.2) (M := δ) hO hr (hsubK.trans hK) hdiff
    (fun q' hq' ↦ (hm q' (hsubK hq')).le)
  simp only [Prod.mk.eta] at hb
  rw [iterPartial_sub hO (hv m.1).1 (hv m.2).1 w q hqO] at hb
  rw [Real.dist_eq]
  refine hb.trans_lt ?_
  have hC1 : 0 < C + 1 := by linarith
  have heq : C * δ / r ^ parOrder w = ε * (C / (C + 1)) := by
    rw [hδdef]; field_simp
  rw [heq]
  calc ε * (C / (C + 1)) < ε * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hε
        rw [div_lt_one hC1]; linarith
    _ = ε := mul_one ε

/-- A locally uniform limit of smooth caloric functions on an open set is
smooth caloric. -/
theorem IsSmoothCaloricOn.of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {O : Set (E d × ℝ)} (hO : IsOpen O) {v : ι → E d × ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hv : ∀ n, IsSmoothCaloricOn O (v n)) (hlim : TendstoLocallyUniformlyOn v u l O) :
    IsSmoothCaloricOn O u := by
  obtain ⟨hu, hconv⟩ :=
    IsSmoothCaloricOn.contDiffOn_and_tendstoLocallyUniformlyOn_iterPartial hO hv hlim
  rw [isSmoothCaloricOn_iff_heatP hO]
  refine ⟨hu, fun p hp ↦ ?_⟩
  have h1 := (hconv [Fin.last d]).tendsto_at hp
  have h2 : Tendsto (fun n ↦ ∑ i : Fin d, iterPartial [i.castSucc, i.castSucc] (v n) p) l
      (𝓝 (∑ i : Fin d, iterPartial [i.castSucc, i.castSucc] u p)) :=
    tendsto_finsetSum _ fun i _ ↦ (hconv _).tendsto_at hp
  have heq : (fun n ↦ iterPartial [Fin.last d] (v n) p) =
      fun n ↦ ∑ i : Fin d, iterPartial [i.castSucc, i.castSucc] (v n) p :=
    funext fun n ↦ (hv n).partialDeriv_last_eq hO hp
  rw [heq] at h1
  have := tendsto_nhds_unique h1 h2
  simp only [iterPartial_cons, iterPartial_nil] at this
  simp only [heatP, this, sub_self]

/-- For a locally uniform limit of smooth caloric functions, `∂^w vₙ → ∂^w u` locally
uniformly. -/
theorem IsSmoothCaloricOn.tendstoLocallyUniformlyOn_iterPartial {ι : Type*} {l : Filter ι}
    [l.NeBot] {O : Set (E d × ℝ)} (hO : IsOpen O) {v : ι → E d × ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hv : ∀ n, IsSmoothCaloricOn O (v n)) (hlim : TendstoLocallyUniformlyOn v u l O)
    (w : List (Fin (d + 1))) :
    TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (v n)) (iterPartial w u) l O :=
  (IsSmoothCaloricOn.contDiffOn_and_tendstoLocallyUniformlyOn_iterPartial hO hv hlim).2 w

end ParabolicBasic
