/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Viscosity
public import ParabolicBasic.Defs.Classical
public import ParabolicBasic.Calculus.Extremum

/-!
# Classical solutions are viscosity solutions

* `heat_le_of_le_past`: the core comparison of the heat operators of two functions touching at
  `p`, one of them from above on the spatial slice and on the *past* half of the time slice;
  `heat_le_of_eventually_le` is the two-sided form;
* standard notion: `isViscSubOn_of_contDiffOn` (joint `C²`), `IsC21On.isViscSubOn`
  (`C^{2,1}` on an open box), and the supersolution mirrors;
* past-touching notion: `IsSemilinearSolOn.isSemilinearViscSubOn`,
  `IsSemilinearSolOn.isSemilinearViscSuperOn`; only the past half of the time slice is available,
  so the one-sided time test is used;
* `IsSemilinearViscSubOn.isViscSubOn` (+ super): the past-touching notion implies the standard one
  on the open cylinder.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### The core pointwise comparison -/

/-- Let the spatial slices of `φ`, `ψ` be `C²` at `p.1` and their time slices differentiable at
`p.2`. If `φ p = ψ p`, `φ ≤ ψ` on the spatial slice near `p.1`, and `φ ≤ ψ` on the time slice for
earlier times near `p.2`, then
`dₜψ(p) - Δₓψ(p) ≤ dₜφ(p) - Δₓφ(p)`. -/
theorem heat_le_of_le_past {φ ψ : E d × ℝ → ℝ} {p : E d × ℝ}
    (hφx : ContDiffAt ℝ 2 (fun y ↦ φ (y, p.2)) p.1)
    (hψx : ContDiffAt ℝ 2 (fun y ↦ ψ (y, p.2)) p.1)
    (hφt : DifferentiableAt ℝ (fun s ↦ φ (p.1, s)) p.2)
    (hψt : DifferentiableAt ℝ (fun s ↦ ψ (p.1, s)) p.2) (heq : φ p = ψ p)
    (hleX : ∀ᶠ y in 𝓝 p.1, φ (y, p.2) ≤ ψ (y, p.2))
    (hleT : ∀ᶠ s in 𝓝[≤] p.2, φ (p.1, s) ≤ ψ (p.1, s)) :
    dₜ ψ p - lapₓ ψ p ≤ dₜ φ p - lapₓ φ p := by
  have hlap := lapₓ_le_of_touchesAbove hψx hφx heq hleX
  have hmin : IsLocalMinOn (fun s ↦ ψ (p.1, s) - φ (p.1, s)) (Iic p.2) p.2 := by
    change ∀ᶠ s in 𝓝[≤] p.2, _
    filter_upwards [hleT] with s hs
    simp only [Prod.mk.eta, heq, sub_self]
    linarith
  have hdt := dₜ_le_of_isLocalMinOn_Iic hψt hφt hmin
  linarith

/-- Two-sided form of `heat_le_of_le_past`: `φ ≤ ψ` near `p` with equality at `p`. -/
theorem heat_le_of_eventually_le {φ ψ : E d × ℝ → ℝ} {p : E d × ℝ}
    (hφx : ContDiffAt ℝ 2 (fun y ↦ φ (y, p.2)) p.1)
    (hψx : ContDiffAt ℝ 2 (fun y ↦ ψ (y, p.2)) p.1)
    (hφt : DifferentiableAt ℝ (fun s ↦ φ (p.1, s)) p.2)
    (hψt : DifferentiableAt ℝ (fun s ↦ ψ (p.1, s)) p.2) (heq : φ p = ψ p)
    (hle : ∀ᶠ q in 𝓝 p, φ q ≤ ψ q) :
    dₜ ψ p - lapₓ ψ p ≤ dₜ φ p - lapₓ φ p :=
  heat_le_of_le_past hφx hψx hφt hψt heq ((tendsto_sliceX p).eventually hle)
    (((tendsto_sliceT p).mono_left nhdsWithin_le_nhds).eventually hle)

/-! ### The standard notion -/

/-- Classical ⇒ viscosity (standard notion), sub form, from slice regularity at each point. -/
theorem isViscSubOn_of_slices {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hΩ : IsOpen Ω) (hc : ContinuousOn u Ω)
    (hx : ∀ p ∈ Ω, ContDiffAt ℝ 2 (fun y ↦ u (y, p.2)) p.1)
    (ht : ∀ p ∈ Ω, DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2)
    (heq : ∀ p ∈ Ω, dₜ u p - lapₓ u p + F p (u p) ≤ 0) : IsViscSubOn Ω F u := by
  refine ⟨hc.upperSemicontinuousOn, fun ψ hψ p hp hto ↦ ?_⟩
  have hle : ∀ᶠ q in 𝓝 p, u q ≤ ψ q := by
    rw [← hΩ.nhdsWithin_eq hp]; exact hto.2.2
  have := heat_le_of_eventually_le (hx p hp) (contDiff_sliceX hψ p.2).contDiffAt (ht p hp)
    ((contDiff_sliceT hψ p.1).differentiable two_ne_zero p.2) hto.2.1.symm hle
  linarith [heq p hp]

/-- Classical ⇒ viscosity (standard notion), super form, from slice regularity at each point. -/
theorem isViscSuperOn_of_slices {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hΩ : IsOpen Ω) (hc : ContinuousOn u Ω)
    (hx : ∀ p ∈ Ω, ContDiffAt ℝ 2 (fun y ↦ u (y, p.2)) p.1)
    (ht : ∀ p ∈ Ω, DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2)
    (heq : ∀ p ∈ Ω, 0 ≤ dₜ u p - lapₓ u p + F p (u p)) : IsViscSuperOn Ω F u := by
  refine ⟨hc.lowerSemicontinuousOn, fun ψ hψ p hp hto ↦ ?_⟩
  have hle : ∀ᶠ q in 𝓝 p, ψ q ≤ u q := by
    rw [← hΩ.nhdsWithin_eq hp]; exact hto.2.2
  have := heat_le_of_eventually_le (contDiff_sliceX hψ p.2).contDiffAt (hx p hp)
    ((contDiff_sliceT hψ p.1).differentiable two_ne_zero p.2) (ht p hp) hto.2.1 hle
  linarith [heq p hp]

/-- A `C²` classical subsolution on an open set is a viscosity subsolution. -/
theorem isViscSubOn_of_contDiffOn {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (heq : ∀ p ∈ Ω, dₜ u p - lapₓ u p + F p (u p) ≤ 0) : IsViscSubOn Ω F u :=
  isViscSubOn_of_slices hΩ hu.continuousOn
    (fun _ hp ↦ contDiffAt_sliceX (hu.contDiffAt (hΩ.mem_nhds hp)))
    (fun _ hp ↦ differentiableAt_sliceT
      ((hu.contDiffAt (hΩ.mem_nhds hp)).differentiableAt two_ne_zero)) heq

/-- A `C²` classical supersolution on an open set is a viscosity supersolution. -/
theorem isViscSuperOn_of_contDiffOn {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (heq : ∀ p ∈ Ω, 0 ≤ dₜ u p - lapₓ u p + F p (u p)) : IsViscSuperOn Ω F u :=
  isViscSuperOn_of_slices hΩ hu.continuousOn
    (fun _ hp ↦ contDiffAt_sliceX (hu.contDiffAt (hΩ.mem_nhds hp)))
    (fun _ hp ↦ differentiableAt_sliceT
      ((hu.contDiffAt (hΩ.mem_nhds hp)).differentiableAt two_ne_zero)) heq

/-- A `C^{2,1}` classical subsolution on an open box `U × I` is a viscosity subsolution. -/
theorem IsC21On.isViscSubOn {U : Set (E d)} {I : Set ℝ} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : IsOpen I) (hu : IsC21On U I u)
    (heq : ∀ p ∈ U ×ˢ I, dₜ u p - lapₓ u p + F p (u p) ≤ 0) : IsViscSubOn (U ×ˢ I) F u :=
  isViscSubOn_of_slices (hU.prod hI) hu.1
    (fun _ hp ↦ (hu.2.1 _ hp.2).contDiffAt (hU.mem_nhds hp.1)) hu.2.2.2.2.1 heq

/-- A `C^{2,1}` classical supersolution on an open box `U × I` is a viscosity supersolution. -/
theorem IsC21On.isViscSuperOn {U : Set (E d)} {I : Set ℝ} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : IsOpen I) (hu : IsC21On U I u)
    (heq : ∀ p ∈ U ×ˢ I, 0 ≤ dₜ u p - lapₓ u p + F p (u p)) :
    IsViscSuperOn (U ×ˢ I) F u :=
  isViscSuperOn_of_slices (hU.prod hI) hu.1
    (fun _ hp ↦ (hu.2.1 _ hp.2).contDiffAt (hU.mem_nhds hp.1)) hu.2.2.2.2.1 heq

/-! ### The past-touching notion -/

section Past

variable {U : Set (E d)} {I : Set ℝ} {p : E d × ℝ}

/-- The spatial slice through `p ∈ U × I` tends to `p` within the parabolic past. -/
theorem tendsto_sliceX_past (hU : IsOpen U) (hp : p ∈ U ×ˢ I) :
    Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ p.2}] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_sliceX p, ?_⟩
  filter_upwards [hU.mem_nhds hp.1] with y hy
  exact ⟨⟨hy, hp.2⟩, le_refl p.2⟩

/-- The past half of the time slice through `p ∈ U × I` tends to `p` within the parabolic past,
if `I` contains a left neighbourhood of `p.2`. -/
theorem tendsto_sliceT_past (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I) (hp : p ∈ U ×ˢ I) :
    Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝[≤] p.2) (𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ p.2}] p) := by
  obtain ⟨δ, hδ, hδI⟩ := hI p.2 hp.2
  refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_sliceT p).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [Ioc_mem_nhdsLE (show p.2 - δ < p.2 by linarith)] with s hs
  exact ⟨⟨hp.1, hδI hs⟩, hs.2⟩

/-- A classical solution of `∂ₜu = Δₓu - f(x, u)` on `U × I` (`U` open, `I` with left
neighbourhoods) is a viscosity subsolution in the past-touching sense. -/
theorem IsSemilinearSolOn.isSemilinearViscSubOn {f : E d → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSubOn U f I u := by
  refine ⟨hu.1, fun ψ hψ p hp hto ↦ ?_⟩
  have := heat_le_of_le_past ((hu.2.1 _ hp.2).contDiffAt (hU.mem_nhds hp.1))
    (contDiff_sliceX hψ p.2).contDiffAt (hu.2.2.2.2.1 p hp)
    ((contDiff_sliceT hψ p.1).differentiable two_ne_zero p.2) hto.2.1.symm
    ((tendsto_sliceX_past hU hp).eventually hto.2.2)
    ((tendsto_sliceT_past hI hp).eventually hto.2.2)
  linarith [hu.2.2.2.2.2.2 p hp]

/-- A classical solution of `∂ₜu = Δₓu - f(x, u)` on `U × I` (`U` open, `I` with left
neighbourhoods) is a viscosity supersolution in the past-touching sense. -/
theorem IsSemilinearSolOn.isSemilinearViscSuperOn {f : E d → ℝ → ℝ} {u : E d × ℝ → ℝ}
    (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U f I u) : IsSemilinearViscSuperOn U f I u := by
  refine ⟨hu.1, fun ψ hψ p hp hto ↦ ?_⟩
  have := heat_le_of_le_past (contDiff_sliceX hψ p.2).contDiffAt
    ((hu.2.1 _ hp.2).contDiffAt (hU.mem_nhds hp.1))
    ((contDiff_sliceT hψ p.1).differentiable two_ne_zero p.2) (hu.2.2.2.2.1 p hp) hto.2.1
    ((tendsto_sliceX_past hU hp).eventually hto.2.2)
    ((tendsto_sliceT_past hI hp).eventually hto.2.2)
  linarith [hu.2.2.2.2.2.2 p hp]

end Past

/-! ### The past-touching notion implies the standard notion -/

/-- A touching from above in the open cylinder `V × (a, b)` is a touching in the parabolic past
`(V × (a, b]) ∩ {q.2 ≤ p.2}`. -/
theorem TouchesAbove.past_of_isOpen {V : Set (E d)} {a b : ℝ} {ψ u : E d × ℝ → ℝ}
    {p : E d × ℝ} (hV : IsOpen V) (ht : TouchesAbove ψ u (V ×ˢ Ioo a b) p) :
    TouchesAbove ψ u ((V ×ˢ Ioc a b) ∩ {q | q.2 ≤ p.2}) p := by
  refine ⟨⟨⟨ht.1.1, Ioo_subset_Ioc_self ht.1.2⟩, le_refl p.2⟩, ht.2.1, ?_⟩
  have h := ht.2.2
  rw [(hV.prod isOpen_Ioo).nhdsWithin_eq ht.1] at h
  exact h.filter_mono nhdsWithin_le_nhds

/-- Mirror of `TouchesAbove.past_of_isOpen`. -/
theorem TouchesBelow.past_of_isOpen {V : Set (E d)} {a b : ℝ} {ψ u : E d × ℝ → ℝ}
    {p : E d × ℝ} (hV : IsOpen V) (ht : TouchesBelow ψ u (V ×ˢ Ioo a b) p) :
    TouchesBelow ψ u ((V ×ˢ Ioc a b) ∩ {q | q.2 ≤ p.2}) p := by
  refine ⟨⟨⟨ht.1.1, Ioo_subset_Ioc_self ht.1.2⟩, le_refl p.2⟩, ht.2.1, ?_⟩
  have h := ht.2.2
  rw [(hV.prod isOpen_Ioo).nhdsWithin_eq ht.1] at h
  exact h.filter_mono nhdsWithin_le_nhds

/-- The past-touching subsolution notion implies the standard one on the open cylinder. -/
theorem IsSemilinearViscSubOn.isViscSubOn {f : E d → ℝ → ℝ} {V : Set (E d)} {a b : ℝ}
    {u : E d × ℝ → ℝ} (hV : IsOpen V) (hu : IsSemilinearViscSubOn V f (Ioc a b) u) :
    IsViscSubOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z) u := by
  refine ⟨(hu.1.mono (prod_mono subset_rfl Ioo_subset_Ioc_self)).upperSemicontinuousOn,
    fun ψ hψ p hp ht ↦ ?_⟩
  have := hu.2 ψ hψ p ⟨hp.1, Ioo_subset_Ioc_self hp.2⟩ (ht.past_of_isOpen hV)
  simp only
  linarith

/-- The past-touching supersolution notion implies the standard one on the open cylinder. -/
theorem IsSemilinearViscSuperOn.isViscSuperOn {f : E d → ℝ → ℝ} {V : Set (E d)} {a b : ℝ}
    {u : E d × ℝ → ℝ} (hV : IsOpen V) (hu : IsSemilinearViscSuperOn V f (Ioc a b) u) :
    IsViscSuperOn (V ×ˢ Ioo a b) (fun p z ↦ f p.1 z) u := by
  refine ⟨(hu.1.mono (prod_mono subset_rfl Ioo_subset_Ioc_self)).lowerSemicontinuousOn,
    fun ψ hψ p hp ht ↦ ?_⟩
  have := hu.2 ψ hψ p ⟨hp.1, Ioo_subset_Ioc_self hp.2⟩ (ht.past_of_isOpen hV)
  simp only
  linarith

end ParabolicBasic
