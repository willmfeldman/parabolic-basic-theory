/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Upper and lower envelopes relative to a set

For `W : X → ℝ` and a set `S ⊆ X`, the upper envelope relative to `S` is
`W^*(z) = limsup_{q → z, q ∈ S} W q` and the lower envelope is
`W_*(z) = -(-W)^*(z) = liminf_{q → z, q ∈ S} W q`. Only the values of `W` on `S` matter.

All results assume two-sided bounds `m ≤ W ≤ M` on `S` (in Perron's method they come from the
barriers), which discharge the `IsBoundedUnder` side conditions of `limsup`.
-/

@[expose] public section

open Set Filter Topology

namespace ParabolicBasic

variable {X : Type*} [TopologicalSpace X]

/-- The upper envelope of `W` relative to `S`: `W^*(z) = limsup W (𝓝[S] z)`. -/
noncomputable def upperEnv (S : Set X) (W : X → ℝ) (z : X) : ℝ :=
  limsup W (𝓝[S] z)

/-- The lower envelope of `W` relative to `S`: `W_*(z) = -(-W)^*(z)`, i.e.
`liminf W (𝓝[S] z)`. -/
noncomputable def lowerEnv (S : Set X) (W : X → ℝ) (z : X) : ℝ :=
  -upperEnv S (fun q ↦ -W q) z

variable {S : Set X} {W : X → ℝ} {m M : ℝ} {z : X}

theorem isBoundedUnder_le_nhdsWithin (hup : ∀ q ∈ S, W q ≤ M) :
    (𝓝[S] z).IsBoundedUnder (· ≤ ·) W :=
  isBoundedUnder_of_eventually_le (a := M) (eventually_nhdsWithin_of_forall hup)

theorem isCoboundedUnder_le_nhdsWithin (hz : z ∈ closure S) (hlo : ∀ q ∈ S, m ≤ W q) :
    (𝓝[S] z).IsCoboundedUnder (· ≤ ·) W :=
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hz
  isCoboundedUnder_le_of_eventually_le _ (x := m) (eventually_nhdsWithin_of_forall hlo)

/-- `W ≤ W^*` on `S`. -/
theorem le_upperEnv (hup : ∀ q ∈ S, W q ≤ M) (hz : z ∈ S) : W z ≤ upperEnv S W z :=
  le_limsup_of_frequently_le
    ((frequently_pure.2 le_rfl : ∃ᶠ q in pure z, W z ≤ W q).filter_mono
      (pure_le_nhdsWithin hz))
    (isBoundedUnder_le_nhdsWithin hup)

/-- If `W ≤ y` near `z` in `S`, then `W^*(z) ≤ y`. -/
theorem upperEnv_le_of_eventually (hz : z ∈ closure S) (hlo : ∀ q ∈ S, m ≤ W q) {y : ℝ}
    (h : ∀ᶠ q in 𝓝[S] z, W q ≤ y) : upperEnv S W z ≤ y :=
  limsup_le_of_le (isCoboundedUnder_le_nhdsWithin hz hlo) h

/-- `W^*(z) < y` forces `W < y` near `z` in `S`. -/
theorem eventually_lt_of_upperEnv_lt (hup : ∀ q ∈ S, W q ≤ M) {y : ℝ}
    (h : upperEnv S W z < y) : ∀ᶠ q in 𝓝[S] z, W q < y :=
  eventually_lt_of_limsup_lt h (isBoundedUnder_le_nhdsWithin hup)

/-- `y < W^*(z)` gives points of `S` near `z` with `y < W`. -/
theorem frequently_lt_of_lt_upperEnv (hz : z ∈ closure S) (hlo : ∀ q ∈ S, m ≤ W q) {y : ℝ}
    (h : y < upperEnv S W z) : ∃ᶠ q in 𝓝[S] z, y < W q :=
  frequently_lt_of_lt_limsup (isCoboundedUnder_le_nhdsWithin hz hlo) h

/-- A continuous majorant of `W` on `S` majorizes `W^*` at points of `closure S`. -/
theorem upperEnv_le_of_continuousWithinAt (hz : z ∈ closure S) (hlo : ∀ q ∈ S, m ≤ W q)
    {φ : X → ℝ} (hφ : ContinuousWithinAt φ S z) (h : ∀ q ∈ S, W q ≤ φ q) :
    upperEnv S W z ≤ φ z := by
  refine le_of_forall_pos_le_add fun ε hε ↦ upperEnv_le_of_eventually hz hlo ?_
  filter_upwards [hφ.eventually (Iio_mem_nhds (lt_add_of_pos_right (φ z) hε)),
    self_mem_nhdsWithin] with q hq hqS
  exact (h q hqS).trans hq.le

/-- `W^*` is upper semicontinuous on `closure S`. -/
theorem upperSemicontinuousOn_upperEnv (hlo : ∀ q ∈ S, m ≤ W q) (hup : ∀ q ∈ S, W q ≤ M) :
    UpperSemicontinuousOn (upperEnv S W) (closure S) := by
  intro z hz y hy
  obtain ⟨y', hy1, hy2⟩ := exists_between hy
  obtain ⟨N, hNo, hzN, hNS⟩ := mem_nhdsWithin.1 (eventually_lt_of_upperEnv_lt hup hy1)
  filter_upwards [nhdsWithin_le_nhds (hNo.mem_nhds hzN), self_mem_nhdsWithin] with z' hz'N hz'
  refine lt_of_le_of_lt (upperEnv_le_of_eventually hz' hlo ?_) hy2
  exact mem_nhdsWithin.2 ⟨N, hNo, hz'N, fun q hq ↦ show W q ≤ y' from (hNS hq).le⟩

/-! ### Lower envelopes -/

theorem lowerEnv_le (hlo : ∀ q ∈ S, m ≤ W q) (hz : z ∈ S) : lowerEnv S W z ≤ W z := by
  have := le_upperEnv (W := fun q ↦ -W q) (M := -m) (fun q hq ↦ neg_le_neg (hlo q hq)) hz
  unfold lowerEnv
  linarith

theorem le_lowerEnv_of_eventually (hz : z ∈ closure S) (hup : ∀ q ∈ S, W q ≤ M) {y : ℝ}
    (h : ∀ᶠ q in 𝓝[S] z, y ≤ W q) : y ≤ lowerEnv S W z := by
  have := upperEnv_le_of_eventually (W := fun q ↦ -W q) (m := -M) (y := -y) hz
    (fun q hq ↦ neg_le_neg (hup q hq)) (h.mono fun q hq ↦ neg_le_neg hq)
  unfold lowerEnv
  linarith

theorem frequently_lt_of_lowerEnv_lt (hz : z ∈ closure S) (hup : ∀ q ∈ S, W q ≤ M) {y : ℝ}
    (h : lowerEnv S W z < y) : ∃ᶠ q in 𝓝[S] z, W q < y := by
  have := frequently_lt_of_lt_upperEnv (W := fun q ↦ -W q) (m := -M) (y := -y) hz
    (fun q hq ↦ neg_le_neg (hup q hq)) (by unfold lowerEnv at h; linarith)
  exact this.mono fun q hq ↦ by linarith

theorem le_lowerEnv_of_continuousWithinAt (hz : z ∈ closure S) (hup : ∀ q ∈ S, W q ≤ M)
    {φ : X → ℝ} (hφ : ContinuousWithinAt φ S z) (h : ∀ q ∈ S, φ q ≤ W q) :
    φ z ≤ lowerEnv S W z := by
  have := upperEnv_le_of_continuousWithinAt (W := fun q ↦ -W q) (m := -M) hz
    (fun q hq ↦ neg_le_neg (hup q hq)) hφ.neg (fun q hq ↦ neg_le_neg (h q hq))
  unfold lowerEnv
  linarith

theorem lowerSemicontinuousOn_lowerEnv (hlo : ∀ q ∈ S, m ≤ W q) (hup : ∀ q ∈ S, W q ≤ M) :
    LowerSemicontinuousOn (lowerEnv S W) (closure S) := by
  have := upperSemicontinuousOn_upperEnv (W := fun q ↦ -W q) (m := -M) (M := -m)
    (fun q hq ↦ neg_le_neg (hup q hq)) (fun q hq ↦ neg_le_neg (hlo q hq))
  intro z hz y hy
  filter_upwards [this z hz (-y) (by unfold lowerEnv at hy; linarith)] with q hq
  unfold lowerEnv
  linarith

end ParabolicBasic
