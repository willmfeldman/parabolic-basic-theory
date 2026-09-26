/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Semilinear
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# API of `SemilinearHyp` and the Hölder–McShane extension

* `SemilinearHyp.zero`, `SemilinearHyp.mono`, `SemilinearHyp.continuousOn`;
* `exists_holderLip_extension`: a nonlinearity `f` that is `α`-Hölder in `x ∈ S` uniformly in `z`
  and Lipschitz in `z` uniformly in `x ∈ S` extends to a function on all of `E d × ℝ` with the
  same bounds, jointly continuous. The extension is
  `f̃ x z := ⨅ y : S, (f y z + K * dist x y ^ α)` (McShane in `x`, uniformly in `z`);
* `SemilinearHyp.exists_extension`: the same, followed by a truncation, for the full bundle.

The extension is needed because the `Proper` and `OperatorContinuous` conditions of
`ViscositySolns` are global in the space variable, while `f` is controlled only on `closure V`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- The zero nonlinearity satisfies the standing hypotheses on every set. -/
theorem SemilinearHyp.zero (S : Set (E d)) : SemilinearHyp (fun _ _ ↦ (0 : ℝ)) S :=
  ⟨⟨0, 1, one_pos, le_rfl, fun _ _ _ _ _ ↦ by simp⟩, ⟨0, fun _ _ _ _ ↦ by simp⟩,
    ⟨0, fun _ _ _ ↦ by simp⟩⟩

/-- The standing hypotheses restrict to subsets. -/
theorem SemilinearHyp.mono {f : E d → ℝ → ℝ} {S T : Set (E d)} (hf : SemilinearHyp f T)
    (hST : S ⊆ T) : SemilinearHyp f S := by
  obtain ⟨⟨K, α, hα, hα1, hK⟩, ⟨L, hL⟩, ⟨M, hM⟩⟩ := hf
  exact ⟨⟨K, α, hα, hα1, fun x hx y hy z ↦ hK x (hST hx) y (hST hy) z⟩,
    ⟨L, fun x hx ↦ hL x (hST hx)⟩, ⟨M, fun x hx ↦ hM x (hST hx)⟩⟩

/-- `dist x y ^ α ≤ dist x x' ^ α + dist x' y ^ α` for `0 ≤ α ≤ 1`. -/
theorem dist_rpow_le_add {X : Type*} [PseudoMetricSpace X] {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (x x' y : X) : dist x y ^ α ≤ dist x x' ^ α + dist x' y ^ α :=
  (Real.rpow_le_rpow dist_nonneg (dist_triangle x x' y) hα).trans
    (Real.rpow_add_le_add_rpow dist_nonneg dist_nonneg hα hα1)

/-- **Hölder–McShane extension, uniform in `z`.** -/
theorem exists_holderLip_extension {S : Set (E d)} {f : E d → ℝ → ℝ}
    (hfx : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ z, |f x z - f y z| ≤ K * dist x y ^ α)
    (hfz : ∃ L : ℝ, ∀ x ∈ S, ∀ z w, |f x z - f x w| ≤ L * |z - w|) :
    ∃ g : E d → ℝ → ℝ, (∀ x ∈ S, ∀ z, g x z = f x z) ∧
      (∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x y z, |g x z - g y z| ≤ K * dist x y ^ α) ∧
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x z w, |g x z - g x w| ≤ L * |z - w|) ∧
      Continuous (fun q : E d × ℝ ↦ g q.1 q.2) := by
  obtain ⟨K₀, α, hα, hα1, hK₀⟩ := hfx
  obtain ⟨L₀, hL₀⟩ := hfz
  rcases S.eq_empty_or_nonempty with hS | ⟨y₀, hy₀⟩
  · subst hS
    exact ⟨fun _ _ ↦ 0, fun _ h ↦ absurd h (notMem_empty _),
      ⟨0, 1, one_pos, le_rfl, fun _ _ _ ↦ by simp⟩, ⟨0, le_rfl, fun _ _ _ ↦ by simp⟩,
      continuous_const⟩
  set K := max K₀ 0 with hKdef
  set L := max L₀ 0 with hLdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hL0 : 0 ≤ L := le_max_right _ _
  have hK : ∀ x ∈ S, ∀ y ∈ S, ∀ z, |f x z - f y z| ≤ K * dist x y ^ α := fun x hx y hy z ↦
    (hK₀ x hx y hy z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg dist_nonneg _))
  have hL : ∀ x ∈ S, ∀ z w, |f x z - f x w| ≤ L * |z - w| := fun x hx z w ↦
    (hL₀ x hx z w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  haveI : Nonempty S := ⟨⟨y₀, hy₀⟩⟩
  set g : E d → ℝ → ℝ := fun x z ↦ ⨅ y : S, (f y z + K * dist x y ^ α) with hgdef
  have hsub : ∀ x x' y : E d, dist x y ^ α ≤ dist x x' ^ α + dist x' y ^ α :=
    dist_rpow_le_add hα.le hα1
  have hbdd : ∀ (x : E d) z, BddBelow (range fun y : S ↦ f y z + K * dist x (y : E d) ^ α) := by
    intro x z
    refine ⟨f y₀ z - K * dist x y₀ ^ α, ?_⟩
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have h1 := (abs_le.1 (hK y hy y₀ hy₀ z)).1
    have h2 := hsub y x y₀
    rw [dist_comm y x] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hK0
    simp only
    nlinarith
  have hle : ∀ x z (y : E d) (hy : y ∈ S), g x z ≤ f y z + K * dist x y ^ α :=
    fun x z y hy ↦ ciInf_le (hbdd x z) ⟨y, hy⟩
  have hge : ∀ x z c, (∀ y ∈ S, c ≤ f y z + K * dist x y ^ α) → c ≤ g x z :=
    fun x z c h ↦ le_ciInf fun y ↦ h y y.2
  -- (i) agreement on `S`
  have hagree : ∀ x ∈ S, ∀ z, g x z = f x z := by
    intro x hx z
    refine le_antisymm ?_ (hge x z _ fun y hy ↦ ?_)
    · have := hle x z x hx
      rwa [dist_self, Real.zero_rpow hα.ne', mul_zero, add_zero] at this
    · have := (abs_le.1 (hK x hx y hy z)).2
      linarith
  -- (ii) Hölder in `x`
  have hhol1 : ∀ x x' z, g x z - K * dist x x' ^ α ≤ g x' z := by
    intro x x' z
    refine hge x' z _ fun y hy ↦ ?_
    have h1 := hle x z y hy
    have h2 := mul_le_mul_of_nonneg_left (hsub x x' y) hK0
    linarith
  have hhol : ∀ x y z, |g x z - g y z| ≤ K * dist x y ^ α := by
    intro x y z
    rw [abs_le]
    have h1 := hhol1 x y z
    have h2 := hhol1 y x z
    rw [dist_comm y x] at h2
    constructor <;> linarith
  -- (iii) Lipschitz in `z`
  have hlip1 : ∀ x z w, g x z - L * |z - w| ≤ g x w := by
    intro x z w
    refine hge x w _ fun y hy ↦ ?_
    have h1 := hle x z y hy
    have h2 := (abs_le.1 (hL y hy z w)).2
    linarith
  have hlip : ∀ x z w, |g x z - g x w| ≤ L * |z - w| := by
    intro x z w
    rw [abs_le]
    have h1 := hlip1 x z w
    have h2 := hlip1 x w z
    rw [abs_sub_comm w z] at h2
    constructor <;> linarith
  -- (iv) joint continuity
  have hcont : Continuous fun q : E d × ℝ ↦ g q.1 q.2 := by
    refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have hb : Continuous fun q : E d × ℝ ↦ K * dist q.1 q₀.1 ^ α + L * dist q.2 q₀.2 :=
      (continuous_const.mul ((continuous_fst.dist continuous_const).rpow_const
        fun _ ↦ Or.inr hα.le)).add (continuous_const.mul (continuous_snd.dist continuous_const))
    refine squeeze_zero (g := fun q : E d × ℝ ↦ K * dist q.1 q₀.1 ^ α + L * dist q.2 q₀.2)
      (fun q ↦ dist_nonneg) (fun q ↦ ?_) ?_
    · change dist (g q.1 q.2) (g q₀.1 q₀.2) ≤ K * dist q.1 q₀.1 ^ α + L * dist q.2 q₀.2
      rw [Real.dist_eq, Real.dist_eq q.2]
      calc |g q.1 q.2 - g q₀.1 q₀.2|
          ≤ |g q.1 q.2 - g q₀.1 q.2| + |g q₀.1 q.2 - g q₀.1 q₀.2| := abs_sub_le _ _ _
        _ ≤ K * dist q.1 q₀.1 ^ α + L * |q.2 - q₀.2| := add_le_add (hhol _ _ _) (hlip _ _ _)
    · have := hb.tendsto q₀
      simpa [Real.zero_rpow hα.ne'] using this
  exact ⟨g, hagree, ⟨K, α, hα, hα1, hhol⟩, ⟨L, hL0, hlip⟩, hcont⟩

/-- Under the standing hypotheses, `(x, z) ↦ f x z` is continuous on `S × ℝ`. -/
theorem SemilinearHyp.continuousOn {f : E d → ℝ → ℝ} {S : Set (E d)} (hf : SemilinearHyp f S) :
    ContinuousOn (fun q : E d × ℝ ↦ f q.1 q.2) (S ×ˢ univ) := by
  obtain ⟨g, hgf, -, -, hgc⟩ := exists_holderLip_extension hf.holder_x hf.lip_z
  exact hgc.continuousOn.congr fun q hq ↦ (hgf q.1 hq.1 q.2).symm

/-- Global extension (Hölder–McShane in `x`, then truncation). -/
theorem SemilinearHyp.exists_extension {f : E d → ℝ → ℝ} {S : Set (E d)}
    (hf : SemilinearHyp f S) :
    ∃ g : E d → ℝ → ℝ, (∀ x ∈ S, ∀ z, g x z = f x z) ∧ SemilinearHyp g univ ∧
      Continuous (fun q : E d × ℝ ↦ g q.1 q.2) := by
  obtain ⟨g, hgf, ⟨K, α, hα, hα1, hK⟩, ⟨L, -, hL⟩, hgc⟩ :=
    exists_holderLip_extension hf.holder_x hf.lip_z
  obtain ⟨M₀, hM₀⟩ := hf.bounded
  set M := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  set c : ℝ → ℝ := fun s ↦ max (min s M) (-M) with hcdef
  have hc : ∀ s t, |c s - c t| ≤ |s - t| := fun s t ↦
    (abs_max_sub_max_le_abs _ _ _).trans
      ((abs_min_sub_min_le_max _ _ _ _).trans (by simp))
  refine ⟨fun x z ↦ c (g x z), fun x hx z ↦ ?_,
    ⟨⟨K, α, hα, hα1, fun x _ y _ z ↦ (hc _ _).trans (hK x y z)⟩,
      ⟨L, fun x _ z w ↦ (hc _ _).trans (hL x z w)⟩,
      ⟨M, fun x _ z ↦ abs_le.2 ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩⟩⟩,
    (hgc.min continuous_const).max continuous_const⟩
  have h := abs_le.1 ((hM₀ x hx z).trans (le_max_left M₀ 0))
  simp only [hcdef, hgf x hx z]
  rw [min_eq_left h.2, max_eq_left h.1]

end ParabolicBasic
