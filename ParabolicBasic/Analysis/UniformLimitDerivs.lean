/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.PartialsSmooth
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Locally uniform limits of derivatives

If `fₙ` are `Cᵏ` on an open set, converge pointwise to `g`, and their derivatives of order `≤ k`
converge locally uniformly, then `g` is `Cᵏ` and its derivatives are the limits.

* `contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv`: general normed codomain, with
  `iteratedFDeriv`;
* `contDiffOn_of_tendstoLocallyUniformlyOn_partials` (and `…_infty_…`): scalar functions on
  `E d × ℝ`, with coordinate partials `iterPartial w`;
* `contDiffOn_of_uniformCauchySeqOn_partials` (and `…_infty_…`): the Cauchy variant, with no
  a-priori limits of the partials (the form produced by bounds on differences).

All statements are for an arbitrary filter `l` with `l.NeBot` (e.g. `atTop` on `ℕ`).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic


/-! ### Auxiliary facts on locally uniform convergence -/

section Aux

variable {ι α β κ : Type*} {l : Filter ι} [TopologicalSpace α] [NormedAddCommGroup β] {s : Set α}

private theorem tendstoLocallyUniformlyOn_const' (b : α → β) :
    TendstoLocallyUniformlyOn (fun (_ : ι) x ↦ b x) b l s :=
  fun _u hu _x _hx ↦ ⟨s, self_mem_nhdsWithin,
    Eventually.of_forall fun _n _y _hy ↦ refl_mem_uniformity hu⟩

private theorem tendstoLocallyUniformlyOn_finsetSum' {F : κ → ι → α → β} {G : κ → α → β}
    (S : Finset κ) (h : ∀ j ∈ S, TendstoLocallyUniformlyOn (F j) (G j) l s) :
    TendstoLocallyUniformlyOn (fun n x ↦ ∑ j ∈ S, F j n x) (fun x ↦ ∑ j ∈ S, G j x) l s := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tendstoLocallyUniformlyOn_const' (ι := ι) (s := s) (fun _ ↦ (0 : β))
  | insert a S ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

private theorem tendstoLocallyUniformlyOn_smul_const' {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ι → α → ℝ} {G : α → ℝ} (h : TendstoLocallyUniformlyOn F G l s)
    (c : StrongDual ℝ V) :
    TendstoLocallyUniformlyOn (fun n x ↦ F n x • c) (fun x ↦ G x • c) l s :=
  (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).uniformContinuous
    |>.comp_tendstoLocallyUniformlyOn h

/-- Locally uniformly Cauchy families converge locally uniformly (to the pointwise limit). -/
private theorem tendstoLocallyUniformlyOn_limUnder_of_uniformCauchySeqOn [CompleteSpace β]
    [l.NeBot] {F : ι → α → β}
    (h : ∀ x ∈ s, ∃ u ∈ 𝓝 x, UniformCauchySeqOn F l u) :
    TendstoLocallyUniformlyOn F (fun x ↦ limUnder l fun n ↦ F n x) l s := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx ↦ ?_
  obtain ⟨u, hu, hc⟩ := h x hx
  refine ⟨u, mem_nhdsWithin_of_mem_nhds hu, hc.tendstoUniformlyOn_of_tendsto fun y hy ↦ ?_⟩
  obtain ⟨a, ha⟩ := CompleteSpace.complete (hc.cauchy_map hy)
  exact tendsto_nhds_limUnder ⟨a, ha⟩

private theorem tendstoLocallyUniformlyOn_linearIsometryEquiv {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedSpace ℝ β] (e : A ≃ₗᵢ[ℝ] β) {Φ : ι → α → A} {Ψ : α → A}
    (h : TendstoLocallyUniformlyOn Φ Ψ l s) :
    TendstoLocallyUniformlyOn (fun n x ↦ e (Φ n x)) (fun x ↦ e (Ψ x)) l s :=
  e.lipschitz.uniformContinuous.comp_tendstoLocallyUniformlyOn h

end Aux

/-- If `fₙ` are `Cᵏ` on an open set, converge pointwise to `g`, and their iterated derivatives of
order `≤ k` converge locally uniformly, then `g` is `Cᵏ` and its iterated derivatives are the
limits (general normed codomain). -/
theorem contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} {l : Filter ι} [l.NeBot] {s : Set V} (hs : IsOpen s) {k : ℕ}
    {f : ι → V → F} {g : V → F} (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hfg : ∀ x ∈ s, Tendsto (fun n ↦ f n x) l (𝓝 (g x)))
    (hconv : ∀ j ≤ k, ∃ G, TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ j (f n)) G l s) :
    ContDiffOn ℝ k g s ∧
      ∀ j ≤ k, TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ j (f n))
        (iteratedFDeriv ℝ j g) l s := by
  -- `fₙ → g` locally uniformly
  have h0 : TendstoLocallyUniformlyOn f g l s := by
    obtain ⟨G, hG⟩ := hconv 0 (Nat.zero_le _)
    have := tendstoLocallyUniformlyOn_linearIsometryEquiv
      (continuousMultilinearCurryFin0 ℝ V F) hG
    simp only [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply] at this
    exact this.congr_right fun x hx ↦ tendsto_nhds_unique (this.tendsto_at hx) (hfg x hx)
  have h0' : TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ 0 (f n))
      (iteratedFDeriv ℝ 0 g) l s := by
    simp only [iteratedFDeriv_zero_eq_comp]
    exact tendstoLocallyUniformlyOn_linearIsometryEquiv
      (continuousMultilinearCurryFin0 ℝ V F).symm h0
  -- regularity of the `fₙ`
  have hcont : ∀ n, ∀ j ≤ k, ContinuousOn (iteratedFDeriv ℝ j (f n)) s := fun n j hj ↦
    ((hf n).continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hs.uniqueDiffOn).congr
      fun x hx ↦ (iteratedFDerivWithin_of_isOpen j hs hx).symm
  have hdiff : ∀ n, ∀ j < k, ∀ x ∈ s, HasFDerivAt (iteratedFDeriv ℝ j (f n))
      (fderiv ℝ (iteratedFDeriv ℝ j (f n)) x) x := fun n j hj x hx ↦
    ((((hf n).differentiableOn_iteratedFDerivWithin (by exact_mod_cast hj)
      hs.uniqueDiffOn).congr fun y hy ↦ (iteratedFDerivWithin_of_isOpen j hs hy).symm) x hx
      |>.differentiableAt (hs.mem_nhds hx)).hasFDerivAt
  -- one step: from order `j` to order `j + 1`
  have step : ∀ j < k, TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ j (f n))
      (iteratedFDeriv ℝ j g) l s →
      DifferentiableOn ℝ (iteratedFDeriv ℝ j g) s ∧
        TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ (j + 1) (f n))
          (iteratedFDeriv ℝ (j + 1) g) l s := by
    intro j hj hP
    obtain ⟨G, hG⟩ := hconv (j + 1) hj
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ V) F
    have hD : TendstoLocallyUniformlyOn (fun n x ↦ fderiv ℝ (iteratedFDeriv ℝ j (f n)) x)
        (fun x ↦ L (G x)) l s := by
      refine (L.lipschitz.uniformContinuous.comp_tendstoLocallyUniformlyOn hG).congr
        fun n x _ ↦ ?_
      simp [L, iteratedFDeriv_succ_eq_comp_left]
    have hder : ∀ x ∈ s, HasFDerivAt (iteratedFDeriv ℝ j g) (L (G x)) x := fun x hx ↦
      hasFDerivAt_of_tendstoLocallyUniformlyOn hs hD (fun n z hz ↦ hdiff n j hj z hz)
        (fun z hz ↦ hP.tendsto_at hz) hx
    refine ⟨fun x hx ↦ (hder x hx).differentiableAt.differentiableWithinAt,
      hG.congr_right fun x hx ↦ ?_⟩
    simp [iteratedFDeriv_succ_eq_comp_left, (hder x hx).fderiv, L]
  have hP : ∀ j ≤ k, TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ j (f n))
      (iteratedFDeriv ℝ j g) l s := by
    intro j hj
    induction j with
    | zero => exact h0'
    | succ j ih => exact (step j hj (ih (by omega))).2
  refine ⟨?_, hP⟩
  have hc : ∀ m : ℕ, (m : ℕ∞) ≤ (k : ℕ∞) →
      ContinuousOn (fun x ↦ iteratedFDerivWithin ℝ m g s x) s := fun m hm ↦ by
    have hm : m ≤ k := by exact_mod_cast hm
    exact ((hP m hm).continuousOn (Eventually.of_forall fun n ↦ hcont n m hm).frequently).congr
      fun x hx ↦ iteratedFDerivWithin_of_isOpen m hs hx
  have hd : ∀ m : ℕ, (m : ℕ∞) < (k : ℕ∞) →
      DifferentiableOn ℝ (fun x ↦ iteratedFDerivWithin ℝ m g s x) s := fun m hm ↦ by
    have hm : m < k := by exact_mod_cast hm
    exact (step m hm (hP m hm.le)).1.congr fun x hx ↦ iteratedFDerivWithin_of_isOpen m hs hx
  exact_mod_cast contDiffOn_of_continuousOn_differentiableOn hc hd

variable {d : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot] {s : Set (E d × ℝ)}
  {f : ι → E d × ℝ → ℝ} {g : E d × ℝ → ℝ}

/-- If scalar `fₙ` are `Cᵏ` on an open set, converge pointwise to `g`, and their coordinate
partials of order `≤ k` converge locally uniformly, then `g` is `Cᵏ` and its partials are the
limits. -/
theorem contDiffOn_of_tendstoLocallyUniformlyOn_partials (hs : IsOpen s) {k : ℕ}
    (hf : ∀ n, ContDiffOn ℝ k (f n) s) (hfg : ∀ x ∈ s, Tendsto (fun n ↦ f n x) l (𝓝 (g x)))
    (hconv : ∀ w : List (Fin (d + 1)), w.length ≤ k →
      ∃ G, TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (f n)) G l s) :
    ContDiffOn ℝ k g s ∧
      ∀ w : List (Fin (d + 1)), w.length ≤ k →
        TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (f n)) (iterPartial w g) l s := by
  -- `fₙ → g` locally uniformly (the limit of `∂^[] fₙ = fₙ` is the pointwise limit `g`)
  have h0 : TendstoLocallyUniformlyOn f g l s := by
    obtain ⟨G, hG⟩ := hconv [] (Nat.zero_le _)
    exact hG.congr_right fun x hx ↦ tendsto_nhds_unique (hG.tendsto_at hx) (hfg x hx)
  induction k generalizing f g with
  | zero =>
    refine ⟨?_, fun w hw ↦ ?_⟩
    · simpa using h0.continuousOn (Eventually.of_forall fun n ↦ (hf n).continuousOn).frequently
    · obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
      exact h0
  | succ k ih =>
    have hf' : ∀ n, ContDiffOn ℝ (k + 1) (f n) s := fun n ↦ by exact_mod_cast hf n
    choose G hG using fun j : Fin (d + 1) ↦ hconv [j] (by simp)
    -- the derivatives converge locally uniformly to `∑ⱼ Gⱼ eⱼ*`
    have hD : TendstoLocallyUniformlyOn (fun n z ↦ fderiv ℝ (f n) z)
        (fun z ↦ ∑ j, G j z • ecoord d j) l s := by
      simp_rw [fderiv_eq_sum_partialDeriv]
      exact tendstoLocallyUniformlyOn_finsetSum' _ fun j _ ↦
        tendstoLocallyUniformlyOn_smul_const' (hG j) _
    have hderiv : ∀ x ∈ s, HasFDerivAt g (∑ j, G j x • ecoord d j) x := fun x hx ↦
      hasFDerivAt_of_tendstoLocallyUniformlyOn hs hD
        (fun n z hz ↦ (((hf' n).differentiableOn (by simp) z hz).differentiableAt
          (hs.mem_nhds hz)).hasFDerivAt) hfg hx
    have hpg : ∀ j, ∀ x ∈ s, partialDeriv j g x = G j x := by
      intro j x hx
      simp [partialDeriv, (hderiv x hx).fderiv, ecoord_ebasis]
    -- induction hypothesis for the first partials
    have H : ∀ j, ContDiffOn ℝ k (partialDeriv j g) s ∧
        ∀ w : List (Fin (d + 1)), w.length ≤ k →
          TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (partialDeriv j (f n)))
            (iterPartial w (partialDeriv j g)) l s := by
      intro j
      have hGj : TendstoLocallyUniformlyOn (fun n ↦ partialDeriv j (f n)) (partialDeriv j g) l s :=
        (hG j).congr_right fun x hx ↦ (hpg j x hx).symm
      refine ih (fun n ↦ ContDiffOn.partialDeriv hs (hf' n) j) (fun x hx ↦ hGj.tendsto_at hx)
        (fun w hw ↦ ?_) hGj
      simpa [iterPartial_concat] using hconv (w ++ [j]) (by simpa using hw)
    refine ⟨?_, fun w hw ↦ ?_⟩
    · rw [Nat.cast_add_one, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      rw [show fderiv ℝ g = fun z ↦ ∑ j, partialDeriv j g z • ecoord d j from
        funext (fderiv_eq_sum_partialDeriv g)]
      exact ContDiffOn.sum fun j _ ↦ (H j).1.smul contDiffOn_const
    · rcases List.eq_nil_or_concat' w with rfl | ⟨w', j, rfl⟩
      · exact h0
      · simp_rw [iterPartial_concat]
        exact (H j).2 w' (by simpa using hw)

/-- The `C^∞` version of `contDiffOn_of_tendstoLocallyUniformlyOn_partials`. -/
theorem contDiffOn_infty_of_tendstoLocallyUniformlyOn_partials (hs : IsOpen s)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) s) (hfg : ∀ x ∈ s, Tendsto (fun n ↦ f n x) l (𝓝 (g x)))
    (hconv : ∀ w : List (Fin (d + 1)),
      ∃ G, TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (f n)) G l s) :
    ContDiffOn ℝ ∞ g s ∧
      ∀ w : List (Fin (d + 1)),
        TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (f n)) (iterPartial w g) l s := by
  have H : ∀ k : ℕ, ContDiffOn ℝ k g s ∧ ∀ w : List (Fin (d + 1)), w.length ≤ k →
      TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (f n)) (iterPartial w g) l s := fun k ↦
    contDiffOn_of_tendstoLocallyUniformlyOn_partials hs (fun n ↦ contDiffOn_infty.1 (hf n) k) hfg
      fun w _ ↦ hconv w
  exact ⟨contDiffOn_infty.2 fun k ↦ (H k).1, fun w ↦ (H w.length).2 w le_rfl⟩

/-- Cauchy variant: locally uniformly Cauchy partials of order `≤ k`
(and pointwise convergence of `fₙ`) suffice. -/
theorem contDiffOn_of_uniformCauchySeqOn_partials (hs : IsOpen s) {k : ℕ}
    (hf : ∀ n, ContDiffOn ℝ k (f n) s) (hfg : ∀ x ∈ s, Tendsto (fun n ↦ f n x) l (𝓝 (g x)))
    (hcauchy : ∀ w : List (Fin (d + 1)), w.length ≤ k →
      ∀ x ∈ s, ∃ u ∈ 𝓝 x, UniformCauchySeqOn (fun n ↦ iterPartial w (f n)) l u) :
    ContDiffOn ℝ k g s ∧
      ∀ w : List (Fin (d + 1)), w.length ≤ k →
        TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (f n)) (iterPartial w g) l s :=
  contDiffOn_of_tendstoLocallyUniformlyOn_partials hs hf hfg fun w hw ↦
    ⟨_, tendstoLocallyUniformlyOn_limUnder_of_uniformCauchySeqOn (hcauchy w hw)⟩

/-- The `C^∞` version of `contDiffOn_of_uniformCauchySeqOn_partials`. -/
theorem contDiffOn_infty_of_uniformCauchySeqOn_partials (hs : IsOpen s)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) s) (hfg : ∀ x ∈ s, Tendsto (fun n ↦ f n x) l (𝓝 (g x)))
    (hcauchy : ∀ w : List (Fin (d + 1)),
      ∀ x ∈ s, ∃ u ∈ 𝓝 x, UniformCauchySeqOn (fun n ↦ iterPartial w (f n)) l u) :
    ContDiffOn ℝ ∞ g s ∧
      ∀ w : List (Fin (d + 1)),
        TendstoLocallyUniformlyOn (fun n ↦ iterPartial w (f n)) (iterPartial w g) l s :=
  contDiffOn_infty_of_tendstoLocallyUniformlyOn_partials hs hf hfg fun w ↦
    ⟨_, tendstoLocallyUniformlyOn_limUnder_of_uniformCauchySeqOn (hcauchy w)⟩

end ParabolicBasic
