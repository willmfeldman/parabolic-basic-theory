/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.PartialsSmooth
public import ParabolicBasic.Calculus.Affine
public import ParabolicBasic.Calculus.Slice
public import ParabolicBasic.Defs.Parabolic

/-!
# Smooth caloric functions: definitions and calculus

* `IsSmoothCaloricOn O v`: `v` is `C^∞` on `O` and `dₜ v = lapₓ v` on `O`;
* `closedParCyl x t r = closedBall x r ×ˢ Icc (t - r²) t`, the closed backward cylinder;
* `parOrder w`: the parabolic order of a word of partials (space letters count `1`, the time letter
  `Fin.last d` counts `2`);
* `heatP f z := ∂_last f z - ∑ᵢ ∂ᵢ∂ᵢ f z`, the heat operator written with coordinate partials; on
  an open set where `f` is `C²` it equals `dₜ f - lapₓ f` (`heatP_eq_dₜ_sub_lapₓ`, via the slice
  dictionary);
* calculus: coordinate partials of smooth caloric functions are smooth caloric
  (`IsSmoothCaloricOn.partial`, `.iterPartial`, `.dₜ`), the product rule
  `heatP_mul`, and the parabolic rescaling `IsSmoothCaloricOn.comp_parAffine` together with
  `iterPartial_comp_parAffine` (`∂^w (v ∘ A) = r ^ parOrder w · (∂^w v) ∘ A`).

Everything is done in the coordinate-partials language (`partialDeriv`, `iterPartial`); the only
link to the slice operators `dₜ`, `lapₓ`, `gradₓ` is the dictionary of
`ParabolicBasic.Analysis.Partials`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Definitions -/

/-- `v` is smooth caloric on `O`: `v ∈ C^∞(O)` and `∂ₜ v = Δₓ v` on `O`.
(`C^∞` is `ContDiffOn ℝ ∞`, never `ω`: caloric functions are not analytic in time.) -/
def IsSmoothCaloricOn (O : Set (E d × ℝ)) (v : E d × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ v O ∧ ∀ p ∈ O, dₜ v p = lapₓ v p

/-- The closed backward parabolic cylinder `B̄_r(x) × [t - r², t]`. -/
def closedParCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := closedBall x r ×ˢ Icc (t - r ^ 2) t

/-- The parabolic order of a word of partials: space letters count `1`, the time letter
`Fin.last d` counts `2`. -/
def parOrder : List (Fin (d + 1)) → ℕ
  | [] => 0
  | j :: w => (if j = Fin.last d then 2 else 1) + parOrder w

@[simp] theorem parOrder_nil : parOrder ([] : List (Fin (d + 1))) = 0 := rfl

@[simp] theorem parOrder_cons (j : Fin (d + 1)) (w : List (Fin (d + 1))) :
    parOrder (j :: w) = (if j = Fin.last d then 2 else 1) + parOrder w := rfl

/-- The heat operator in coordinate partials: `∂_last f - ∑ᵢ ∂ᵢ∂ᵢ f`. -/
noncomputable def heatP (f : E d × ℝ → ℝ) (z : E d × ℝ) : ℝ :=
  partialDeriv (Fin.last d) f z -
    ∑ i : Fin d, partialDeriv i.castSucc (partialDeriv i.castSucc f) z

theorem mem_closedParCyl {x : E d} {t r : ℝ} {q : E d × ℝ} :
    q ∈ closedParCyl x t r ↔ dist q.1 x ≤ r ∧ t - r ^ 2 ≤ q.2 ∧ q.2 ≤ t := Iff.rfl

theorem center_mem_closedParCyl (x : E d) (t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (x, t) ∈ closedParCyl x t r :=
  ⟨mem_closedBall_self hr, by simp only [mem_Icc]; constructor <;> nlinarith⟩

theorem isCompact_closedParCyl (x : E d) (t r : ℝ) : IsCompact (closedParCyl x t r) :=
  (isCompact_closedBall x r).prod isCompact_Icc

/-- Nested cylinders: the cylinder of radius `r/2` around a point of `closedParCyl x t (r/2)` lies
in `closedParCyl x t r`. -/
theorem closedParCyl_half_subset {x : E d} {t r : ℝ} {q : E d × ℝ}
    (hq : q ∈ closedParCyl x t (r / 2)) : closedParCyl q.1 q.2 (r / 2) ⊆ closedParCyl x t r := by
  rintro ⟨y, s⟩ ⟨hy, hs1, hs2⟩
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · have := dist_triangle y q.1 x
    simp only [mem_closedBall] at hy hq1 ⊢
    linarith
  · have : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  · simp only at hs2; linarith

/-! ### Calculus of coordinate partials -/

section PartialCalculus

variable {f g : E d × ℝ → ℝ} {z : E d × ℝ}

theorem partialDeriv_congr_nhds (h : f =ᶠ[𝓝 z] g) (j : Fin (d + 1)) :
    partialDeriv j f z = partialDeriv j g z := by
  simp only [partialDeriv, h.fderiv_eq]

theorem partialDeriv_const (c : ℝ) (j : Fin (d + 1)) (z : E d × ℝ) :
    partialDeriv j (fun _ ↦ c) z = 0 := by
  simp [partialDeriv]

theorem partialDeriv_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (j : Fin (d + 1)) :
    partialDeriv j (fun y ↦ f y + g y) z = partialDeriv j f z + partialDeriv j g z := by
  simp [partialDeriv, fderiv_fun_add hf hg]

theorem partialDeriv_sub (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (j : Fin (d + 1)) :
    partialDeriv j (fun y ↦ f y - g y) z = partialDeriv j f z - partialDeriv j g z := by
  simp [partialDeriv, fderiv_fun_sub hf hg]

theorem partialDeriv_const_mul (hf : DifferentiableAt ℝ f z) (a : ℝ) (j : Fin (d + 1)) :
    partialDeriv j (fun y ↦ a * f y) z = a * partialDeriv j f z := by
  simp [partialDeriv, fderiv_const_mul hf]

theorem partialDeriv_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (j : Fin (d + 1)) :
    partialDeriv j (fun y ↦ f y * g y) z =
      f z * partialDeriv j g z + g z * partialDeriv j f z := by
  simp [partialDeriv, fderiv_fun_mul hf hg]

theorem partialDeriv_sum {ι : Type*} (S : Finset ι) {F : ι → E d × ℝ → ℝ}
    (hF : ∀ i ∈ S, DifferentiableAt ℝ (F i) z) (j : Fin (d + 1)) :
    partialDeriv j (fun y ↦ ∑ i ∈ S, F i y) z = ∑ i ∈ S, partialDeriv j (F i) z := by
  simp [partialDeriv, fderiv_fun_sum hF]

end PartialCalculus

/-! ### Partials of smooth functions on open sets -/

section OpenSet

variable {O : Set (E d × ℝ)} {f g v : E d × ℝ → ℝ} {z : E d × ℝ}

private theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

theorem differentiableAt_iterPartial (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (w : List (Fin (d + 1))) (hz : z ∈ O) : DifferentiableAt ℝ (iterPartial w f) z :=
  ((ContDiffOn.iterPartial hO hf w).differentiableOn (by simp) z hz).differentiableAt
    (hO.mem_nhds hz)

theorem differentiableAt_partialDeriv (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (j : Fin (d + 1)) (hz : z ∈ O) : DifferentiableAt ℝ (partialDeriv j f) z :=
  differentiableAt_iterPartial hO hf [j] hz

theorem contDiffOn_partialDeriv (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (j : Fin (d + 1)) : ContDiffOn ℝ ∞ (partialDeriv j f) O :=
  ContDiffOn.iterPartial hO hf [j]

theorem differentiableAt_of_contDiffOn (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hz : z ∈ O) :
    DifferentiableAt ℝ f z :=
  differentiableAt_iterPartial hO hf [] hz

/-- Linearity of iterated partials of smooth functions on an open set. -/
theorem iterPartial_linear_comb (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hg : ContDiffOn ℝ ∞ g O) (a b : ℝ) (w : List (Fin (d + 1))) :
    ∀ z ∈ O, iterPartial w (fun y ↦ a * f y + b * g y) z =
      a * iterPartial w f z + b * iterPartial w g z := by
  induction w with
  | nil => intro z _; rfl
  | cons j w ih =>
    intro z hz
    have hev : iterPartial w (fun y ↦ a * f y + b * g y) =ᶠ[𝓝 z]
        fun y ↦ a * iterPartial w f y + b * iterPartial w g y :=
      Filter.eventually_of_mem (hO.mem_nhds hz) ih
    simp only [iterPartial_cons]
    rw [partialDeriv_congr_nhds hev, partialDeriv_add
      ((differentiableAt_iterPartial hO hf w hz).const_mul a)
      ((differentiableAt_iterPartial hO hg w hz).const_mul b),
      partialDeriv_const_mul (differentiableAt_iterPartial hO hf w hz),
      partialDeriv_const_mul (differentiableAt_iterPartial hO hg w hz)]

theorem iterPartial_sub (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (w : List (Fin (d + 1))) :
    ∀ z ∈ O, iterPartial w (fun y ↦ f y - g y) z = iterPartial w f z - iterPartial w g z := by
  intro z hz
  have h := iterPartial_linear_comb hO hf hg 1 (-1) w z hz
  have he : (fun y ↦ f y - g y) = fun y ↦ 1 * f y + -1 * g y := by funext y; ring
  rw [he, h]; ring

theorem iterPartial_add (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (w : List (Fin (d + 1))) :
    ∀ z ∈ O, iterPartial w (fun y ↦ f y + g y) z = iterPartial w f z + iterPartial w g z := by
  intro z hz
  have h := iterPartial_linear_comb hO hf hg 1 1 w z hz
  have he : (fun y ↦ f y + g y) = fun y ↦ 1 * f y + 1 * g y := by funext y; ring
  rw [he, h]; ring

theorem iterPartial_const_mul (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (a : ℝ)
    (w : List (Fin (d + 1))) :
    ∀ z ∈ O, iterPartial w (fun y ↦ a * f y) z = a * iterPartial w f z := by
  intro z hz
  have h := iterPartial_linear_comb hO hf hf a 0 w z hz
  have he : (fun y ↦ a * f y) = fun y ↦ a * f y + 0 * f y := by funext y; ring
  rw [he, h]; ring

/-- Iterated partials commute with finite sums of smooth functions on an open set. -/
theorem iterPartial_finset_sum {ι : Type*} (hO : IsOpen O) (S : Finset ι)
    {F : ι → E d × ℝ → ℝ} (hF : ∀ k ∈ S, ContDiffOn ℝ ∞ (F k) O) (w : List (Fin (d + 1))) :
    ∀ z ∈ O, iterPartial w (fun y ↦ ∑ k ∈ S, F k y) z = ∑ k ∈ S, iterPartial w (F k) z := by
  induction w with
  | nil => intro z _; rfl
  | cons j w ih =>
    intro z hz
    have hev : iterPartial w (fun y ↦ ∑ k ∈ S, F k y) =ᶠ[𝓝 z]
        fun y ↦ ∑ k ∈ S, iterPartial w (F k) y :=
      Filter.eventually_of_mem (hO.mem_nhds hz) ih
    simp only [iterPartial_cons]
    rw [partialDeriv_congr_nhds hev,
      partialDeriv_sum S fun k hk ↦ differentiableAt_iterPartial hO (hF k hk) w hz]

/-- `iterPartial` depends only on the values on an open set. -/
theorem iterPartial_congr_of_eqOn (hO : IsOpen O) (h : EqOn f g O) (w : List (Fin (d + 1))) :
    EqOn (iterPartial w f) (iterPartial w g) O := by
  induction w with
  | nil => exact h
  | cons j w ih =>
    intro z hz
    exact partialDeriv_congr_nhds (Filter.eventually_of_mem (hO.mem_nhds hz) ih) j

/-- **The slice dictionary, packaged.** On an open set where `f` is `C²`,
`heatP f = dₜ f - lapₓ f`. -/
theorem heatP_eq_dₜ_sub_lapₓ (hO : IsOpen O) (hf : ContDiffOn ℝ 2 f O) (hz : z ∈ O) :
    heatP f z = dₜ f z - lapₓ f z := by
  rw [heatP, dₜ_eq_partialDeriv_last ((hf.differentiableOn (by norm_num) z hz).differentiableAt
    (hO.mem_nhds hz)), lapₓ_eq_sum_partialDeriv hO hf hz]

theorem heatP_sub (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (hz : z ∈ O) : heatP (fun y ↦ f y - g y) z = heatP f z - heatP g z := by
  have h1 := iterPartial_sub hO hf hg [Fin.last d] z hz
  have h2 := fun i : Fin d ↦ iterPartial_sub hO hf hg [i.castSucc, i.castSucc] z hz
  simp only [iterPartial_cons, iterPartial_nil] at h1 h2
  simp only [heatP, h1, h2, Finset.sum_sub_distrib]
  ring

theorem heatP_linear_comb (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (a b : ℝ) (hz : z ∈ O) :
    heatP (fun y ↦ a * f y + b * g y) z = a * heatP f z + b * heatP g z := by
  have h1 := iterPartial_linear_comb hO hf hg a b [Fin.last d] z hz
  have h2 := fun i : Fin d ↦ iterPartial_linear_comb hO hf hg a b [i.castSucc, i.castSucc] z hz
  simp only [iterPartial_cons, iterPartial_nil] at h1 h2
  simp only [heatP, h1, h2, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem heatP_finset_sum {ι : Type*} (hO : IsOpen O) {S : Finset ι} {F : ι → E d × ℝ → ℝ}
    (hF : ∀ k ∈ S, ContDiffOn ℝ ∞ (F k) O) (hz : z ∈ O) :
    heatP (fun y ↦ ∑ k ∈ S, F k y) z = ∑ k ∈ S, heatP (F k) z := by
  have h1 := iterPartial_finset_sum hO S hF [Fin.last d] z hz
  have h2 := fun i : Fin d ↦ iterPartial_finset_sum hO S hF [i.castSucc, i.castSucc] z hz
  simp only [iterPartial_cons, iterPartial_nil] at h1 h2
  simp only [heatP, h1, h2, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem heatP_const (c : ℝ) (z : E d × ℝ) : heatP (fun _ ↦ c) z = 0 := by
  have h : ∀ j, partialDeriv j (fun _ : E d × ℝ ↦ c) = fun _ ↦ 0 := fun j ↦
    funext fun y ↦ partialDeriv_const c j y
  simp [heatP, h, partialDeriv_const]

/-- Product rule for the first partials, near a point of an open set. -/
theorem partialDeriv_mul_eventuallyEq (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hg : ContDiffOn ℝ ∞ g O) (j : Fin (d + 1)) (hz : z ∈ O) :
    partialDeriv j (fun y ↦ f y * g y) =ᶠ[𝓝 z]
      fun y ↦ f y * partialDeriv j g y + g y * partialDeriv j f y :=
  Filter.eventually_of_mem (hO.mem_nhds hz) fun _ hy ↦
    partialDeriv_mul (differentiableAt_iterPartial hO hf [] hy)
      (differentiableAt_iterPartial hO hg [] hy) j

/-- **Product rule**:
`H(fg) = f Hg + g Hf - 2 ∑ᵢ ∂ᵢf ∂ᵢg` (in partials). -/
theorem heatP_mul (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (hz : z ∈ O) :
    heatP (fun y ↦ f y * g y) z = f z * heatP g z + g z * heatP f z -
      2 * ∑ i : Fin d, partialDeriv i.castSucc f z * partialDeriv i.castSucc g z := by
  have hf0 := differentiableAt_of_contDiffOn hO hf hz
  have hg0 := differentiableAt_of_contDiffOn hO hg hz
  have hf1 := fun j ↦ differentiableAt_partialDeriv hO hf j hz
  have hg1 := fun j ↦ differentiableAt_partialDeriv hO hg j hz
  have hlast : partialDeriv (Fin.last d) (fun y ↦ f y * g y) z =
      f z * partialDeriv (Fin.last d) g z + g z * partialDeriv (Fin.last d) f z :=
    partialDeriv_mul hf0 hg0 _
  have hii : ∀ i : Fin d, partialDeriv i.castSucc (partialDeriv i.castSucc
      (fun y ↦ f y * g y)) z =
      f z * partialDeriv i.castSucc (partialDeriv i.castSucc g) z +
        g z * partialDeriv i.castSucc (partialDeriv i.castSucc f) z +
        2 * (partialDeriv i.castSucc f z * partialDeriv i.castSucc g z) := by
    intro i
    rw [partialDeriv_congr_nhds (partialDeriv_mul_eventuallyEq hO hf hg _ hz),
      partialDeriv_add (hf0.fun_mul (hg1 i.castSucc)) (hg0.fun_mul (hf1 i.castSucc)),
      partialDeriv_mul hf0 (hg1 i.castSucc), partialDeriv_mul hg0 (hf1 i.castSucc)]
    ring
  simp only [heatP, hlast, hii, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Mixed partials of a smooth function commute on an open set (`partialDeriv_comm`). -/
theorem partialDeriv_comm_of_contDiffOn (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (i j : Fin (d + 1)) (hz : z ∈ O) :
    partialDeriv i (partialDeriv j f) z = partialDeriv j (partialDeriv i f) z :=
  partialDeriv_comm ((hf.contDiffAt (hO.mem_nhds hz)).of_le two_le_infty) i j

/-- The heat operator commutes with coordinate partials of smooth functions. -/
theorem heatP_partialDeriv (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (j : Fin (d + 1))
    (hz : z ∈ O) : heatP (partialDeriv j f) z = partialDeriv j (heatP f) z := by
  have hd1 : DifferentiableAt ℝ (partialDeriv (Fin.last d) f) z :=
    differentiableAt_partialDeriv hO hf _ hz
  have hd2 : ∀ i : Fin d, DifferentiableAt ℝ
      (partialDeriv i.castSucc (partialDeriv i.castSucc f)) z := fun i ↦
    differentiableAt_partialDeriv hO (contDiffOn_partialDeriv hO hf _) _ hz
  have hsum : partialDeriv j (heatP f) z = partialDeriv j (partialDeriv (Fin.last d) f) z -
      ∑ i : Fin d, partialDeriv j (partialDeriv i.castSucc (partialDeriv i.castSucc f)) z := by
    rw [show heatP f = fun y ↦ partialDeriv (Fin.last d) f y -
      ∑ i : Fin d, partialDeriv i.castSucc (partialDeriv i.castSucc f) y from rfl,
      partialDeriv_sub hd1 (DifferentiableAt.fun_sum fun (i : Fin d) _ ↦ hd2 i),
      partialDeriv_sum _ (fun (i : Fin d) _ ↦ hd2 i)]
  rw [hsum, heatP, partialDeriv_comm_of_contDiffOn hO hf _ _ hz]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- `∂ᵢ∂ᵢ∂ⱼ f = ∂ᵢ∂ⱼ∂ᵢ f = ∂ⱼ∂ᵢ∂ᵢ f`
  have hev : partialDeriv i.castSucc (partialDeriv j f) =ᶠ[𝓝 z]
      partialDeriv j (partialDeriv i.castSucc f) :=
    Filter.eventually_of_mem (hO.mem_nhds hz) fun y hy ↦
      partialDeriv_comm_of_contDiffOn hO hf _ _ hy
  rw [partialDeriv_congr_nhds hev,
    partialDeriv_comm_of_contDiffOn hO (contDiffOn_partialDeriv hO hf i.castSucc) _ _ hz]

end OpenSet

/-! ### Smooth caloric functions -/

section Caloric

variable {O : Set (E d × ℝ)} {f g v : E d × ℝ → ℝ}

theorem isSmoothCaloricOn_iff_heatP (hO : IsOpen O) :
    IsSmoothCaloricOn O v ↔ ContDiffOn ℝ ∞ v O ∧ ∀ p ∈ O, heatP v p = 0 := by
  refine and_congr_right fun hv ↦ forall₂_congr fun p hp ↦ ?_
  rw [heatP_eq_dₜ_sub_lapₓ hO (hv.of_le two_le_infty) hp, sub_eq_zero]

theorem IsSmoothCaloricOn.contDiffOn (hv : IsSmoothCaloricOn O v) : ContDiffOn ℝ ∞ v O := hv.1

theorem IsSmoothCaloricOn.heatP_eq_zero (hO : IsOpen O) (hv : IsSmoothCaloricOn O v) {p}
    (hp : p ∈ O) : heatP v p = 0 :=
  ((isSmoothCaloricOn_iff_heatP hO).1 hv).2 p hp

/-- On a smooth caloric function, the time partial is the sum of the pure second spatial
partials. -/
theorem IsSmoothCaloricOn.partialDeriv_last_eq (hO : IsOpen O) (hv : IsSmoothCaloricOn O v) {p}
    (hp : p ∈ O) : partialDeriv (Fin.last d) v p =
      ∑ i : Fin d, partialDeriv i.castSucc (partialDeriv i.castSucc v) p :=
  sub_eq_zero.1 (hv.heatP_eq_zero hO hp)

theorem IsSmoothCaloricOn.mono {O' : Set (E d × ℝ)} (hv : IsSmoothCaloricOn O v) (h : O' ⊆ O) :
    IsSmoothCaloricOn O' v :=
  ⟨hv.1.mono h, fun p hp ↦ hv.2 p (h hp)⟩

theorem IsSmoothCaloricOn.congr (hO : IsOpen O) (hv : IsSmoothCaloricOn O v) (h : EqOn v f O) :
    IsSmoothCaloricOn O f := by
  refine ⟨hv.1.congr fun p hp ↦ (h hp).symm, fun p hp ↦ ?_⟩
  have hev : v =ᶠ[𝓝 p] f := Filter.eventually_of_mem (hO.mem_nhds hp) h
  rw [← dₜ_congr_nhds hev, ← lapₓ_congr_nhds hev, hv.2 p hp]

theorem IsSmoothCaloricOn.linear_comb (hO : IsOpen O) (hf : IsSmoothCaloricOn O f)
    (hg : IsSmoothCaloricOn O g) (a b : ℝ) :
    IsSmoothCaloricOn O (fun y ↦ a * f y + b * g y) := by
  rw [isSmoothCaloricOn_iff_heatP hO] at *
  refine ⟨(contDiffOn_const.mul hf.1).add (contDiffOn_const.mul hg.1), fun p hp ↦ ?_⟩
  rw [heatP_linear_comb hO hf.1 hg.1 a b hp, hf.2 p hp, hg.2 p hp]
  ring

theorem IsSmoothCaloricOn.sub (hO : IsOpen O) (hf : IsSmoothCaloricOn O f)
    (hg : IsSmoothCaloricOn O g) : IsSmoothCaloricOn O (fun y ↦ f y - g y) := by
  have := hf.linear_comb hO hg 1 (-1)
  exact this.congr hO fun y _ ↦ by ring

theorem IsSmoothCaloricOn.add (hO : IsOpen O) (hf : IsSmoothCaloricOn O f)
    (hg : IsSmoothCaloricOn O g) : IsSmoothCaloricOn O (fun y ↦ f y + g y) := by
  have := hf.linear_comb hO hg 1 1
  exact this.congr hO fun y _ ↦ by ring

theorem IsSmoothCaloricOn.const_mul (hO : IsOpen O) (hf : IsSmoothCaloricOn O f) (a : ℝ) :
    IsSmoothCaloricOn O (fun y ↦ a * f y) := by
  have := hf.linear_comb hO hf a 0
  exact this.congr hO fun y _ ↦ by ring

/-- Every coordinate partial (space or time) of a smooth caloric function is smooth caloric. -/
theorem IsSmoothCaloricOn.partial (hO : IsOpen O) (hv : IsSmoothCaloricOn O v)
    (j : Fin (d + 1)) : IsSmoothCaloricOn O (partialDeriv j v) := by
  rw [isSmoothCaloricOn_iff_heatP hO] at *
  refine ⟨contDiffOn_partialDeriv hO hv.1 j, fun p hp ↦ ?_⟩
  rw [heatP_partialDeriv hO hv.1 j hp,
    partialDeriv_congr_nhds (Filter.eventually_of_mem (hO.mem_nhds hp) hv.2), partialDeriv_const]

/-- Spatial partials of a smooth caloric function are smooth caloric. -/
theorem IsSmoothCaloricOn.partialDeriv_space (hO : IsOpen O) (hv : IsSmoothCaloricOn O v)
    (i : Fin d) : IsSmoothCaloricOn O (partialDeriv i.castSucc v) :=
  hv.partial hO i.castSucc

/-- Iterated partials of a smooth caloric function are smooth caloric. -/
theorem IsSmoothCaloricOn.iteratedPartial (hO : IsOpen O) (hv : IsSmoothCaloricOn O v)
    (w : List (Fin (d + 1))) : IsSmoothCaloricOn O (iterPartial w v) := by
  induction w with
  | nil => exact hv
  | cons j w ih => exact ih.partial hO j

/-- The time derivative of a smooth caloric function is smooth caloric. -/
theorem IsSmoothCaloricOn.timeDeriv (hO : IsOpen O) (hv : IsSmoothCaloricOn O v) :
    IsSmoothCaloricOn O (dₜ v) :=
  (hv.partial hO (Fin.last d)).congr hO fun p hp ↦
    (dₜ_eq_partialDeriv_last ((hv.1.differentiableOn (by simp) p hp).differentiableAt
      (hO.mem_nhds hp))).symm

end Caloric

/-! ### Parabolic rescaling -/

section Scaling

variable {O : Set (E d × ℝ)} {v : E d × ℝ → ℝ} {x₀ : E d} {t₀ r : ℝ}

/-- The linear part of `parAffine x₀ t₀ r`: `(y, s) ↦ (r y, r² s)`. -/
noncomputable def parScale (r : ℝ) : E d × ℝ →L[ℝ] E d × ℝ :=
  (r • ContinuousLinearMap.fst ℝ (E d) ℝ).prod (r ^ 2 • ContinuousLinearMap.snd ℝ (E d) ℝ)

theorem hasFDerivAt_parAffine (x₀ : E d) (t₀ r : ℝ) (q : E d × ℝ) :
    HasFDerivAt (parAffine x₀ t₀ r) (parScale r) q := by
  have h := (parScale (d := d) r).hasFDerivAt (x := q) |>.const_add (x₀, t₀)
  convert h using 1
  funext p
  ext <;> simp [parScale]

theorem parScale_ebasis (r : ℝ) (j : Fin (d + 1)) :
    parScale r (ebasis d j) = r ^ (if j = Fin.last d then 2 else 1) • ebasis d j := by
  induction j using Fin.lastCases with
  | last => simp [parScale]
  | cast i =>
    simp [parScale, Fin.castSucc_ne_last]

/-- Chain rule for a coordinate partial under the parabolic affine map. -/
theorem partialDeriv_comp_parAffine {q : E d × ℝ}
    (hv : DifferentiableAt ℝ v (parAffine x₀ t₀ r q)) (j : Fin (d + 1)) :
    partialDeriv j (v ∘ parAffine x₀ t₀ r) q =
      r ^ (if j = Fin.last d then 2 else 1) * partialDeriv j v (parAffine x₀ t₀ r q) := by
  simp only [partialDeriv, (hv.hasFDerivAt.comp q (hasFDerivAt_parAffine x₀ t₀ r q)).fderiv,
    ContinuousLinearMap.comp_apply, parScale_ebasis, map_smul, smul_eq_mul]

/-- **Scaling of all partials:** `∂^w (v ∘ A) = r ^ parOrder w · (∂^w v) ∘ A` on `A⁻¹(O)`. -/
theorem iterPartial_comp_parAffine (hO : IsOpen O) (hv : ContDiffOn ℝ ∞ v O)
    (w : List (Fin (d + 1))) :
    ∀ q ∈ parAffine x₀ t₀ r ⁻¹' O, iterPartial w (v ∘ parAffine x₀ t₀ r) q =
      r ^ parOrder w * iterPartial w v (parAffine x₀ t₀ r q) := by
  have hO' : IsOpen (parAffine x₀ t₀ r ⁻¹' O) := hO.preimage (continuous_parAffine x₀ t₀ r)
  induction w with
  | nil => intro q _; simp
  | cons j w ih =>
    intro q hq
    have hev : iterPartial w (v ∘ parAffine x₀ t₀ r) =ᶠ[𝓝 q]
        fun y ↦ r ^ parOrder w * (iterPartial w v ∘ parAffine x₀ t₀ r) y :=
      Filter.eventually_of_mem (hO'.mem_nhds hq) ih
    have hd : DifferentiableAt ℝ (iterPartial w v) (parAffine x₀ t₀ r q) :=
      differentiableAt_iterPartial hO hv w hq
    have hdc : DifferentiableAt ℝ (iterPartial w v ∘ parAffine x₀ t₀ r) q :=
      hd.comp q (hasFDerivAt_parAffine x₀ t₀ r q).differentiableAt
    simp only [iterPartial_cons, parOrder_cons]
    rw [partialDeriv_congr_nhds hev, partialDeriv_const_mul hdc, partialDeriv_comp_parAffine hd,
      pow_add]
    ring

/-- Smooth caloric functions are invariant under parabolic affine maps. -/
theorem IsSmoothCaloricOn.comp_parAffine (hO : IsOpen O) (hv : IsSmoothCaloricOn O v)
    (x₀ : E d) (t₀ r : ℝ) :
    IsSmoothCaloricOn (parAffine x₀ t₀ r ⁻¹' O) (v ∘ parAffine x₀ t₀ r) := by
  have hO' : IsOpen (parAffine x₀ t₀ r ⁻¹' O) := hO.preimage (continuous_parAffine x₀ t₀ r)
  rw [isSmoothCaloricOn_iff_heatP hO']
  refine ⟨hv.1.comp (contDiff_parAffine x₀ t₀ r).contDiffOn fun _ hq ↦ hq, fun q hq ↦ ?_⟩
  have h1 : partialDeriv (Fin.last d) (v ∘ parAffine x₀ t₀ r) q =
      r ^ 2 * partialDeriv (Fin.last d) v (parAffine x₀ t₀ r q) := by
    simpa using iterPartial_comp_parAffine hO hv.1 [Fin.last d] q hq
  have h2 : ∀ i : Fin d, partialDeriv i.castSucc (partialDeriv i.castSucc
      (v ∘ parAffine x₀ t₀ r)) q =
      r ^ 2 * partialDeriv i.castSucc (partialDeriv i.castSucc v) (parAffine x₀ t₀ r q) := by
    intro i
    simpa [Fin.castSucc_ne_last] using
      iterPartial_comp_parAffine hO hv.1 [i.castSucc, i.castSucc] q hq
  have h3 := hv.heatP_eq_zero hO hq
  unfold heatP at h3 ⊢
  rw [h1, Finset.sum_congr rfl fun i _ ↦ h2 i, ← Finset.mul_sum, ← mul_sub, h3, mul_zero]

end Scaling

end ParabolicBasic
