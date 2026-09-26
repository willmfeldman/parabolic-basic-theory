/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.PartialsSmooth
public import ParabolicBasic.Caloric.BernsteinBasic
public import ParabolicBasic.Schauder.Holder

/-!
# The classes `𝓗ᵐ` of locally Hölder functions with Hölder partials

`HolderCk α m φ Ω`: all space-time coordinate partials `∂^w φ` (`partialDeriv`, `iterPartial`) of
order `|w| ≤ m` exist, are continuous and locally parabolically `α`-Hölder on `Ω`. The definition is
recursive:

* `HolderCk α 0 φ Ω := ContinuousOn φ Ω ∧ LocHolderOnPar α φ Ω`;
* `HolderCk α (m+1) φ Ω := HolderCk α 0 φ Ω ∧ DifferentiableOn ℝ φ Ω ∧ ∀ j, HolderCk α m (∂ⱼ φ) Ω`.

Algebra (all on an open `Ω`, by induction on `m` generalizing the functions): `mono_order`,
`congr`, `const`, `add`, `mul`, `neg`, and `comp_contDiff` (`p ↦ G (p, u p)` for `G` of class
`C^∞`; the chain rule `∂ⱼ (G ∘ (id, u)) = G_j ∘ (id, u) + (G_z ∘ (id, u)) ∂ⱼ u` with the `C^∞`
functions `G_j q = DG(q)[(eⱼ, 0)]`, `G_z q = DG(q)[(0, 1)]` replaces Faà di Bruno). Finally
`hasPartialsOn`: `𝓗ᵐ ⊆ HasPartialsOn m`, hence `(∀ m, φ ∈ 𝓗ᵐ) → ContDiffOn ℝ ∞ φ Ω`
(`contDiffOn_infty_of_forall_holderCk`, via `contDiffOn_infty_of_hasPartialsOn`).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- All space-time coordinate partials of order `≤ m` exist, are continuous and locally
parabolically `α`-Hölder on `Ω`. -/
def HolderCk (α : ℝ) : ℕ → (E d × ℝ → ℝ) → Set (E d × ℝ) → Prop
  | 0, φ, Ω => ContinuousOn φ Ω ∧ LocHolderOnPar α φ Ω
  | m + 1, φ, Ω => (ContinuousOn φ Ω ∧ LocHolderOnPar α φ Ω) ∧ DifferentiableOn ℝ φ Ω ∧
      ∀ j : Fin (d + 1), HolderCk α m (partialDeriv j φ) Ω

/-! ### Auxiliary facts on `LocHolderOnPar` and `partialDeriv` -/

/-- `LocHolderOnPar` only depends on the values on `Ω`. -/
theorem LocHolderOnPar.congr_eqOn {α : ℝ} {φ ψ : E d × ℝ → ℝ} {Ω : Set (E d × ℝ)}
    (h : LocHolderOnPar α φ Ω) (he : EqOn φ ψ Ω) : LocHolderOnPar α ψ Ω := by
  intro K hK hKc
  obtain ⟨C, hC⟩ := h K hK hKc
  exact ⟨C, fun p hp q hq ↦ by rw [← he (hK hp), ← he (hK hq)]; exact hC p hp q hq⟩

section PartialDeriv

variable {Ω : Set (E d × ℝ)} {φ ψ : E d × ℝ → ℝ}

/-- Partials only depend on the values on an open set. -/
theorem partialDeriv_congr_of_eqOn (hΩ : IsOpen Ω) (he : EqOn φ ψ Ω) (j : Fin (d + 1)) :
    EqOn (partialDeriv j φ) (partialDeriv j ψ) Ω := fun p hp ↦ by
  simp only [partialDeriv]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hp) he)]

/-- The chain rule along the graph: `∂ⱼ (G (·, u ·)) = DG[(eⱼ, 0)] + DG[(0, 1)] ∂ⱼ u`. -/
theorem partialDeriv_comp_graph {G : (E d × ℝ) × ℝ → ℝ} {u : E d × ℝ → ℝ} {p : E d × ℝ}
    (hG : DifferentiableAt ℝ G (p, u p)) (hu : DifferentiableAt ℝ u p) (j : Fin (d + 1)) :
    partialDeriv j (fun q ↦ G (q, u q)) p =
      fderiv ℝ G (p, u p) (ebasis d j, 0) +
        fderiv ℝ G (p, u p) ((0 : E d × ℝ), (1 : ℝ)) * partialDeriv j u p := by
  have h1 : HasFDerivAt (fun q ↦ (q, u q))
      ((ContinuousLinearMap.id ℝ (E d × ℝ)).prod (fderiv ℝ u p)) p :=
    (hasFDerivAt_id p).prodMk hu.hasFDerivAt
  have h2 : HasFDerivAt (fun q ↦ G (q, u q)) _ p := hG.hasFDerivAt.comp p h1
  simp only [partialDeriv]
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq]
  have e : ((ebasis d j, fderiv ℝ u p (ebasis d j)) : (E d × ℝ) × ℝ) =
      (ebasis d j, 0) + (fderiv ℝ u p (ebasis d j)) • ((0 : E d × ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [e, map_add, map_smul, smul_eq_mul, mul_comm]

end PartialDeriv

/-! ### Algebra of `HolderCk` -/

namespace HolderCk

variable {α : ℝ} {Ω : Set (E d × ℝ)}

theorem zero_iff {φ : E d × ℝ → ℝ} :
    HolderCk α 0 φ Ω ↔ ContinuousOn φ Ω ∧ LocHolderOnPar α φ Ω := Iff.rfl

theorem succ_iff {m : ℕ} {φ : E d × ℝ → ℝ} :
    HolderCk α (m + 1) φ Ω ↔ HolderCk α 0 φ Ω ∧ DifferentiableOn ℝ φ Ω ∧
      ∀ j : Fin (d + 1), HolderCk α m (partialDeriv j φ) Ω := Iff.rfl

/-- Level `0` is implied by every level. -/
theorem zero {m : ℕ} {φ : E d × ℝ → ℝ} (h : HolderCk α m φ Ω) : HolderCk α 0 φ Ω := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

theorem continuousOn {m : ℕ} {φ : E d × ℝ → ℝ} (h : HolderCk α m φ Ω) : ContinuousOn φ Ω :=
  h.zero.1

theorem locHolderOnPar {m : ℕ} {φ : E d × ℝ → ℝ} (h : HolderCk α m φ Ω) :
    LocHolderOnPar α φ Ω :=
  h.zero.2

/-- `𝓗^{m+1} ⊆ 𝓗^m`. -/
theorem mono_order {m : ℕ} {φ : E d × ℝ → ℝ} (h : HolderCk α (m + 1) φ Ω) :
    HolderCk α m φ Ω := by
  induction m generalizing φ with
  | zero => exact h.1
  | succ m ih => exact ⟨h.1, h.2.1, fun j ↦ ih (h.2.2 j)⟩

/-- Congruence: `𝓗^m` only depends on the values on the open set `Ω`. -/
theorem congr (hΩ : IsOpen Ω) {m : ℕ} {φ ψ : E d × ℝ → ℝ} (h : HolderCk α m φ Ω)
    (he : EqOn φ ψ Ω) : HolderCk α m ψ Ω := by
  induction m generalizing φ ψ with
  | zero => exact ⟨h.1.congr he.symm, h.2.congr_eqOn he⟩
  | succ m ih =>
    exact ⟨⟨h.1.1.congr he.symm, h.1.2.congr_eqOn he⟩, h.2.1.congr he.symm,
      fun j ↦ ih (h.2.2 j) (partialDeriv_congr_of_eqOn hΩ he j)⟩

theorem const (m : ℕ) (c : ℝ) : HolderCk α m (fun _ ↦ c) Ω := by
  induction m generalizing c with
  | zero => exact ⟨continuousOn_const, LocHolderOnPar.const c α Ω⟩
  | succ m ih =>
    refine ⟨⟨continuousOn_const, LocHolderOnPar.const c α Ω⟩,
      differentiableOn_const c, fun j ↦ ?_⟩
    have : partialDeriv j (fun _ : E d × ℝ ↦ c) = fun _ ↦ 0 :=
      funext (partialDeriv_const c j)
    rw [this]
    exact ih 0

theorem differentiableAt (hΩ : IsOpen Ω) {m : ℕ} {φ : E d × ℝ → ℝ}
    (h : HolderCk α (m + 1) φ Ω) {p : E d × ℝ} (hp : p ∈ Ω) : DifferentiableAt ℝ φ p :=
  (h.2.1 p hp).differentiableAt (hΩ.mem_nhds hp)

theorem add (hΩ : IsOpen Ω) {m : ℕ} {φ ψ : E d × ℝ → ℝ} (hφ : HolderCk α m φ Ω)
    (hψ : HolderCk α m ψ Ω) : HolderCk α m (fun p ↦ φ p + ψ p) Ω := by
  induction m generalizing φ ψ with
  | zero => exact ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  | succ m ih =>
    refine ⟨⟨hφ.1.1.add hψ.1.1, hφ.1.2.add hψ.1.2⟩, hφ.2.1.add hψ.2.1, fun j ↦ ?_⟩
    refine (ih (hφ.2.2 j) (hψ.2.2 j)).congr hΩ fun p hp ↦ ?_
    exact (partialDeriv_add (hφ.differentiableAt hΩ hp) (hψ.differentiableAt hΩ hp) j).symm

theorem mul (hΩ : IsOpen Ω) (hα : 0 ≤ α) {m : ℕ} {φ ψ : E d × ℝ → ℝ} (hφ : HolderCk α m φ Ω)
    (hψ : HolderCk α m ψ Ω) : HolderCk α m (fun p ↦ φ p * ψ p) Ω := by
  induction m generalizing φ ψ with
  | zero => exact ⟨hφ.1.mul hψ.1, hφ.2.mul hα hψ.2⟩
  | succ m ih =>
    refine ⟨⟨hφ.1.1.mul hψ.1.1, hφ.1.2.mul hα hψ.1.2⟩, hφ.2.1.mul hψ.2.1, fun j ↦ ?_⟩
    refine ((ih hφ.mono_order (hψ.2.2 j)).add hΩ (ih hψ.mono_order (hφ.2.2 j))).congr hΩ
      fun p hp ↦ ?_
    exact (partialDeriv_mul (hφ.differentiableAt hΩ hp) (hψ.differentiableAt hΩ hp) j).symm

theorem neg (hΩ : IsOpen Ω) (hα : 0 ≤ α) {m : ℕ} {φ : E d × ℝ → ℝ} (hφ : HolderCk α m φ Ω) :
    HolderCk α m (fun p ↦ -φ p) Ω :=
  ((const m (-1)).mul hΩ hα hφ).congr hΩ fun p _ ↦ by simp

/-- Composition with a `C^∞` function of `(p, u p)`. -/
theorem comp_contDiff (hΩ : IsOpen Ω) (hα : 0 < α ∧ α ≤ 1) {m : ℕ}
    {G : (E d × ℝ) × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {u : E d × ℝ → ℝ}
    (hu : HolderCk α m u Ω) : HolderCk α m (fun p ↦ G (p, u p)) Ω := by
  have base : ∀ {G : (E d × ℝ) × ℝ → ℝ}, ContDiff ℝ ∞ G → ∀ {u : E d × ℝ → ℝ},
      HolderCk α 0 u Ω → HolderCk α 0 (fun p ↦ G (p, u p)) Ω := by
    intro G hG u hu
    refine ⟨hG.continuous.comp_continuousOn (continuousOn_id.prodMk hu.1), ?_⟩
    have hG1 : ContDiff ℝ 1 (fun z : (E d × ℝ) × ℝ ↦ G (z.1, z.2)) := hG.of_le (by simp)
    exact hu.2.comp_contDiff (G := fun p z ↦ G (p, z)) hα hG1
  induction m generalizing G u with
  | zero => exact base hG hu
  | succ m ih =>
    have hGd : Differentiable ℝ G := hG.differentiable (by simp)
    refine ⟨base hG hu.1, fun p hp ↦ ?_, fun j ↦ ?_⟩
    · exact ((hGd _).comp p ((differentiableAt_id).prodMk
        (hu.differentiableAt hΩ hp))).differentiableWithinAt
    · set Gj : (E d × ℝ) × ℝ → ℝ := fun q ↦ fderiv ℝ G q (ebasis d j, 0) with hGj
      set Gz : (E d × ℝ) × ℝ → ℝ := fun q ↦ fderiv ℝ G q ((0 : E d × ℝ), (1 : ℝ)) with hGz
      have hdG : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
      have hGjc : ContDiff ℝ ∞ Gj := hdG.clm_apply contDiff_const
      have hGzc : ContDiff ℝ ∞ Gz := hdG.clm_apply contDiff_const
      refine ((ih hGjc hu.mono_order).add hΩ
        ((ih hGzc hu.mono_order).mul hΩ hα.1.le (hu.2.2 j))).congr hΩ fun p hp ↦ ?_
      exact (partialDeriv_comp_graph (hGd _) (hu.differentiableAt hΩ hp) j).symm

/-- `𝓗^m ⊆ HasPartialsOn m` on an open set. -/
theorem hasPartialsOn (hΩ : IsOpen Ω) {m : ℕ} {φ : E d × ℝ → ℝ} (h : HolderCk α m φ Ω) :
    HasPartialsOn m φ Ω := by
  induction m generalizing φ with
  | zero =>
    intro w hw
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    exact ⟨by simpa using h.1, fun h ↦ absurd h (lt_irrefl 0)⟩
  | succ m ih =>
    intro w hw
    rcases List.eq_nil_or_concat' w with rfl | ⟨w', j, rfl⟩
    · exact ⟨h.continuousOn, fun _ z hz ↦ h.differentiableAt hΩ hz⟩
    · have := ih (h.2.2 j) w' (by simpa using hw)
      rw [iterPartial_concat]
      exact ⟨this.1, fun hlt ↦ this.2 (by simpa using hlt)⟩

end HolderCk

/-- A function in every `𝓗^m` is `C^∞` on the open set `Ω` (`ContDiffOn ℝ ∞`, never `⊤`). -/
theorem contDiffOn_infty_of_forall_holderCk {α : ℝ} {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {φ : E d × ℝ → ℝ} (h : ∀ m, HolderCk α m φ Ω) : ContDiffOn ℝ ∞ φ Ω :=
  contDiffOn_infty_of_hasPartialsOn hΩ fun m ↦ (h m).hasPartialsOn hΩ

/-- `d = 0` regression: only the time direction exists, and the algebra is unchanged. -/
example {α : ℝ} {Ω : Set (E 0 × ℝ)} (hΩ : IsOpen Ω) {φ : E 0 × ℝ → ℝ} (m : ℕ)
    (h : HolderCk α m φ Ω) : HasPartialsOn m φ Ω :=
  h.hasPartialsOn hΩ

end ParabolicBasic
