/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Defs.Viscosity
public import ParabolicBasic.Transport.Operator
public import ViscositySolns.Solutions
public import ViscositySolns.TestFunctions.Characterization

/-!
# Our viscosity notion is `ViscositySolns`' semijet notion, transported

For arbitrary `Ω`, `F`, `u`:

* `IsViscSubOn Ω F u ↔ SmoothTestFunctionSubsolution Ω♯ (parabolicOp F) u♯` (no openness);
* `IsViscSubOn Ω F u → ViscositySubsolution Ω♯ (parabolicOp F) u♯` (no openness;
  `IsViscSubOn.toViscositySubsolution`), an equivalence when `Ω` is open;
* closed-superjet form for the sum-closure theorem (`IsViscSubOn.closedSuperjet_le`);

and the mirrors for supersolutions and solutions. The comparison principle and the sum-closure
theorem only use "ours ⇒ theirs".
-/

@[expose] public section

open Set Filter Topology

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Test-function form (no openness) -/

/-- Adding a constant to a test function on `Point (d + 1)` changes neither its Fréchet
gradient nor its Fréchet Hessian: the jet of `(φ ∘ e + c)♯ = φ + c` is the jet of `φ`. -/
theorem toPointFun_comp_add_const (φ : ViscositySolns.Point (d + 1) → ℝ) (c : ℝ) :
    toPointFun (fun q ↦ φ (spaceTimeEquiv d q) + c) = fun w ↦ φ w + c := by
  funext w
  simp only [toPointFun, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem fderiv_add_const_fun {n : ℕ} (φ : ViscositySolns.Point n → ℝ) (c : ℝ) :
    fderiv ℝ (fun w ↦ φ w + c) = fderiv ℝ φ := by
  funext w
  exact fderiv_add_const c

/-- The jet identity behind the test-function form, `⇒`: for `C²` `φ` on `Point (d + 1)`, the
operator on the jet of `φ` at `z` is `dₜ − lapₓ + F` of the pulled-back test `φ ∘ e + c` at `e⁻¹ z`.
-/
theorem parabolicOp_smoothJet_of_point (F : E d × ℝ → ℝ → ℝ)
    {φ : ViscositySolns.Point (d + 1) → ℝ} (hφ : ContDiff ℝ 2 φ) (c : ℝ)
    (z : ViscositySolns.Point (d + 1)) (r : ℝ) :
    parabolicOp F z r (ViscositySolns.linearMapGradient (fderiv ℝ φ z))
        (ViscositySolns.bilinearMapHessian (fderiv ℝ (fderiv ℝ φ) z))
      = dₜ (fun q ↦ φ (spaceTimeEquiv d q) + c) ((spaceTimeEquiv d).symm z)
        - lapₓ (fun q ↦ φ (spaceTimeEquiv d q) + c) ((spaceTimeEquiv d).symm z)
        + F ((spaceTimeEquiv d).symm z) r := by
  have hψ : ContDiff ℝ 2 (fun q ↦ φ (spaceTimeEquiv d q) + c) :=
    (hφ.comp (spaceTimeEquiv d).contDiff).add contDiff_const
  have := parabolicOp_smoothJet F hψ ((spaceTimeEquiv d).symm z) r
  rwa [toPointFun_comp_add_const, fderiv_add_const_fun,
    ContinuousLinearEquiv.apply_symm_apply] at this

theorem isViscSubOn_iff_smoothTestFunctionSubsolution {Ω : Set (E d × ℝ)}
    {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ} :
    IsViscSubOn Ω F u ↔
      ViscositySolns.SmoothTestFunctionSubsolution (toPointSet Ω) (parabolicOp F)
        (toPointFun u) := by
  constructor
  · intro hu
    refine ⟨upperSemicontinuousOn_toPointFun_iff.2 hu.1, fun z hz φ hφ htouch ↦ ?_⟩
    have hψ : ContDiff ℝ 2
        (fun q ↦ φ (spaceTimeEquiv d q) + (u ((spaceTimeEquiv d).symm z) - φ z)) :=
      (hφ.comp (spaceTimeEquiv d).contDiff).add contDiff_const
    have h := hu.2 _ hψ _ hz (touchesAbove_of_touchesAboveOn htouch hz)
    rw [parabolicOp_smoothJet_of_point F hφ (u ((spaceTimeEquiv d).symm z) - φ z)]
    exact h
  · intro h
    refine ⟨upperSemicontinuousOn_toPointFun_iff.1 h.1, fun ψ hψ p hp htouch ↦ ?_⟩
    have := h.2 (spaceTimeEquiv d p) (by simpa using hp) (toPointFun ψ)
      (contDiff_toPointFun_iff.2 hψ) htouch.toPoint
    rwa [toPointFun_spaceTimeEquiv, parabolicOp_smoothJet F hψ p] at this

theorem isViscSuperOn_iff_smoothTestFunctionSupersolution {Ω : Set (E d × ℝ)}
    {F : E d × ℝ → ℝ → ℝ} {u : E d × ℝ → ℝ} :
    IsViscSuperOn Ω F u ↔
      ViscositySolns.SmoothTestFunctionSupersolution (toPointSet Ω) (parabolicOp F)
        (toPointFun u) := by
  constructor
  · intro hu
    refine ⟨lowerSemicontinuousOn_toPointFun_iff.2 hu.1, fun z hz φ hφ htouch ↦ ?_⟩
    have hψ : ContDiff ℝ 2
        (fun q ↦ φ (spaceTimeEquiv d q) + (u ((spaceTimeEquiv d).symm z) - φ z)) :=
      (hφ.comp (spaceTimeEquiv d).contDiff).add contDiff_const
    have h := hu.2 _ hψ _ hz (touchesBelow_of_touchesBelowOn htouch hz)
    rw [parabolicOp_smoothJet_of_point F hφ (u ((spaceTimeEquiv d).symm z) - φ z)]
    exact h
  · intro h
    refine ⟨lowerSemicontinuousOn_toPointFun_iff.1 h.1, fun ψ hψ p hp htouch ↦ ?_⟩
    have := h.2 (spaceTimeEquiv d p) (by simpa using hp) (toPointFun ψ)
      (contDiff_toPointFun_iff.2 hψ) htouch.toPoint
    rwa [toPointFun_spaceTimeEquiv, parabolicOp_smoothJet F hψ p] at this

/-! ### Ours ⇒ theirs (no openness) -/

/-- Ours ⇒ `ViscositySolns`' semijet notion: needs no openness. -/
theorem IsViscSubOn.toViscositySubsolution {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsViscSubOn Ω F u) :
    ViscositySolns.ViscositySubsolution (toPointSet Ω) (parabolicOp F) (toPointFun u) :=
  ViscositySolns.ViscositySubsolution.of_smoothTestFunctionSubsolution
    (parabolicOp_continuous_hessian F) (parabolicOp_hessianSymmetricInvariant F)
    (isViscSubOn_iff_smoothTestFunctionSubsolution.1 hu)

/-- Ours ⇒ `ViscositySolns`' semijet notion, supersolution mirror: needs no openness. -/
theorem IsViscSuperOn.toViscositySupersolution {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsViscSuperOn Ω F u) :
    ViscositySolns.ViscositySupersolution (toPointSet Ω) (parabolicOp F) (toPointFun u) :=
  ViscositySolns.ViscositySupersolution.of_smoothTestFunctionSupersolution
    (parabolicOp_continuous_hessian F) (parabolicOp_hessianSymmetricInvariant F)
    (isViscSuperOn_iff_smoothTestFunctionSupersolution.1 hu)

/-! ### Equivalences on open sets -/

theorem isViscSubOn_iff_viscositySubsolution {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) :
    IsViscSubOn Ω F u ↔
      ViscositySolns.ViscositySubsolution (toPointSet Ω) (parabolicOp F) (toPointFun u) := by
  rw [isViscSubOn_iff_smoothTestFunctionSubsolution]
  exact (ViscositySolns.viscositySubsolution_iff_smoothTestFunctionSubsolution
    (isOpen_toPointSet hΩ) (parabolicOp_continuous_hessian F)
    (parabolicOp_hessianSymmetricInvariant F)).symm

theorem isViscSuperOn_iff_viscositySupersolution {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) :
    IsViscSuperOn Ω F u ↔
      ViscositySolns.ViscositySupersolution (toPointSet Ω) (parabolicOp F) (toPointFun u) := by
  rw [isViscSuperOn_iff_smoothTestFunctionSupersolution]
  exact (ViscositySolns.viscositySupersolution_iff_smoothTestFunctionSupersolution
    (isOpen_toPointSet hΩ) (parabolicOp_continuous_hessian F)
    (parabolicOp_hessianSymmetricInvariant F)).symm

theorem isViscSolOn_iff_viscositySolution {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hΩ : IsOpen Ω) :
    IsViscSolOn Ω F u ↔
      ViscositySolns.ViscositySolution (toPointSet Ω) (parabolicOp F) (toPointFun u) := by
  exact and_congr (isViscSubOn_iff_viscositySubsolution hΩ)
    (isViscSuperOn_iff_viscositySupersolution hΩ)

/-! ### Closed-jet forms (for the sum-closure theorem) -/

/-- The closed-superjet inequality, in coordinates. -/
theorem IsViscSubOn.closedSuperjet_le {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsViscSubOn Ω F u)
    (hF : Continuous fun q : (E d × ℝ) × ℝ ↦ F q.1 q.2) {z : ViscositySolns.Point (d + 1)}
    {J : ViscositySolns.Jet (d + 1)}
    (hJ : J ∈ ViscositySolns.ClosedSuperjet (toPointSet Ω) (toPointFun u) z) :
    J.gradient (Fin.last d) - ∑ i : Fin d, J.hessian i.castSucc i.castSucc
      + F ((spaceTimeEquiv d).symm z) (u ((spaceTimeEquiv d).symm z)) ≤ 0 := by
  have h := hu.toViscositySubsolution.closedSuperjet_le_of_operatorContinuous
    (parabolicOp_operatorContinuous hF) hJ
  rw [parabolicOp_apply] at h
  change _ + _ + F _ (u ((spaceTimeEquiv d).symm z)) ≤ 0 at h
  linarith

/-- Supersolution mirror: the closed-subjet inequality. -/
theorem IsViscSuperOn.closedSubjet_nonneg {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsViscSuperOn Ω F u)
    (hF : Continuous fun q : (E d × ℝ) × ℝ ↦ F q.1 q.2) {z : ViscositySolns.Point (d + 1)}
    {J : ViscositySolns.Jet (d + 1)}
    (hJ : J ∈ ViscositySolns.ClosedSubjet (toPointSet Ω) (toPointFun u) z) :
    0 ≤ J.gradient (Fin.last d) - ∑ i : Fin d, J.hessian i.castSucc i.castSucc
      + F ((spaceTimeEquiv d).symm z) (u ((spaceTimeEquiv d).symm z)) := by
  have h := hu.toViscositySupersolution.closedSubjet_nonneg_of_operatorContinuous
    (parabolicOp_operatorContinuous hF) hJ
  rw [parabolicOp_apply] at h
  change 0 ≤ _ + _ + F _ (u ((spaceTimeEquiv d).symm z)) at h
  linarith

end ParabolicBasic
