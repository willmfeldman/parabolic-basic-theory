/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import ParabolicBasic.Defs.Touching
public import ViscositySolns.Foundation
public import ViscositySolns.TestFunctions.Smooth
public import ViscositySolns.Comparison.ProperComparison.Core

/-!
# Transport `E d × ℝ ≃L[ℝ] Point (d + 1)`

The space-time `E d × ℝ` of this library is identified with `ViscositySolns`'
`Point (d + 1) = Fin (d + 1) → ℝ`: the space coordinates go to the indices `Fin.castSucc i`, and
time goes to the last index `Fin.last d`.

* `spaceTimeEquiv d : E d × ℝ ≃L[ℝ] Point (d + 1)`, `(x, t) ↦ Fin.snoc (x₀, …, x_{d-1}) t`,
  with `@[simp]` apply / symm-apply / coordinate lemmas. Later proofs never unfold it.
* `toPointSet Ω := e.symm ⁻¹' Ω` and `toPointFun u := u ∘ e.symm` (membership and evaluation are
  definitional).
* Transfer of openness, closure, frontier, compactness, local compactness, semicontinuity and
  touching (touching in `ViscositySolns` is *up to a constant*, `TouchesAboveOn`).

Norms: `Point (d + 1)` carries the sup norm of the Pi type, and `E d × ℝ` the sup of the
Euclidean norm on `E d` and `|t|`. They are equivalent, not equal; moduli are always stated in the
`E d × ℝ` distance.
-/

@[expose] public section

open Set Filter Topology

namespace ParabolicBasic

variable {d : ℕ}

/-! ### The linear equivalence -/

/-- `(y, t) ↦ Fin.snoc y t` as a linear equivalence `(Fin d → ℝ) × ℝ ≃ₗ[ℝ] Fin (d + 1) → ℝ`
(time at the last index). -/
def snocLinearEquiv (d : ℕ) : ((Fin d → ℝ) × ℝ) ≃ₗ[ℝ] ViscositySolns.Point (d + 1) where
  toFun p := Fin.snoc (α := fun _ ↦ ℝ) p.1 p.2
  invFun z := (Fin.init z, z (Fin.last d))
  map_add' p q := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' c p := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  left_inv p := by simp
  right_inv z := by simp

/-- The space-time equivalence `E d × ℝ ≃L[ℝ] Point (d + 1)`: space in the first `d`
coordinates (`Fin.castSucc`), time at `Fin.last d`. -/
noncomputable def spaceTimeEquiv (d : ℕ) : (E d × ℝ) ≃L[ℝ] ViscositySolns.Point (d + 1) :=
  ((EuclideanSpace.equiv (Fin d) ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
    (snocLinearEquiv d).toContinuousLinearEquiv

/-- Simp normal form of `EuclideanSpace.equiv` (a `WithLp` coercion). -/
@[simp]
theorem euclideanSpace_equiv_apply (x : E d) : EuclideanSpace.equiv (Fin d) ℝ x = x.ofLp :=
  rfl

/-- Simp normal form of `(EuclideanSpace.equiv).symm` (a `WithLp` coercion). -/
@[simp]
theorem euclideanSpace_equiv_symm_apply (y : Fin d → ℝ) :
    (EuclideanSpace.equiv (Fin d) ℝ).symm y = WithLp.toLp 2 y :=
  rfl

@[simp]
theorem spaceTimeEquiv_apply (p : E d × ℝ) :
    spaceTimeEquiv d p = Fin.snoc (α := fun _ ↦ ℝ) (EuclideanSpace.equiv (Fin d) ℝ p.1) p.2 :=
  rfl

@[simp]
theorem spaceTimeEquiv_symm_apply (z : ViscositySolns.Point (d + 1)) :
    (spaceTimeEquiv d).symm z =
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (Fin.init z), z (Fin.last d)) :=
  rfl

@[simp]
theorem spaceTimeEquiv_apply_castSucc (p : E d × ℝ) (i : Fin d) :
    spaceTimeEquiv d p i.castSucc = p.1 i := by
  simp

@[simp]
theorem spaceTimeEquiv_apply_last (p : E d × ℝ) : spaceTimeEquiv d p (Fin.last d) = p.2 := by
  simp

@[simp]
theorem spaceTimeEquiv_symm_apply_fst_apply (z : ViscositySolns.Point (d + 1)) (i : Fin d) :
    ((spaceTimeEquiv d).symm z).1 i = z i.castSucc := by
  simp [Fin.init]

@[simp]
theorem spaceTimeEquiv_symm_apply_snd (z : ViscositySolns.Point (d + 1)) :
    ((spaceTimeEquiv d).symm z).2 = z (Fin.last d) :=
  rfl

/-- `ViscositySolns`' `coordinateVector i` is `Pi.single i 1`. -/
theorem coordinateVector_eq_single {n : ℕ} (i : Fin n) :
    ViscositySolns.coordinateVector i = Pi.single i 1 := by
  funext j
  simp [ViscositySolns.coordinateVector, Pi.single_apply, eq_comm]

/-- `e (bᵢ, 0) = ε_{castSucc i}`. -/
theorem spaceTimeEquiv_space_basis (i : Fin d) :
    spaceTimeEquiv d (EuclideanSpace.single i 1, 0) =
      ViscositySolns.coordinateVector i.castSucc := by
  rw [coordinateVector_eq_single]
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp [Fin.castSucc_ne_last]
  · simp [Pi.single_apply, Fin.castSucc_inj]

/-- `e (0, 1) = ε_t`. -/
theorem spaceTimeEquiv_time :
    spaceTimeEquiv d (0, 1) = ViscositySolns.coordinateVector (Fin.last d) := by
  rw [coordinateVector_eq_single]
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp
  · simp [Fin.castSucc_ne_last]

/-- `d = 0`: the only coordinate is time. -/
example (x : E 0) (t : ℝ) : spaceTimeEquiv 0 (x, t) 0 = t := spaceTimeEquiv_apply_last (x, t)

/-! ### Sets and functions -/

/-- A space-time set, transported to `Point (d + 1)`. -/
abbrev toPointSet (Ω : Set (E d × ℝ)) : Set (ViscositySolns.Point (d + 1)) :=
  (spaceTimeEquiv d).symm ⁻¹' Ω

/-- A space-time function, transported to `Point (d + 1)`. -/
noncomputable abbrev toPointFun (u : E d × ℝ → ℝ) : ViscositySolns.Point (d + 1) → ℝ :=
  u ∘ (spaceTimeEquiv d).symm

theorem mem_toPointSet {Ω : Set (E d × ℝ)} {z : ViscositySolns.Point (d + 1)} :
    z ∈ toPointSet Ω ↔ (spaceTimeEquiv d).symm z ∈ Ω :=
  Iff.rfl

@[simp]
theorem spaceTimeEquiv_mem_toPointSet {Ω : Set (E d × ℝ)} {p : E d × ℝ} :
    spaceTimeEquiv d p ∈ toPointSet Ω ↔ p ∈ Ω := by
  simp only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply]

@[simp]
theorem toPointFun_apply (u : E d × ℝ → ℝ) (z : ViscositySolns.Point (d + 1)) :
    toPointFun u z = u ((spaceTimeEquiv d).symm z) :=
  rfl

@[simp]
theorem toPointFun_spaceTimeEquiv (u : E d × ℝ → ℝ) (p : E d × ℝ) :
    toPointFun u (spaceTimeEquiv d p) = u p := by
  simp only [toPointFun, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem toPointSet_eq_image (Ω : Set (E d × ℝ)) : toPointSet Ω = spaceTimeEquiv d '' Ω :=
  ((spaceTimeEquiv d).toEquiv.image_eq_preimage_symm Ω).symm

/-! ### Topology -/

theorem isOpen_toPointSet_iff {Ω : Set (E d × ℝ)} : IsOpen (toPointSet Ω) ↔ IsOpen Ω :=
  (spaceTimeEquiv d).symm.toHomeomorph.isOpen_preimage

theorem isOpen_toPointSet {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) : IsOpen (toPointSet Ω) :=
  isOpen_toPointSet_iff.2 hΩ

theorem isClosed_toPointSet_iff {Ω : Set (E d × ℝ)} : IsClosed (toPointSet Ω) ↔ IsClosed Ω :=
  (spaceTimeEquiv d).symm.toHomeomorph.isClosed_preimage

theorem closure_toPointSet (Ω : Set (E d × ℝ)) : closure (toPointSet Ω) = toPointSet (closure Ω) :=
  ((spaceTimeEquiv d).symm.toHomeomorph.preimage_closure Ω).symm

theorem frontier_toPointSet (Ω : Set (E d × ℝ)) :
    frontier (toPointSet Ω) = toPointSet (frontier Ω) :=
  ((spaceTimeEquiv d).symm.toHomeomorph.preimage_frontier Ω).symm

theorem interior_toPointSet (Ω : Set (E d × ℝ)) :
    interior (toPointSet Ω) = toPointSet (interior Ω) :=
  ((spaceTimeEquiv d).symm.toHomeomorph.preimage_interior Ω).symm

theorem isCompact_toPointSet_iff {K : Set (E d × ℝ)} : IsCompact (toPointSet K) ↔ IsCompact K :=
  (spaceTimeEquiv d).symm.toHomeomorph.isCompact_preimage

theorem isCompact_toPointSet {K : Set (E d × ℝ)} (hK : IsCompact K) : IsCompact (toPointSet K) :=
  isCompact_toPointSet_iff.2 hK

theorem toPointSet_nonempty_iff {Ω : Set (E d × ℝ)} : (toPointSet Ω).Nonempty ↔ Ω.Nonempty :=
  ⟨fun ⟨z, hz⟩ ↦ ⟨_, hz⟩, fun ⟨p, hp⟩ ↦ ⟨spaceTimeEquiv d p, by simpa using hp⟩⟩

theorem compactClosure_toPointSet {Ω : Set (E d × ℝ)} (h : IsCompact (closure Ω)) :
    ViscositySolns.CompactClosure (toPointSet Ω) := by
  rw [ViscositySolns.CompactClosure, closure_toPointSet]
  exact isCompact_toPointSet h

theorem locallyCompactSpace_toPointSet {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) :
    LocallyCompactSpace (toPointSet Ω) :=
  (isOpen_toPointSet hΩ).locallyCompactSpace

/-! ### Semicontinuity -/

theorem upperSemicontinuousOn_toPointFun_iff {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)} :
    UpperSemicontinuousOn (toPointFun u) (toPointSet S) ↔ UpperSemicontinuousOn u S := by
  constructor
  · intro h
    have := h.comp (spaceTimeEquiv d).continuous.continuousOn
      (fun p hp ↦ by simpa using hp : MapsTo (spaceTimeEquiv d) S (toPointSet S))
    simpa [Function.comp_def] using this
  · intro h
    exact h.comp (spaceTimeEquiv d).symm.continuous.continuousOn (fun _ hz ↦ hz)

theorem lowerSemicontinuousOn_toPointFun_iff {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)} :
    LowerSemicontinuousOn (toPointFun u) (toPointSet S) ↔ LowerSemicontinuousOn u S := by
  constructor
  · intro h
    have := h.comp (spaceTimeEquiv d).continuous.continuousOn
      (fun p hp ↦ by simpa using hp : MapsTo (spaceTimeEquiv d) S (toPointSet S))
    simpa [Function.comp_def] using this
  · intro h
    exact h.comp (spaceTimeEquiv d).symm.continuous.continuousOn (fun _ hz ↦ hz)

theorem continuousOn_toPointFun_iff {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)} :
    ContinuousOn (toPointFun u) (toPointSet S) ↔ ContinuousOn u S := by
  constructor
  · intro h
    have := h.comp (spaceTimeEquiv d).continuous.continuousOn
      (fun p hp ↦ by simpa using hp : MapsTo (spaceTimeEquiv d) S (toPointSet S))
    simpa [Function.comp_def] using this
  · intro h
    exact h.comp (spaceTimeEquiv d).symm.continuous.continuousOn (fun _ hz ↦ hz)

/-! ### Relative neighbourhoods and touching -/

/-- `e⁻¹` maps `𝓝[Ω♯] z` into `𝓝[Ω] (e⁻¹ z)`. -/
theorem tendsto_spaceTimeEquiv_symm_nhdsWithin (S : Set (E d × ℝ))
    (z : ViscositySolns.Point (d + 1)) :
    Tendsto (spaceTimeEquiv d).symm (𝓝[toPointSet S] z) (𝓝[S] ((spaceTimeEquiv d).symm z)) :=
  (spaceTimeEquiv d).symm.continuous.continuousWithinAt.tendsto_nhdsWithin (fun _ hz ↦ hz)

/-- `e` maps `𝓝[Ω] p` into `𝓝[Ω♯] (e p)`. -/
theorem tendsto_spaceTimeEquiv_nhdsWithin (S : Set (E d × ℝ)) (p : E d × ℝ) :
    Tendsto (spaceTimeEquiv d) (𝓝[S] p) (𝓝[toPointSet S] (spaceTimeEquiv d p)) :=
  (spaceTimeEquiv d).continuous.continuousWithinAt.tendsto_nhdsWithin
    (fun _ hp ↦ by simpa using hp)

/-- Our touching from above gives `ViscositySolns`' touching (up to a constant) of the transported
functions. -/
theorem TouchesAbove.toPoint {ψ u : E d × ℝ → ℝ} {S : Set (E d × ℝ)} {p : E d × ℝ}
    (h : TouchesAbove ψ u S p) :
    ViscositySolns.TouchesAboveOn (toPointSet S) (toPointFun u) (toPointFun ψ)
      (spaceTimeEquiv d p) := by
  obtain ⟨-, hψp, hev⟩ := h
  have := (tendsto_spaceTimeEquiv_symm_nhdsWithin S (spaceTimeEquiv d p)).eventually
    (by simpa using hev)
  refine this.mono fun z hz ↦ ?_
  simp only [toPointFun_apply, ContinuousLinearEquiv.symm_apply_apply, hψp, sub_self]
  linarith

/-- Our touching from below gives `ViscositySolns`' touching (up to a constant) of the transported
functions. -/
theorem TouchesBelow.toPoint {ψ u : E d × ℝ → ℝ} {S : Set (E d × ℝ)} {p : E d × ℝ}
    (h : TouchesBelow ψ u S p) :
    ViscositySolns.TouchesBelowOn (toPointSet S) (toPointFun u) (toPointFun ψ)
      (spaceTimeEquiv d p) := by
  obtain ⟨-, hψp, hev⟩ := h
  have := (tendsto_spaceTimeEquiv_symm_nhdsWithin S (spaceTimeEquiv d p)).eventually
    (by simpa using hev)
  refine this.mono fun z hz ↦ ?_
  simp only [toPointFun_apply, ContinuousLinearEquiv.symm_apply_apply, hψp, sub_self]
  linarith

/-- `ViscositySolns`' touching from above (up to a constant) gives our touching from above, after
adding the constant `u♯ z − φ z` to the pulled-back test function. -/
theorem touchesAbove_of_touchesAboveOn {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)}
    {φ : ViscositySolns.Point (d + 1) → ℝ} {z : ViscositySolns.Point (d + 1)}
    (h : ViscositySolns.TouchesAboveOn (toPointSet S) (toPointFun u) φ z)
    (hz : z ∈ toPointSet S) :
    TouchesAbove (fun q ↦ φ (spaceTimeEquiv d q) + (u ((spaceTimeEquiv d).symm z) - φ z)) u S
      ((spaceTimeEquiv d).symm z) := by
  refine ⟨hz, by simp, ?_⟩
  have ht := tendsto_spaceTimeEquiv_nhdsWithin S ((spaceTimeEquiv d).symm z)
  rw [ContinuousLinearEquiv.apply_symm_apply] at ht
  refine (ht.eventually h).mono fun q hq ↦ ?_
  have hq' : u q - φ (spaceTimeEquiv d q) ≤ u ((spaceTimeEquiv d).symm z) - φ z := by
    simpa only [toPointFun_apply, ContinuousLinearEquiv.symm_apply_apply] using hq
  dsimp only
  linarith

/-- `ViscositySolns`' touching from below (up to a constant) gives our touching from below, after
adding the constant `u♯ z − φ z` to the pulled-back test function. -/
theorem touchesBelow_of_touchesBelowOn {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)}
    {φ : ViscositySolns.Point (d + 1) → ℝ} {z : ViscositySolns.Point (d + 1)}
    (h : ViscositySolns.TouchesBelowOn (toPointSet S) (toPointFun u) φ z)
    (hz : z ∈ toPointSet S) :
    TouchesBelow (fun q ↦ φ (spaceTimeEquiv d q) + (u ((spaceTimeEquiv d).symm z) - φ z)) u S
      ((spaceTimeEquiv d).symm z) := by
  refine ⟨hz, by simp, ?_⟩
  have ht := tendsto_spaceTimeEquiv_nhdsWithin S ((spaceTimeEquiv d).symm z)
  rw [ContinuousLinearEquiv.apply_symm_apply] at ht
  refine (ht.eventually h).mono fun q hq ↦ ?_
  have hq' : u q - φ (spaceTimeEquiv d q) ≥ u ((spaceTimeEquiv d).symm z) - φ z := by
    simpa only [toPointFun_apply, ContinuousLinearEquiv.symm_apply_apply] using hq
  dsimp only
  linarith

end ParabolicBasic
