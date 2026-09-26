/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import ParabolicBasic.Defs.Touching
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Viscosity sub- and supersolutions

Two notions.

* **Standard notion** `IsViscSubOn Ω F u`, `IsViscSuperOn Ω F u`, `IsViscSolOn Ω F u`:
  viscosity sub/supersolutions of `dₜu - lapₓu + F p (u p) ≤ 0` (resp. `≥ 0`) on a set
  `Ω ⊆ E d × ℝ` (intended open). The function is upper (resp. lower) semicontinuous on `Ω` (not
  continuous: Perron needs USC/LSC); the test functions are global `C²` functions `ψ`; touching is
  two-sided and local, relative to `Ω` (`𝓝[Ω] p`, which is `𝓝 p` for open `Ω`).
  [CIL] Crandall–Ishii–Lions, *User's guide to viscosity solutions*, Bull. AMS 27 (1992), §8.
* **Past-touching notion** `IsSemilinearViscSubOn U f I u`, `IsSemilinearViscSuperOn U f I u`
  for `∂ₜu = Δₓu - f(x, u)` on `U × I`: continuous functions, global `C²` tests touching relative to
  the parabolic past `(U × I) ∩ {q | q.2 ≤ p.2}`.

The past-touching notion is *stronger* than the standard one: it implies it
(`IsSemilinearViscSubOn.isViscSubOn`).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

variable {d : ℕ}

/-! ### The standard notion -/

/-- Standard viscosity subsolution of `dₜu - lapₓu + F p (u p) ≤ 0` on `Ω`:
`u` is upper semicontinuous on `Ω`, and whenever a global `C²` function `ψ` touches `u` from above
at `p ∈ Ω` (relative to `Ω`), `dₜ ψ p - lapₓ ψ p + F p (u p) ≤ 0`. -/
def IsViscSubOn (Ω : Set (E d × ℝ)) (F : E d × ℝ → ℝ → ℝ) (u : E d × ℝ → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ Ω,
    TouchesAbove ψ u Ω p → dₜ ψ p - lapₓ ψ p + F p (u p) ≤ 0

/-- Standard viscosity supersolution of `dₜu - lapₓu + F p (u p) ≥ 0` on `Ω`:
`u` is lower semicontinuous on `Ω`, and whenever a global `C²` function `ψ` touches `u` from below
at `p ∈ Ω` (relative to `Ω`), `0 ≤ dₜ ψ p - lapₓ ψ p + F p (u p)`. -/
def IsViscSuperOn (Ω : Set (E d × ℝ)) (F : E d × ℝ → ℝ → ℝ) (u : E d × ℝ → ℝ) : Prop :=
  LowerSemicontinuousOn u Ω ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ Ω,
    TouchesBelow ψ u Ω p → 0 ≤ dₜ ψ p - lapₓ ψ p + F p (u p)

/-- Standard viscosity solution of `dₜu - lapₓu + F p (u p) = 0` on `Ω`: both a
subsolution and a supersolution (so `u` is continuous on `Ω`). -/
def IsViscSolOn (Ω : Set (E d × ℝ)) (F : E d × ℝ → ℝ → ℝ) (u : E d × ℝ → ℝ) : Prop :=
  IsViscSubOn Ω F u ∧ IsViscSuperOn Ω F u

/-- Viscosity solution of the linear heat equation with source, `dₜu − lapₓu = H` on `Ω`:
`IsViscSolOn` with the zero-order term `fun p _ ↦ -H p`. Used by the Schauder theory. -/
def IsHeatSolOn (Ω : Set (E d × ℝ)) (H : E d × ℝ → ℝ) (u : E d × ℝ → ℝ) : Prop :=
  IsViscSubOn Ω (fun p _ ↦ -H p) u ∧ IsViscSuperOn Ω (fun p _ ↦ -H p) u

/-! ### The past-touching notion -/

/-- Parabolic continuous viscosity subsolution of `∂ₜu = Δₓu - f(x, u)` in `U × I`, with touching
relative to the parabolic past `(U × I) ∩ {s ≤ t}`: `u` is continuous on `U × I`, and whenever a
global `C²` function `ψ` touches `u` from above at `p ∈ U × I` relative to the past,
`dₜ ψ p - lapₓ ψ p ≤ -f(p.1, u p)`. -/
def IsSemilinearViscSubOn (U : Set (E d)) (f : E d → ℝ → ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ U ×ˢ I,
    TouchesAbove ψ u ((U ×ˢ I) ∩ {q | q.2 ≤ p.2}) p →
      dₜ ψ p - lapₓ ψ p ≤ -(f p.1 (u p))

/-- Parabolic continuous viscosity supersolution of `∂ₜu = Δₓu - f(x, u)` in `U × I`, with
touching relative to the parabolic past: whenever a global `C²` function `ψ` touches `u` from
below at `p ∈ U × I` relative to `(U × I) ∩ {s ≤ t}`, `-f(p.1, u p) ≤ dₜ ψ p - lapₓ ψ p`. -/
def IsSemilinearViscSuperOn (U : Set (E d)) (f : E d → ℝ → ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ U ×ˢ I,
    TouchesBelow ψ u ((U ×ˢ I) ∩ {q | q.2 ≤ p.2}) p →
      -(f p.1 (u p)) ≤ dₜ ψ p - lapₓ ψ p

end ParabolicBasic
