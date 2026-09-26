/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.LinearAlgebra.Trace

/-!
# The setting: ambient space and space-time differential operators

`Δ` is `InnerProductSpace.laplacian` (in terms of iterated derivatives:
`InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`), and `∇` is `gradient`.

## Conventions

* All functions are total (`E d → ℝ`, `E d × ℝ → ℝ`); every predicate restricts to its domain
  explicitly, and values outside the domain are never used.
* Space-time points are `p : E d × ℝ`, with `p.1` the space and `p.2` the time variable.
* `E d × ℝ` carries the product (**sup**) metric: `Metric.ball` on space-time is *not* a parabolic
  cylinder. Cylinders are always products of sets (`ParabolicBasic.Defs.Parabolic`).
* Every statement of the library holds for all `d`, including `d = 0` (`E 0` is a point).
-/

@[expose] public section

open Set Filter Topology
open scoped Gradient Laplacian ContDiff

namespace ParabolicBasic

/-- The ambient Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- **`C²` boundary**: `U` has `C²` boundary, encoded by a global `C²` defining
function: `U = {ρ < 0}` with `∇ρ ≠ 0` on `∂U`. -/
def HasC2Boundary (U : Set (E d)) : Prop :=
  ∃ ρ : E d → ℝ, ContDiff ℝ 2 ρ ∧ U = {x | ρ x < 0} ∧ ∀ x ∈ frontier U, ∇ ρ x ≠ 0

/-! ### Differential operators -/

/-- Spatial gradient `∇ₓφ(x,t)` of a space-time function (gradient of the time slice). -/
noncomputable def gradₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : E d :=
  ∇ (fun y ↦ φ (y, p.2)) p.1

/-- Spatial Laplacian `Δₓφ(x,t)` of a space-time function (Laplacian of the time slice). -/
noncomputable def lapₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  Δ (fun y ↦ φ (y, p.2)) p.1

/-- Time derivative `∂ₜφ(x,t)` of a space-time function (two-sided `deriv` of the space slice). -/
noncomputable def dₜ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  deriv (fun s ↦ φ (p.1, s)) p.2

/-- Spatial Hessian `D²ₓφ(x,t)` of a space-time function, as the second iterated Fréchet
derivative of the time slice. (This is the object appearing in the fourth conjunct of
`IsSemilinearSolOn`, which is written out there, not through `hessₓ`.) -/
noncomputable def hessₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E d) ℝ :=
  iteratedFDeriv ℝ 2 (fun y ↦ φ (y, p.2)) p.1

end ParabolicBasic
