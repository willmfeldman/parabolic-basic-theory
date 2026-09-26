import Mathlib

/-!
# Challenge vocabulary: the ambient space and space-time differential operators

Part of the trusted statement surface; imports `Mathlib` only. Restates, token for token, the
definitions of the library file `ParabolicBasic/Basic/Setting.lean` that the challenge uses.

* `E d` is `EuclideanSpace ℝ (Fin d)`; space-time points are `p : E d × ℝ`, with `p.1` the space
  and `p.2` the time variable.
* `gradₓ`, `lapₓ`, `dₜ` are Mathlib's `gradient`, `InnerProductSpace.laplacian` (`Δ`) and `deriv`,
  applied to the time slice (resp. the space slice) through `p`.
* `HasC2Boundary` is not used by any challenge statement. It is restated only so that the
  auxiliary proof that `gradₓ` reuses from it carries the library's name, which Comparator checks.
-/

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

/-- Spatial gradient `∇ₓφ(x,t)` of a space-time function (gradient of the time slice). -/
noncomputable def gradₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : E d :=
  ∇ (fun y ↦ φ (y, p.2)) p.1

/-- Spatial Laplacian `Δₓφ(x,t)` of a space-time function (Laplacian of the time slice). -/
noncomputable def lapₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  Δ (fun y ↦ φ (y, p.2)) p.1

/-- Time derivative `∂ₜφ(x,t)` of a space-time function (two-sided `deriv` of the space slice). -/
noncomputable def dₜ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  deriv (fun s ↦ φ (p.1, s)) p.2

end ParabolicBasic
