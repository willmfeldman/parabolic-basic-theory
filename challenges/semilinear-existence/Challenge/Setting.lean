import Mathlib

/-!
# Challenge vocabulary: the ambient space and the space-time differential operators

Part of the trusted statement surface; imports `Mathlib` only. It restates, token for token,
the definitions of `ParabolicBasic/Basic/Setting.lean`:

* `E d` is `EuclideanSpace ℝ (Fin d)`, i.e. `ℝᵈ`; space-time points are `p : E d × ℝ`, with
  `p.1` the space and `p.2` the time variable;
* `HasC2Boundary U`: `U = {ρ < 0}` for a global `C²` function `ρ` with `∇ρ ≠ 0` on `∂U`;
* `gradₓ`, `lapₓ`, `dₜ`: the spatial gradient and spatial Laplacian of the time slice
  `y ↦ φ (y, t)` (Mathlib's `gradient` and `InnerProductSpace.laplacian`), and the two-sided
  time derivative (`deriv`) of the space slice `s ↦ φ (x, s)`.

This vocabulary lives in its own file because Comparator checks that each restated definition is
the library's definition, including the names of the small auxiliary proofs Lean creates inside
definitions (such as the instance proof for the numeral `2` in `HasC2Boundary`, which `gradₓ`
reuses). Lean shares those auxiliary proofs only within one file, so the file boundaries follow
the library's. `HasC2Boundary` is kept here even where a challenge statement does not use it,
because `gradₓ` refers to one of its auxiliary proofs.
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
