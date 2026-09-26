import Challenge.Setting

/-!
# Challenge vocabulary: touching and viscosity sub- and supersolutions

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Setting`). It
restates, token for token, the definitions `TouchesBelow`, `TouchesAbove`
(`ParabolicBasic/Defs/Touching.lean`) and `IsViscSubOn`, `IsViscSuperOn`
(`ParabolicBasic/Defs/Viscosity.lean`), in the library's order.

These are the standard viscosity notions [Crandall–Ishii–Lions, *User's guide to viscosity
solutions*, Bull. AMS 27 (1992), §8] for `dₜu - lapₓu + F p (u p) = 0` on a set
`Ω ⊆ ℝᵈ × ℝ`: semicontinuity on `Ω`, global `C²` test functions, and non-strict touching that is
local relative to `Ω` (for open `Ω`, an ordinary neighbourhood of the contact point).

This file is separate from `Challenge.Setting` because Comparator checks the names of the
auxiliary proofs Lean creates inside definitions, and Lean shares those only within a file; the
auxiliary proof for the numeral `2` in `IsViscSubOn` (reused by `IsViscSuperOn`) must be created
here, not reused from `HasC2Boundary`. The two touching definitions create no auxiliary proofs,
so they share this file.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

section Touching

variable {X : Type*} [TopologicalSpace X]

/-- `φ` touches `u` from below in `S` at `x`: `x ∈ S`, `φ x = u x`, and `φ ≤ u` on a relative
neighbourhood of `x` in `S`. -/
def TouchesBelow (φ u : X → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, φ y ≤ u y

/-- `φ` touches `u` from above in `S` at `x`: `x ∈ S`, `φ x = u x`, and `u ≤ φ` on a relative
neighbourhood of `x` in `S`. -/
def TouchesAbove (φ u : X → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, u y ≤ φ y

end Touching

variable {d : ℕ}

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

end ParabolicBasic
