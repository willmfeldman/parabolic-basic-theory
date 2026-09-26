import Mathlib

/-!
# Challenge vocabulary: touching from above and below

Part of the trusted statement surface; imports `Mathlib` only. Restates the library file
`ParabolicBasic/Defs/Touching.lean`. Touching is non-strict and local relative to the set `S`
(`𝓝[S] x`); when `S` is open this is `𝓝 x`.
-/

open Set Filter Topology

namespace ParabolicBasic

variable {X : Type*} [TopologicalSpace X]

/-- `φ` touches `u` from below in `S` at `x`: `x ∈ S`, `φ x = u x`, and `φ ≤ u` on a relative
neighbourhood of `x` in `S`. -/
def TouchesBelow (φ u : X → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, φ y ≤ u y

/-- `φ` touches `u` from above in `S` at `x`: `x ∈ S`, `φ x = u x`, and `u ≤ φ` on a relative
neighbourhood of `x` in `S`. -/
def TouchesAbove (φ u : X → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, u y ≤ φ y

end ParabolicBasic
