/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Topology.ContinuousOn
public import Mathlib.Basic.Real.Basic

/-!
# Touching from above and below

Touching is defined generically over a topological space `X`. It is non-strict and local
relative to the set `S` (`𝓝[S] x`); when `S` is open this is `𝓝 x`.
-/

@[expose] public section

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
