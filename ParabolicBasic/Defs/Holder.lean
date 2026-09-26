/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parabolic distance and parabolic Hölder continuity

The parabolic distance
`pdist p q = max ‖p.1 - q.1‖ (√|p.2 - q.2|)` is a plain function, with **no** metric instance
(`E d × ℝ` keeps its sup metric), and parabolic Hölder continuity on a set is the predicate
`HolderOnPar`. The theory (triangle inequality, `mem_cCyl_iff`, the local predicates
`LocHolderOnPar`/`LocHolder`, the Hölder algebra) is in `ParabolicBasic.Schauder.Holder`.
-/

@[expose] public section

namespace ParabolicBasic

variable {d : ℕ}

/-- The parabolic distance `max ‖x - y‖ (√|t - s|)` between `p = (x, t)` and `q = (y, s)`.
A plain function: `E d × ℝ` does not carry it as a metric. -/
noncomputable def pdist (p q : E d × ℝ) : ℝ := max ‖p.1 - q.1‖ (Real.sqrt |p.2 - q.2|)

/-- `φ` is parabolically `α`-Hölder on `S` with constant `C`:
`|φ p - φ q| ≤ C * pdist p q ^ α` for all `p, q ∈ S` (`^` is `Real.rpow`). -/
def HolderOnPar (C α : ℝ) (φ : E d × ℝ → ℝ) (S : Set (E d × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, |φ p - φ q| ≤ C * pdist p q ^ α

end ParabolicBasic
