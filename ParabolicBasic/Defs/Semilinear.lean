/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hypotheses on the nonlinearity `f`

The bundled hypotheses on the zero-order term `f : E d → ℝ → ℝ` of `∂ₜu = Δₓu - f(x, u)` used by
internal statements. The main theorems (`ParabolicBasic.MainTheorems`) spell these hypotheses out
instead.

* `holder_x`: `f` is Hölder in `x` on `S`, **uniformly in `z`**;
* `lip_z`: `f` is Lipschitz in `z`, uniformly in `x ∈ S`;
* `bounded`: `f` is bounded on `S × ℝ`.

This is *less* general than the "continuous in `x` uniformly in `z`" condition of
Crandall–Ishii–Lions (User's guide, §3, §8), so no statement made with it is stronger than the
literature. Hölder regularity in `x` is what the Schauder theory needs, and the Hölder–McShane
extension makes such an `f` global, as `ViscositySolns` requires (its `Proper`/`OperatorContinuous`
conditions are global). Comparison uses only `holder_x` and `lip_z`. The API (`SemilinearHyp.zero`,
`.mono`, the global extension) is in `ParabolicBasic.Comparison.SemilinearHyp`.
-/

@[expose] public section

namespace ParabolicBasic

variable {d : ℕ}

/-- The standing hypotheses on the nonlinearity `f` on a set `S ⊆ ℝᵈ` (usually `S = closure U`):
Hölder in `x` uniformly in `z`, Lipschitz in `z` uniformly in `x`, and bounded. -/
structure SemilinearHyp (f : E d → ℝ → ℝ) (S : Set (E d)) : Prop where
  /-- `f` is `α`-Hölder in `x ∈ S`, uniformly in `z`. -/
  holder_x : ∃ K α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ z, |f x z - f y z| ≤ K * dist x y ^ α
  /-- `f` is Lipschitz in `z`, uniformly in `x ∈ S`. -/
  lip_z : ∃ L : ℝ, ∀ x ∈ S, ∀ z w, |f x z - f x w| ≤ L * |z - w|
  /-- `f` is bounded on `S × ℝ`. -/
  bounded : ∃ M : ℝ, ∀ x ∈ S, ∀ z, |f x z| ≤ M

end ParabolicBasic
