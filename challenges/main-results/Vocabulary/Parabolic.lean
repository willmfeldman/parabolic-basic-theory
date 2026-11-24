module

public import Vocabulary.Setting

@[expose] public section

/-!
# Challenge vocabulary: the parabolic boundary

Part of the trusted statement surface; imports `Mathlib` only (through `Vocabulary.Setting`).
Restates `parBdry` from the library file `ParabolicBasic/Defs/Parabolic.lean`.
-/

open Set Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- The parabolic boundary `∂_P(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])`.
For `d = 0`, `frontier V = ∅`, so only the initial face remains. -/
def parBdry (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) :=
  (closure V ×ˢ {a}) ∪ (frontier V ×ˢ Icc a b)

end ParabolicBasic
