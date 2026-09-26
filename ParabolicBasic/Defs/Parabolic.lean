/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Basic.Setting

/-!
# Parabolic cylinders and parabolic boundaries

`E d × ℝ` carries the sup metric, so `Metric.ball (x, t) r = ball x r ×ˢ Ioo (t - r) (t + r)` is
*not* a parabolic cylinder; every cylinder here is written as a product of sets.
-/

@[expose] public section

open Set Metric

namespace ParabolicBasic

variable {d : ℕ}

/-- The cylinder `V × (a, b]`. -/
def cyl (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) := V ×ˢ Ioc a b

/-- The parabolic boundary `∂_P(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])`.
For `d = 0`, `frontier V = ∅`, so only the initial face remains. -/
def parBdry (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) :=
  (closure V ×ˢ {a}) ∪ (frontier V ×ˢ Icc a b)

/-- The backward parabolic cylinder `Q_r(x, t) = B_r(x) × (t - r², t]`. -/
def parCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := ball x r ×ˢ Ioc (t - r ^ 2) t

/-- The centred (open) parabolic cylinder `B_r(x) × (t - r², t + r²)`, used for the
Schauder theory: `(x, t)` is an interior point, so no one-sided time expansion at a top face is
needed. -/
def cCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := ball x r ×ˢ Ioo (t - r ^ 2) (t + r ^ 2)

end ParabolicBasic
