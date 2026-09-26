import Challenge.Setting

/-!
# Challenge vocabulary: the parabolic distance and parabolic Hölder continuity

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Setting`). It
restates, token for token, `pdist` and `HolderOnPar` (`ParabolicBasic/Defs/Holder.lean`) and
`LocHolderOnPar` (`ParabolicBasic/Schauder/Holder.lean`):

* `pdist (x, t) (y, s) = max ‖x - y‖ √|t - s|`, the parabolic distance, a plain function
  (`E d × ℝ` keeps Mathlib's sup metric);
* `HolderOnPar C α φ S`: `|φ p - φ q| ≤ C * pdist p q ^ α` for `p, q ∈ S`;
* `LocHolderOnPar α φ Ω`: `φ` is `HolderOnPar` with some constant on every compact `K ⊆ Ω`.

None of these definitions creates auxiliary proofs, so they share one file although the library
splits them over two.
-/

namespace ParabolicBasic

variable {d : ℕ}

/-- The parabolic distance `max ‖x - y‖ (√|t - s|)` between `p = (x, t)` and `q = (y, s)`.
A plain function: `E d × ℝ` does not carry it as a metric. -/
noncomputable def pdist (p q : E d × ℝ) : ℝ := max ‖p.1 - q.1‖ (Real.sqrt |p.2 - q.2|)

/-- `φ` is parabolically `α`-Hölder on `S` with constant `C`:
`|φ p - φ q| ≤ C * pdist p q ^ α` for all `p, q ∈ S` (`^` is `Real.rpow`). -/
def HolderOnPar (C α : ℝ) (φ : E d × ℝ → ℝ) (S : Set (E d × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, |φ p - φ q| ≤ C * pdist p q ^ α

/-- `φ` is locally parabolically `α`-Hölder on `Ω`: `HolderOnPar` on every compact subset. -/
def LocHolderOnPar (α : ℝ) (φ : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → ∃ C, HolderOnPar C α φ K

end ParabolicBasic
