module

public import Vocabulary.Setting
public import Vocabulary.Touching

@[expose] public section

/-!
# Challenge vocabulary: viscosity sub- and supersolutions

Part of the trusted statement surface; imports `Mathlib` only (through `Vocabulary.Setting` and
`Vocabulary.Touching`). Restates definitions of the library file
`ParabolicBasic/Defs/Viscosity.lean`, in the library's order. (The library's `IsViscSolOn`, which
sits between `IsViscSuperOn` and `IsHeatSolOn`, is not used and creates no auxiliary proofs, so it
is omitted.)

* **Standard notion** `IsViscSubOn Ω F u`, `IsViscSuperOn Ω F u`: viscosity sub/supersolutions of
  `dₜu - lapₓu + F p (u p) ≤ 0` (resp. `≥ 0`) on `Ω ⊆ E d × ℝ`, with global `C²` test functions
  touching relative to `Ω`. [CIL, §8] The past-touching definitions below also reuse an
  auxiliary proof from `IsViscSubOn`; Comparator checks that it carries the library's name.
* **Heat equation with source** `IsHeatSolOn Ω H u`: a viscosity solution of `dₜu - lapₓu = H`
  on `Ω`, i.e. both of the above with the zero-order term `fun p _ ↦ -H p`.
* **Past-touching notion** `IsSemilinearViscSubOn U f I u`, `IsSemilinearViscSuperOn U f I u` for
  `∂ₜu = Δₓu - f(x, u)` on `U × I`: continuous functions, global `C²` test functions touching
  relative to the parabolic past `(U × I) ∩ {q | q.2 ≤ p.2}`. [CIL, §8]
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace ParabolicBasic

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

/-- Viscosity solution of the linear heat equation with source, `dₜu − lapₓu = H` on `Ω`:
a viscosity subsolution and supersolution with the zero-order term `fun p _ ↦ -H p`. -/
def IsHeatSolOn (Ω : Set (E d × ℝ)) (H : E d × ℝ → ℝ) (u : E d × ℝ → ℝ) : Prop :=
  IsViscSubOn Ω (fun p _ ↦ -H p) u ∧ IsViscSuperOn Ω (fun p _ ↦ -H p) u

/-- Parabolic continuous viscosity subsolution of `∂ₜu = Δₓu - f(x, u)` in `U × I`, with touching
relative to the parabolic past `(U × I) ∩ {s ≤ t}`: `u` is continuous on `U × I`, and whenever a
global `C²` function `ψ` touches `u` from above at `p ∈ U × I` relative to the past,
`dₜ ψ p - lapₓ ψ p ≤ -f(p.1, u p)`. -/
def IsSemilinearViscSubOn (U : Set (E d)) (f : E d → ℝ → ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ U ×ˢ I,
    TouchesAbove ψ u ((U ×ˢ I) ∩ {q | q.2 ≤ p.2}) p →
      dₜ ψ p - lapₓ ψ p ≤ -(f p.1 (u p))

/-- Parabolic continuous viscosity supersolution of `∂ₜu = Δₓu - f(x, u)` in `U × I`, with
touching relative to the parabolic past: whenever a global `C²` function `ψ` touches `u` from
below at `p ∈ U × I` relative to `(U × I) ∩ {s ≤ t}`, `-f(p.1, u p) ≤ dₜ ψ p - lapₓ ψ p`. -/
def IsSemilinearViscSuperOn (U : Set (E d)) (f : E d → ℝ → ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ U ×ˢ I,
    TouchesBelow ψ u ((U ×ˢ I) ∩ {q | q.2 ≤ p.2}) p →
      -(f p.1 (u p)) ≤ dₜ ψ p - lapₓ ψ p

end ParabolicBasic
