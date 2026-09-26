import Challenge.Classical
import Challenge.Viscosity
import Challenge.Holder

/-!
# Challenge: interior Schauder regularity for the heat equation

Trusted statement surface for the interior Schauder theorem for `∂ₜu - Δₓu = H`: a continuous
viscosity solution in `U × I`, with `H` locally parabolically `α`-Hölder, is classical
`C^{2,1}`, and `∂ₜu`, `∇ₓu` and `D²ₓu` are locally parabolically `α`-Hölder. This is the
interior `C^{2+α, 1+α/2}` regularity, obtained in the library by the `L^∞` Campanato iteration
of Caffarelli (1989), L. Wang (1992) and Safonov (1988): approximation in the sup norm by caloric
functions and caloric polynomials at every point and every scale (not Campanato's `L²` integral
method).

Hölder continuity is measured in the parabolic metric
`pdist (x, t) (y, s) = max ‖x - y‖ √|t - s|`, under which space scales like the square root of
time, matching the scaling `(x, t) ↦ (r x, r² t)` of the heat equation. It is a plain function:
`E d × ℝ` keeps Mathlib's sup metric.

All project vocabulary is restated inline in `Challenge/Setting.lean`,
`Challenge/Classical.lean`, `Challenge/Viscosity.lean` and `Challenge/Holder.lean`, which import
`Mathlib` only.
-/

open Set Filter Topology
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-- **Interior Schauder regularity.** Let `U ⊆ ℝᵈ` and `I ⊆ ℝ` be open and `α ∈ (0, 1)`. Let
`u` be continuous on `U × I` and a viscosity solution of `∂ₜu - Δₓu = H` there (`IsHeatSolOn`:
whenever a global `C²` function `ψ` touches `u` from above, resp. below, at `p`,
`∂ₜψ p - Δₓψ p ≤ H p`, resp. `≥ H p`), where `H` is continuous on `U × I` and locally
parabolically `α`-Hölder (`LocHolderOnPar α H`: on each compact `K ⊆ U × I`, for some `C`,
`|H p - H q| ≤ C * pdist p q ^ α` for `p, q ∈ K`, with
`pdist (x, t) (y, s) = max ‖x - y‖ √|t - s|`). Then:

* `u` is classical `C^{2,1}` on `U × I` (`IsC21On`: `u`, `∇ₓu`, `D²ₓu` and the two-sided `∂ₜu`
  exist and are continuous);
* `∂ₜu - Δₓu = H` pointwise on `U × I`;
* `∂ₜu`, every coordinate `∂ᵢu` of `∇ₓu`, and every spatial second derivative
  `∂ᵢ∂ⱼu = D²ₓu (eᵢ, eⱼ)` (written with `iteratedFDeriv ℝ 2` of the time slice applied to the
  standard basis vectors `EuclideanSpace.single i 1`, `EuclideanSpace.single j 1`) are locally
  parabolically `α`-Hölder on `U × I`.

This is the interior `C^{2+α, 1+α/2}` regularity in qualitative form: a Hölder constant exists on
each compact subset, with no explicit dependence on the data stated. The gradient is asserted to
be parabolically `α`-Hölder; the sharper time exponent `(1 + α)/2` for `∇ₓu` that is part of the
full `C^{2+α, 1+α/2}` norm is not part of the statement. The hypothesis is a viscosity solution,
which is weaker than a classical one. Degenerate cases: if `U` or `I` is empty the conclusion is
trivial; the endpoint exponents `α = 0` and `α = 1` are excluded. -/
theorem challenge_schauder_interior {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {u H : E d × ℝ → ℝ}
    (hu : ContinuousOn u (U ×ˢ I)) (hsol : IsHeatSolOn (U ×ˢ I) H u)
    (hH : ContinuousOn H (U ×ˢ I)) (hHα : LocHolderOnPar α H (U ×ˢ I)) :
    IsC21On U I u ∧ (∀ p ∈ U ×ˢ I, dₜ u p - lapₓ u p = H p) ∧
      LocHolderOnPar α (dₜ u) (U ×ˢ I) ∧
      (∀ i, LocHolderOnPar α (fun p ↦ gradₓ u p i) (U ×ˢ I)) ∧
      ∀ i j, LocHolderOnPar α (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (U ×ˢ I) := by
  sorry

end ParabolicBasic
