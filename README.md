# ParabolicBasic

`ParabolicBasic` is a Lean 4 formalization of the basic theory of the heat
operator `∂ₜ − Δₓ` and of semilinear heat equations `∂ₜu = Δₓu − f(x, u)` on
`ℝᵈ × ℝ` (`E d × ℝ`, with `E d = EuclideanSpace ℝ (Fin d)`). It covers
comparison for viscosity solutions, parabolic Perron existence with barriers,
interior `C^∞` regularity of viscosity caloric functions through Bernstein
estimates, the heat Dirichlet problem on ball cylinders, interior Schauder
estimates, and existence, uniqueness and regularity for the semilinear
Cauchy–Dirichlet problem on bounded `C²` domains. The approximately 14,700
lines of Lean source are `sorry`-free and introduce no axioms: every theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Main theorems

The root module `ParabolicBasic` imports the whole library. The headline
results are collected in `ParabolicBasic/MainTheorems.lean`:

| Declaration (`ParabolicBasic.…`) | Statement |
|---|---|
| `caloric_dirichlet_ball` | Heat Dirichlet problem on `B_ρ(x₀) × (a, b]`: continuous data on the parabolic boundary give a solution that is continuous on the closed cylinder and `C^∞` inside |
| `semilinear_comparison` | Comparison for continuous viscosity sub- and supersolutions of `∂ₜu = Δₓu − f(x, u)` on `V × (a, b]` |
| `isSemilinearViscSubOn_of_solOn`, `isSemilinearViscSuperOn_of_solOn` | Classical `C^{2,1}` solutions are viscosity solutions |
| `semilinear_unique` | Uniqueness for the semilinear Cauchy–Dirichlet problem |
| `semilinear_exists` | Existence of a classical solution on a bounded `C²` domain with Lipschitz data |
| `semilinear_contDiffOn_of_contDiff` | Interior `C^∞` regularity when `f` is `C^∞` |
| `semilinear_continuousOn_gradₓ_of_contDiff` | The spatial gradient `∇ₓu` is continuous up to `t = 0` |

The hypotheses on `f` are: Hölder continuity in `x`, uniformly in `z`;
Lipschitz continuity in `z`, uniformly in `x`; and, for existence,
boundedness. All three are required on the closure of the domain.

The main intermediate results are:

- `comparison_usc_lsc`: comparison for semicontinuous viscosity sub- and
  supersolutions;
- `exists_viscSolution_cyl`: Perron's method on a space-time cylinder, given
  barriers;
- `isSmoothCaloricOn_of_isVisc`: continuous viscosity solutions of the heat
  equation are `C^∞` and caloric;
- `IsSmoothCaloricOn.norm_gradₓ_le` and the Taylor coefficient bounds:
  Bernstein estimates;
- `schauder_interior`: interior `C^{2+α,1+α/2}` Schauder estimates;
- `isC21On_of_polyApprox`: a Campanato-type characterization of `C^{2,1}`
  through polynomial approximation.

The Schauder theory uses the pointwise sup-norm (L^∞) form of the Campanato
iteration due to Caffarelli, L. Wang and Safonov, not Campanato's L² method.

## Building

This project uses the pinned Lean toolchain in `lean-toolchain` and dependency
revisions in `lake-manifest.json`. From a checkout, fetch the Mathlib cache and
build the entire library:

```bash
lake exe cache get
lake build
```

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.35.0-rc3`.
- [viscosity-solution-theory](https://github.com/willmfeldman/viscosity-solution-theory)
  [`v0.4.0`](https://github.com/willmfeldman/viscosity-solution-theory/releases/tag/v0.4.0)
  (library `ViscositySolns`). It supplies the elliptic Crandall–Ishii–Lions
  theory: the Crandall–Ishii lemma and the strict comparison theorem, applied
  to the heat operator through the linear isomorphism `E d × ℝ ≃ ℝᵈ⁺¹`
  (`ParabolicBasic/Transport/`). Its Perron existence theorem is not used.
- [aleksandrov-differentiability](https://github.com/willmfeldman/aleksandrov-differentiability)
  [`v0.4.0`](https://github.com/willmfeldman/aleksandrov-differentiability/releases/tag/v0.4.0),
  a dependency of `ViscositySolns`.

## Layout

- `ParabolicBasic/Basic/`, `ParabolicBasic/Defs/`: the setting and vocabulary
  (slice derivatives `gradₓ`, `lapₓ`, `dₜ`; parabolic cylinders and boundaries;
  parabolic Hölder spaces; touching; viscosity and classical solutions).
- `ParabolicBasic/Calculus/`, `Analysis/`: calculus on slices, partial
  derivatives, mollification.
- `ParabolicBasic/Viscosity/`, `Classical/`: elementary viscosity lemmas, the
  maximum principle, classical ⇒ viscosity.
- `ParabolicBasic/Transport/`, `Comparison/`: transport to `ViscositySolns` and
  the comparison principle.
- `ParabolicBasic/Perron/`, `Barriers/`, `Dirichlet/`: Perron's method,
  barriers, the Dirichlet problem on ball cylinders.
- `ParabolicBasic/Caloric/`: Bernstein estimates and regularity of caloric
  functions.
- `ParabolicBasic/Schauder/`: parabolic Hölder spaces, the Campanato
  characterization, and the interior Schauder iteration.
- `ParabolicBasic/Semilinear/`: the semilinear Cauchy–Dirichlet problem.
- `ParabolicBasic/MainTheorems.lean`: the headline theorems.

## References

- M. G. Crandall, H. Ishii, P.-L. Lions, [*User's guide to viscosity solutions
  of second order partial differential
  equations*](https://doi.org/10.1090/S0273-0979-1992-00266-5), Bull. AMS 27
  (1992).
- G. M. Lieberman, *Second Order Parabolic Differential Equations*, World
  Scientific (1996).
- O. A. Ladyzhenskaya, V. A. Solonnikov, N. N. Ural'tseva, *Linear and
  Quasi-linear Equations of Parabolic Type*, AMS (1968).
- L. A. Caffarelli, *Interior a priori estimates for solutions of fully
  non-linear equations*, Ann. of Math. 130 (1989); L. Wang, *On the regularity
  theory of fully nonlinear parabolic equations* I–II, CPAM 45 (1992);
  M. V. Safonov, *Classical solution of second-order nonlinear elliptic
  equations*, Izv. Akad. Nauk SSSR 52 (1988).

## License and citation

The project is released under the [Apache License 2.0](LICENSE). If you use
this work, please cite it using [CITATION.cff](CITATION.cff).

The Lean proofs were written by AI coding agents (Claude, by Anthropic) under
the author's mathematical direction and review. The theorem statements and
proof routes were reviewed by the author. Correctness rests on Lean's kernel
check, together with the comparator challenges in `challenges/`. See
`automation` in [formalization.yaml](formalization.yaml).
