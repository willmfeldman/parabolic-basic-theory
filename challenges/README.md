# Comparator Challenges

This directory contains the release comparator workspace for the public
`ParabolicBasic` API: a single workspace, `main-results`, for the library's
main results. It is a standalone Lake workspace with:

- `Vocabulary.lean` and `Vocabulary/*.lean`: the restated definitions, as Lean
  modules that import `Mathlib` only; see below.
- `Challenge.lean`: the trusted statement surface. It imports `Mathlib` and
  the workspace's own `Vocabulary` modules only.
- `Solution.lean`: the solution proofs, importing the library.
- `config.json`: comparator module names, theorem names, and permitted axioms.
- `lakefile.toml`: local workspace metadata, pinned through the parent project.

Every `.lean` file is a Lean module (`module` header). `python3
scripts/challenge-prep.py check` checks the layout of the workspace.

The `Vocabulary` files restate all project-local vocabulary inline: the slice
derivatives `dₜ`, `lapₓ`, `gradₓ`, the parabolic boundary, touching, viscosity
sub- and supersolutions, classical `C^{2,1}` solutions, `C²` boundaries, and
parabolic Hölder continuity. They do not import the library, so a referee can
check the meaning of each statement without reading it. The flagship
statement (`challenge_caloric_dirichlet_ball`) uses no project definition at
all, only Mathlib's `EuclideanSpace`, balls and spheres, `deriv` and the
Laplacian `Δ`.

The inline definitions reuse the library's names, so Comparator also checks
that each one is exactly the library's definition. That check compares the
names of the small auxiliary proofs Lean creates inside definitions (for
example for the numeral `2` in `ContDiff ℝ 2`). Lean shares those proofs only
within a file. For this reason the vocabulary is split into
`Vocabulary/Setting.lean`, `Vocabulary/Classical.lean`,
`Vocabulary/Viscosity.lean`, and so on, following the library's file
boundaries (`Basic/Setting.lean`, `Defs/Classical.lean`,
`Defs/Viscosity.lean`, …); the root `Vocabulary.lean` only re-exports them,
and `Challenge.lean` imports them directly (its first comment line, starting
`challenge-prep: split vocabulary`, records this). A few definitions that no
statement uses (such as `HasC2Boundary`) are restated only so that the
auxiliary proofs reused by later definitions carry the library's names. Every
vocabulary file still imports `Mathlib` only.

## Challenge set

`Challenge.lean` (and `Solution.lean`) has one section per group of
statements below, in this order; `config.json` lists all 14 theorems.

| Group | Statement certified | Library theorem used by the solution |
|---|---|---|
| `caloric-dirichlet-ball` | Heat Dirichlet problem on `B_ρ(x₀) × (a, b]`, in Mathlib vocabulary only: continuous data on `(B̄ × {a}) ∪ (∂B × [a, b])` give `h ∈ C(B̄ × [a, b])`, `C^∞` in `B × (a, b)`, with the time derivative equal to the spatial Laplacian, and matching the data on both faces | `caloric_dirichlet_ball` (with Mathlib's `closure_ball`, `frontier_ball`) |
| `semilinear-comparison` | Comparison for past-touching viscosity sub- and supersolutions of `∂ₜu = Δu − f(x, u)` on bounded open `V × (a, b]`, with `f` Hölder in `x` and Lipschitz in `z` [CIL Thm 8.2]; plus the uniqueness corollary for the Cauchy–Dirichlet problem (redundant coverage). Sanity check: the parabolic boundary of `B₁(0) × (0, 1]` is `(B̄₁ × {0}) ∪ (∂B₁ × [0, 1])` and is nonempty | `semilinear_comparison`, `semilinear_unique`; `parBdry` unfolded with Mathlib's `closure_ball`, `frontier_ball` |
| `classical-viscosity` | Classical `C^{2,1}` solutions of `∂ₜu = Δu − f(x, u)` on open `U × I` (with `I` containing a left neighbourhood of each of its points, and `f` arbitrary) are past-touching viscosity sub- and supersolutions [CIL §8]. Sanity checks: `u = t` is **not** a viscosity subsolution of the heat equation (this pins the sign convention) but is a supersolution; `‖x‖² + 2d·t` is a classical solution of the heat equation on `ℝᵈ × ℝ` (non-vacuity of the classical-solution hypotheses) | `isSemilinearViscSubOn_of_solOn`, `isSemilinearViscSuperOn_of_solOn`; for the sanity checks, slice calculus, `isViscSuperOn_of_contDiffOn` and Mathlib's `laplacian_norm_sub_sq` |
| `semilinear-existence` | Existence for `∂ₜu = Δₓu − f(x, u)` in `U × (0, ∞)`, `u = g` on the parabolic boundary. Hypotheses: bounded open `U` with `C²` boundary (global defining function), `f` Hölder in `x`, Lipschitz in `z` and bounded, `g` Lipschitz. The solution lies in `C(Ū × [0, ∞)) ∩ C^{2,1}(U × (0, ∞))` [Lieberman IX; LSU V] | `semilinear_exists` (Perron and barriers, then interior Schauder) |
| `semilinear-regularity` | (a) A classical `C^{2,1}` solution with `C^∞` `f` is `ContDiffOn ℝ ∞` on `U × I`; (b) for a Cauchy–Dirichlet solution with continuous `f` and `C²` data, `∇ₓu` is continuous on `U × [0, ∞)` (in the interior, up to `t = 0`) | `semilinear_contDiffOn_of_contDiff`, `semilinear_continuousOn_gradₓ_of_contDiff` |
| `caloric-smooth` | A continuous viscosity solution of the heat equation on an open `O ⊆ ℝᵈ × ℝ` is `ContDiffOn ℝ ∞` on `O`, with `∂ₜu = Δₓu` pointwise (stated in Mathlib vocabulary, not through the library's `IsSmoothCaloricOn`) | `isSmoothCaloricOn_of_isVisc` |
| `schauder-interior` | Interior Schauder estimates, qualitative form: a continuous viscosity solution of `∂ₜu − Δₓu = H`, with `H` locally parabolic-`C^α` and `α ∈ (0, 1)`, is `C^{2,1}` and solves the equation pointwise; `∂ₜu`, `∂ᵢu` and `∂ᵢ∂ⱼu` are locally parabolic-`C^α` for the metric `max ‖x − y‖ √|t − s|` | `schauder_interior` (L^∞ Campanato iteration of Caffarelli, L. Wang and Safonov) |

### Scope of each challenge

- `caloric-dirichlet-ball`, `semilinear-existence` and `caloric-smooth` are
  end-to-end: every hypothesis is a standard mathematical assumption, and the
  Perron barrier hypotheses of `exists_viscSolution_cyl` are discharged inside
  the proofs.
- `semilinear-comparison` and `semilinear-existence` use Hölder-in-`x` and
  Lipschitz-in-`z` hypotheses on `f`. These are less general than the
  "continuous in `x` uniformly in `z`" condition of [CIL].
- The uniqueness theorem adds little independent coverage beyond comparison.
- `schauder-interior` is the qualitative interior estimate, with constants
  depending on the compact set. The gradient is asserted only to be
  parabolic-`C^α`, not `C^{(1+α)/2}` in time.
- The sanity checks in `classical-viscosity` and `semilinear-comparison`
  (`challenge_time_not_viscSub`, `challenge_time_viscSuper`,
  `challenge_caloric_quadratic_solOn`, `challenge_parBdry_ball_nonempty`) are
  sign-convention and non-vacuity checks on the definitions. They are not
  counted as coverage of the headline results.

## Toolchain

- Lean: `leanprover/lean4:v4.36.0`
- Mathlib: `v4.36.0` (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`)
- viscosity-solution-theory (`ViscositySolns`) and AleksandrovDifferentiability:
  pinned through the parent `lake-manifest.json`. The comparison, uniqueness,
  existence and Dirichlet solutions depend on them, so a comparator run on
  these challenges also transitively audits those projects.
- Comparator: the toolchain's own `lake comparator`, run with `--paranoid`
  (every checker bundled with the toolchain) by
  `scripts/release-comparator.sh`. There are no separate tool pins: the
  toolchain pin is the tool pin. The release workflow runs on a standard
  GitHub-hosted Linux runner.

The workspace sets `packagesDir = "../../.lake/packages"` in its
`lakefile.toml` (and records the same folder in its `lake-manifest.json`), so
it shares the root workspace's dependency checkouts and builds. Its manifest
locks the same revisions as the root manifest.

Repository CI builds the full library, validates the manifest against every
challenge configuration and the workspace inventory, and checks headline
declaration names and axioms. On every push it also elaborates the
Vocabulary, Challenge and Solution targets with
`scripts/build-challenges.sh --trusted-all` and runs
`python3 scripts/challenge-prep.py check`.
That shows each file compiles against the current library; **it does not
compare statements**. Statement equality, proof checking and permitted-axiom
checks for those pairs belong to the separate release Comparator workflow.

The workspace defaults to its `Vocabulary` and `Challenge` targets only, so a plain
`lake build` is safe while preparing an adversarial Comparator run: it does
not prebuild `Solution.lean`.

## Acceptance

For routine development in a trusted checkout:

```sh
lake exe cache get && lake build
./scripts/build-challenges.sh --trusted-all
```

For a Comparator release run, dispatch `.github/workflows/release-comparator.yml`
on a fresh release-candidate commit. It prepares the comparator's bubblewrap
sandbox, runs `lake comparator --paranoid` on every configuration, and uploads
an attestation artifact. Treat `Solution.lean` as
potentially adversarial. Review and trust the release checkout's
`Vocabulary.lean`, `Vocabulary/*.lean` and `Challenge.lean`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `config.json`, and the toolchain. Then:

1. Run `make challenges-challenge-only` (or `lake build` in
   `challenges/main-results`). This elaborates only the trusted `Vocabulary` and `Challenge`
   targets.
2. Run `bash scripts/release-comparator.sh install` once, then
   `bash scripts/release-comparator.sh run`. It runs `lake comparator
   --paranoid` with the workspace's `config.json` in Lake's bubblewrap
   sandbox, judging a copy of the repository outside `/home` (the sandbox hides
   home directories), without first running `lake build Solution` or the
   trusted driver.
3. Confirm that each theorem depends only on `propext`, `Classical.choice`
   and `Quot.sound`.

### Recorded acceptance

The release comparator workflow accepted the workspace on a standard
GitHub-hosted Linux runner, with Lean `v4.36.0` and Mathlib `fc4f59e`, running
`lake comparator --paranoid`, on a release candidate with the same Lean sources
as this release:

| Workspace | Theorems | Statement comparison and kernel check | Axioms |
|---|---|---|---|
| `main-results` | 14 | PASS | `propext`, `Classical.choice`, `Quot.sound` only |

The GitHub release carries the attestation artifact from running this
workflow on the release commit itself: commit and tree hashes, toolchain,
per-workspace results, and complete logs.

As a local, non-sandboxed pre-check, `scripts/check-challenge-definitions.lean`
compares every definition restated in the workspace's `Vocabulary` modules,
including auxiliary proofs, against the library constant of the same name
(kind, type, value, universe parameters, reducibility hints). It reports a
match for every challenge theorem. It does not replace Comparator.
