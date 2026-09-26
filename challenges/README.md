# Comparator Challenges

This directory contains release comparator workspaces for the public
`ParabolicBasic` API. Each subdirectory is a standalone Lake workspace with:

- `Challenge.lean`: the trusted statement surface. It imports `Mathlib` only,
  in most workspaces through a few vocabulary files under `Challenge/`; see
  below.
- `Solution.lean`: the solution proof, importing the library.
- `config.json`: comparator module names, theorem names, and permitted axioms.
- `lakefile.toml`: local workspace metadata, pinned through the parent project.

The `Challenge` files restate all project-local vocabulary inline: the slice
derivatives `dₜ`, `lapₓ`, `gradₓ`, the parabolic boundary, touching, viscosity
sub- and supersolutions, classical `C^{2,1}` solutions, `C²` boundaries, and
parabolic Hölder continuity. They do not import the library, so a referee can
check the meaning of each statement without reading it. The flagship
`caloric-dirichlet-ball` restates no project definition at all: its statement
uses only Mathlib's `EuclideanSpace`, balls and spheres, `deriv` and the
Laplacian `Δ`.

The inline definitions reuse the library's names, so Comparator also checks
that each one is exactly the library's definition. That check compares the
names of the small auxiliary proofs Lean creates inside definitions (for
example for the numeral `2` in `ContDiff ℝ 2`). Lean shares those proofs only
within a file. For this reason the vocabulary is split into
`Challenge/Setting.lean`, `Challenge/Classical.lean`,
`Challenge/Viscosity.lean`, and so on, following the library's file
boundaries (`Basic/Setting.lean`, `Defs/Classical.lean`,
`Defs/Viscosity.lean`, …). A few definitions that no statement uses
(`HasC2Boundary`, `IsC21On`, `IsViscSubOn`) are restated in some workspaces
only so that the auxiliary proofs reused by later definitions carry the
library's names. Every file still imports `Mathlib` only.

## Challenge set

| Directory | Statement certified | Library theorem used by the solution |
|---|---|---|
| `caloric-dirichlet-ball` | Heat Dirichlet problem on `B_ρ(x₀) × (a, b]`, in Mathlib vocabulary only: continuous data on `(B̄ × {a}) ∪ (∂B × [a, b])` give `h ∈ C(B̄ × [a, b])`, `C^∞` in `B × (a, b)`, with the time derivative equal to the spatial Laplacian, and matching the data on both faces | `caloric_dirichlet_ball` (with Mathlib's `closure_ball`, `frontier_ball`) |
| `semilinear-comparison` | Comparison for past-touching viscosity sub- and supersolutions of `∂ₜu = Δu − f(x, u)` on bounded open `V × (a, b]`, with `f` Hölder in `x` and Lipschitz in `z` [CIL Thm 8.2]; plus the uniqueness corollary for the Cauchy–Dirichlet problem (redundant coverage) | `semilinear_comparison`, `semilinear_unique` |
| `classical-viscosity` | Classical `C^{2,1}` solutions of `∂ₜu = Δu − f(x, u)` on open `U × I` (with `I` containing a left neighbourhood of each of its points, and `f` arbitrary) are past-touching viscosity sub- and supersolutions [CIL §8] | `isSemilinearViscSubOn_of_solOn`, `isSemilinearViscSuperOn_of_solOn` |
| `semilinear-existence` | Existence for `∂ₜu = Δₓu − f(x, u)` in `U × (0, ∞)`, `u = g` on the parabolic boundary. Hypotheses: bounded open `U` with `C²` boundary (global defining function), `f` Hölder in `x`, Lipschitz in `z` and bounded, `g` Lipschitz. The solution lies in `C(Ū × [0, ∞)) ∩ C^{2,1}(U × (0, ∞))` [Lieberman IX; LSU V] | `semilinear_exists` (Perron and barriers, then interior Schauder) |
| `semilinear-regularity` | (a) A classical `C^{2,1}` solution with `C^∞` `f` is `ContDiffOn ℝ ∞` on `U × I`; (b) for a Cauchy–Dirichlet solution with continuous `f` and `C²` data, `∇ₓu` is continuous on `U × [0, ∞)` (in the interior, up to `t = 0`) | `semilinear_contDiffOn_of_contDiff`, `semilinear_continuousOn_gradₓ_of_contDiff` |
| `caloric-smooth` | A continuous viscosity solution of the heat equation on an open `O ⊆ ℝᵈ × ℝ` is `ContDiffOn ℝ ∞` on `O`, with `∂ₜu = Δₓu` pointwise (stated in Mathlib vocabulary, not through the library's `IsSmoothCaloricOn`) | `isSmoothCaloricOn_of_isVisc` |
| `schauder-interior` | Interior Schauder estimates, qualitative form: a continuous viscosity solution of `∂ₜu − Δₓu = H`, with `H` locally parabolic-`C^α` and `α ∈ (0, 1)`, is `C^{2,1}` and solves the equation pointwise; `∂ₜu`, `∂ᵢu` and `∂ᵢ∂ⱼu` are locally parabolic-`C^α` for the metric `max ‖x − y‖ √|t − s|` | `schauder_interior` (L^∞ Campanato iteration of Caffarelli, L. Wang and Safonov) |
| `model-sanity` | Definition-level sanity checks: `u = t` is **not** a viscosity subsolution of the heat equation (this pins the sign convention) but is a supersolution; `‖x‖² + 2d·t` is a classical solution of the heat equation on `ℝᵈ × ℝ` (non-vacuity of the classical-solution hypotheses); the parabolic boundary of `B₁(0) × (0, 1]` is `(B̄₁ × {0}) ∪ (∂B₁ × [0, 1])` and is nonempty | slice calculus, `isViscSuperOn_of_contDiffOn`, Mathlib's `laplacian_norm_sub_sq` |

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
- `model-sanity` is a sanity check and is not counted as coverage of the
  headline results.

## Toolchain

- Lean: `leanprover/lean4:v4.30.0`
- Mathlib: `v4.30.0`
- viscosity-solution-theory (`ViscositySolns`) and AleksandrovDifferentiability:
  pinned through the parent `lake-manifest.json`. The comparison, uniqueness,
  existence and Dirichlet solutions depend on them, so a comparator run on
  these challenges also transitively audits those projects.
- Comparator: `leanprover/comparator`, with a `lean4export` build matching Lean
  `v4.30.0` and the pinned `landrun` revision (see
  `scripts/release-comparator.sh`); the release workflow runs on a standard
  GitHub-hosted Linux runner.

Every workspace sets `packagesDir = "../../.lake/packages"` in its
`lakefile.toml` (and records the same folder in its `lake-manifest.json`), so
all of them share the root workspace's dependency checkouts and builds. The
manifests lock the same revisions as the root manifest.

Repository CI builds the full library, validates the manifest against every
challenge configuration and the workspace inventory, and checks headline
declaration names and axioms. On every push it also elaborates the
Challenge/Solution pairs with `scripts/build-challenges.sh --trusted-all`.
That shows each file compiles against the current library; **it does not
compare statements**. Statement equality, proof checking and permitted-axiom
checks for those pairs belong to the separate release Comparator workflow.

Each standalone workspace defaults to its `Challenge` target only, so a plain
`lake build` is safe while preparing an adversarial Comparator run: it does
not prebuild `Solution.lean`.

## Acceptance

For routine development in a trusted checkout:

```sh
lake exe cache get && lake build
./scripts/build-challenges.sh --trusted-all
```

For a Comparator release run, dispatch `.github/workflows/release-comparator.yml`
on a fresh release-candidate commit. It installs the pinned tools, runs every
configuration, and uploads an attestation artifact. Treat `Solution.lean` as
potentially adversarial. Review and trust the release checkout's
`Challenge.lean` and `Challenge/*.lean`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `config.json`, and the Comparator toolchain. Then:

1. Run `make challenges-challenge-only` (or `lake build` in an individual
   workspace). This elaborates only the trusted `Challenge` target.
2. Invoke Comparator in its release sandbox with that workspace's
   `config.json`, without first running `lake build Solution` or the trusted
   all-workspace driver.
3. Confirm that each theorem depends only on `propext`, `Classical.choice`
   and `Quot.sound`.

### Recorded acceptance

The release Comparator workflow accepted all eight workspaces on 2026-09-26,
on a standard GitHub-hosted Linux runner, with Lean `v4.30.0`, Mathlib
`c5ea003`, Comparator `d03acab`, `landrun` `5ed4a3d`, and `lean4export`
`a3e35a5`, on a release candidate with the same Lean sources as this
release:

| Workspace | Statement comparison and kernel check | Axioms |
|---|---|---|
| `caloric-dirichlet-ball` | PASS | `propext`, `Classical.choice`, `Quot.sound` only |
| `caloric-smooth` | PASS | same |
| `classical-viscosity` | PASS | same |
| `model-sanity` | PASS | same |
| `schauder-interior` | PASS | same |
| `semilinear-comparison` | PASS | same |
| `semilinear-existence` | PASS | same |
| `semilinear-regularity` | PASS | same |

The GitHub release carries the attestation artifact from running this
workflow on the release commit itself: commit and tree hashes, toolchain and
tool revisions, per-workspace results, and complete logs. Comparator ran under
`landrun` without the additional `systemd-run` containment that upstream
recommends for a full adversarial guarantee, so these results establish
Comparator's checks, not that stronger sandbox claim.

As a local, non-sandboxed pre-check, `scripts/check-challenge-definitions.lean`
compares every definition restated in a workspace's `Challenge` modules,
including auxiliary proofs, against the library constant of the same name
(kind, type, value, universe parameters, reducibility hints). It reports a
match in all eight workspaces. It does not replace Comparator.
