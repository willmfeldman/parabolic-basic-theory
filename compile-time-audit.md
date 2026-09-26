# Compile-time audit

Methodology: `rm -rf .lake/build` (the project's own outputs only; `.lake/packages` stays built), then `lake build ParabolicBasic` through the local build throttle. Per-module seconds are Lake's `Built X (Ns)` figures, which include import loading. Machine: 8-core / 16 GB macOS laptop, shared with other Lean work.

## History

| Date | Change | Threads | Wall | Sum of per-module times |
|---|---|---:|---:|---:|
| 2026-09-26 | baseline (no file is a `module`) | 2 | 680 s | 1178 s |
| 2026-09-26 | 38 files that do not depend on `ViscositySolns` converted to `module` | 3 | 448 s | 923 s |
| 2026-09-26 | dependencies module-ized (viscosity-solution-theory v0.2.0, aleksandrov-differentiability v0.2.0); all 68 library files are `module`s | 3 | **105 s** | 238 s |

Budget: 1 min per 10k lines, i.e. about 88 s for 14,749 lines.

Diagnosis (`lean -Dprofiler=true`, before conversion): import loading took about 1090 s and elaboration about 180 s in total. A non-`module` file loads every imported module's `.olean.private` (Mathlib: 3.2 GB) on top of the public `.olean` (1.7 GB). A `module` loads only the public part. A `module` cannot import a non-module, so the conversion had to proceed bottom-up through the dependency chain.

## Per-module times, latest run (sorted by seconds)

| Module | Lines | Seconds |
|---|---:|---:|
| `ParabolicBasic.Schauder.Campanato` | 676 | 9.4 |
| `ParabolicBasic.Schauder.PolyExtract` | 295 | 7.3 |
| `ParabolicBasic.Schauder.Poly` | 490 | 6.1 |
| `ParabolicBasic.Caloric.BernsteinTaylor` | 729 | 5.9 |
| `ParabolicBasic.Barriers.ExteriorSphere` | 187 | 5.3 |
| `ParabolicBasic.Analysis.Partials` | 338 | 5.2 |
| `ParabolicBasic.Semilinear.InitialGradient` | 390 | 5 |
| `ParabolicBasic.Schauder.Holder` | 652 | 4.9 |
| `ParabolicBasic.Caloric.Bernstein` | 391 | 4.9 |
| `ParabolicBasic.Comparison.SumClosure` | 423 | 4.8 |
| `ParabolicBasic.Comparison.Parabolic` | 422 | 4.8 |
| `ParabolicBasic.Barriers.Heat` | 208 | 4.8 |
| `ParabolicBasic.Calculus.Slice` | 334 | 4.6 |
| `ParabolicBasic.Barriers.Radial` | 318 | 4.4 |
| `ParabolicBasic.Caloric.BernsteinBasic` | 491 | 4.3 |
| `ParabolicBasic.Analysis.UniformLimitDerivs` | 251 | 4.3 |
| `ParabolicBasic.Perron.SupStability` | 245 | 4.2 |
| `ParabolicBasic.Schauder.Iteration.Interior` | 406 | 4.2 |
| `ParabolicBasic.Semilinear.SmoothDiffQuot` | 236 | 4.1 |
| `ParabolicBasic.Viscosity.SliceAux` | 108 | 3.9 |
| `ParabolicBasic.Analysis.PartitionMollifier` | 115 | 3.8 |
| `ParabolicBasic.Caloric.Regularity` | 216 | 3.8 |
| `ParabolicBasic.Perron.Bump` | 169 | 3.8 |
| `ParabolicBasic.Schauder.Iteration.Approx` | 225 | 3.8 |
| `ParabolicBasic.Transport.Operator` | 320 | 3.5 |
| `ParabolicBasic.Classical.MaxPrinciple` | 376 | 3.5 |
| `ParabolicBasic.Analysis.PartialsSmooth` | 110 | 3.5 |
| `ParabolicBasic.Viscosity.Stability` | 176 | 3.5 |
| `ParabolicBasic.Semilinear.SmoothHolderCk` | 220 | 3.5 |
| `ParabolicBasic.Classical.ToViscosity` | 222 | 3.4 |
| `ParabolicBasic.Transport.Equiv` | 310 | 3.3 |
| `ParabolicBasic.Basic.Setting` | 68 | 3.2 |
| `ParabolicBasic.Transport.Quartic` | 108 | 3.2 |
| `ParabolicBasic.Caloric.BernsteinLimit` | 137 | 3.2 |
| `ParabolicBasic.Comparison.SemilinearHyp` | 178 | 3.1 |
| `ParabolicBasic.Transport.Calculus` | 92 | 3.1 |
| `ParabolicBasic.Calculus.Extremum` | 201 | 3 |
| `ParabolicBasic.Schauder.Iteration.Iterate` | 554 | 3 |
| `ParabolicBasic.Viscosity.Basic` | 233 | 2.9 |
| `ParabolicBasic.Viscosity.Invariance` | 162 | 2.9 |
| `ParabolicBasic.Barriers.Perron` | 203 | 2.9 |
| `ParabolicBasic.Semilinear.SmoothBasic` | 89 | 2.8 |
| `ParabolicBasic.Transport.Viscosity` | 181 | 2.8 |
| `ParabolicBasic.Schauder.Iteration.Basic` | 151 | 2.8 |
| `ParabolicBasic.Semilinear.ExistenceRegularity` | 63 | 2.8 |
| `ParabolicBasic.Calculus.Affine` | 99 | 2.7 |
| `ParabolicBasic.Comparison.ExpChange` | 174 | 2.7 |
| `ParabolicBasic.Perron.Class` | 194 | 2.7 |
| `ParabolicBasic.Semilinear.ExistenceGlue` | 169 | 2.7 |
| `ParabolicBasic.Defs.Classical` | 72 | 2.6 |
| `ParabolicBasic.Comparison.Frontier` | 73 | 2.6 |
| `ParabolicBasic.Semilinear.ExistenceBasic` | 56 | 2.6 |
| `ParabolicBasic.Comparison.Unique` | 87 | 2.6 |
| `ParabolicBasic.Dirichlet.Ball` | 193 | 2.6 |
| `ParabolicBasic.Schauder.Iteration.Step` | 88 | 2.6 |
| `ParabolicBasic.Viscosity.Classical` | 38 | 2.4 |
| `ParabolicBasic.Comparison.Continuous` | 73 | 2.4 |
| `ParabolicBasic.Defs.Holder` | 36 | 2.2 |
| `ParabolicBasic.Defs.Semilinear` | 46 | 2.2 |
| `ParabolicBasic.Defs.Viscosity` | 87 | 2.2 |
| `ParabolicBasic.Perron.Existence` | 94 | 2.2 |
| `ParabolicBasic.MainTheorems` | 184 | 2.2 |
| `ParabolicBasic.Perron.Envelope` | 129 | 2.1 |
| `ParabolicBasic.Defs.Parabolic` | 41 | 2.1 |
| `ParabolicBasic.Comparison.LinearSource` | 124 | 2 |
| `ParabolicBasic.Semilinear.Smooth` | 100 | 2 |
| `ParabolicBasic.Defs.Touching` | 36 | 1.9 |
| `ParabolicBasic` | 87 | 1.9 |
