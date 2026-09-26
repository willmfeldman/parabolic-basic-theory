/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Analysis.Partials
public import ParabolicBasic.Analysis.PartialsSmooth
public import ParabolicBasic.Analysis.PartitionMollifier
public import ParabolicBasic.Analysis.UniformLimitDerivs
public import ParabolicBasic.Barriers.ExteriorSphere
public import ParabolicBasic.Barriers.Heat
public import ParabolicBasic.Barriers.Perron
public import ParabolicBasic.Barriers.Radial
public import ParabolicBasic.Basic.Setting
public import ParabolicBasic.Calculus.Affine
public import ParabolicBasic.Calculus.Extremum
public import ParabolicBasic.Calculus.Slice
public import ParabolicBasic.Caloric.Bernstein
public import ParabolicBasic.Caloric.BernsteinBasic
public import ParabolicBasic.Caloric.BernsteinLimit
public import ParabolicBasic.Caloric.BernsteinTaylor
public import ParabolicBasic.Caloric.Regularity
public import ParabolicBasic.Classical.MaxPrinciple
public import ParabolicBasic.Classical.ToViscosity
public import ParabolicBasic.Comparison.Continuous
public import ParabolicBasic.Comparison.ExpChange
public import ParabolicBasic.Comparison.Frontier
public import ParabolicBasic.Comparison.LinearSource
public import ParabolicBasic.Comparison.Parabolic
public import ParabolicBasic.Comparison.SemilinearHyp
public import ParabolicBasic.Comparison.SumClosure
public import ParabolicBasic.Comparison.Unique
public import ParabolicBasic.Defs.Classical
public import ParabolicBasic.Defs.Holder
public import ParabolicBasic.Defs.Parabolic
public import ParabolicBasic.Defs.Semilinear
public import ParabolicBasic.Defs.Touching
public import ParabolicBasic.Defs.Viscosity
public import ParabolicBasic.Dirichlet.Ball
public import ParabolicBasic.MainTheorems
public import ParabolicBasic.Perron.Bump
public import ParabolicBasic.Perron.Class
public import ParabolicBasic.Perron.Envelope
public import ParabolicBasic.Perron.Existence
public import ParabolicBasic.Perron.SupStability
public import ParabolicBasic.Schauder.Campanato
public import ParabolicBasic.Schauder.Holder
public import ParabolicBasic.Schauder.Iteration.Approx
public import ParabolicBasic.Schauder.Iteration.Basic
public import ParabolicBasic.Schauder.Iteration.Interior
public import ParabolicBasic.Schauder.Iteration.Iterate
public import ParabolicBasic.Schauder.Iteration.Step
public import ParabolicBasic.Schauder.Poly
public import ParabolicBasic.Schauder.PolyExtract
public import ParabolicBasic.Semilinear.ExistenceBasic
public import ParabolicBasic.Semilinear.ExistenceGlue
public import ParabolicBasic.Semilinear.ExistenceRegularity
public import ParabolicBasic.Semilinear.InitialGradient
public import ParabolicBasic.Semilinear.Smooth
public import ParabolicBasic.Semilinear.SmoothBasic
public import ParabolicBasic.Semilinear.SmoothDiffQuot
public import ParabolicBasic.Semilinear.SmoothHolderCk
public import ParabolicBasic.Transport.Calculus
public import ParabolicBasic.Transport.Equiv
public import ParabolicBasic.Transport.Operator
public import ParabolicBasic.Transport.Quartic
public import ParabolicBasic.Transport.Viscosity
public import ParabolicBasic.Viscosity.Basic
public import ParabolicBasic.Viscosity.Classical
public import ParabolicBasic.Viscosity.Invariance
public import ParabolicBasic.Viscosity.SliceAux
public import ParabolicBasic.Viscosity.Stability

/-!
# ParabolicBasic

Basic theory of the heat operator `∂ₜ - Δₓ` and of semilinear heat equations
`∂ₜu = Δₓu - f(x, u)` on `ℝᵈ × ℝ`. This root module imports the whole library. The headline
results are in `ParabolicBasic.MainTheorems`: `caloric_dirichlet_ball`, `semilinear_comparison`,
`isSemilinearViscSubOn_of_solOn`, `isSemilinearViscSuperOn_of_solOn`, `semilinear_unique`,
`semilinear_exists`, `semilinear_contDiffOn_of_contDiff` and
`semilinear_continuousOn_gradₓ_of_contDiff`.
-/

@[expose] public section
