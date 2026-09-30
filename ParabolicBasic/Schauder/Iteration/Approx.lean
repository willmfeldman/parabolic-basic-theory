/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Iteration.Basic
public import ParabolicBasic.Dirichlet.Ball
public import ParabolicBasic.Comparison.LinearSource
public import ParabolicBasic.Caloric.BernsteinTaylor

/-!
# Approximation by a caloric function; caloric Taylor polynomials

`Q₁ = cCyl 0 0 1 = ball 0 1 ×ˢ Ioo (-1) 1`.

* `abs_sub_caloric_le`: a solution `u` of `dₜu − lapₓu = H` on `Q₁` with `|H| ≤ δ` and the
  caloric `h` with the same parabolic-boundary values satisfy `|u − h| ≤ 2δ` on `closure Q₁`
  (`abs_sub_le_of_heat_source_cCyl`, a comparison argument; this is the only comparison in the
  iteration).
* `exists_caloric_approx`: with `|u| ≤ 1`, the solution `h` of the heat Dirichlet problem
  (`caloric_dirichlet_cCyl`) has `|h| ≤ 1` and `|u − h| ≤ 2δ`.
* `taylorPoly k h` and `taylor_approx`: the degree-`k` caloric Taylor polynomial
  of a smooth caloric `h` at the origin, with `src = 0`, a coefficient bound, and the error bound
  `|h − taylorPoly k h| ≤ C ρ^{k+1}` on `cCyl 0 0 ρ` (`ρ ≤ 1/2`), from the Taylor bounds
  `IsSmoothCaloricOn.taylor0_le`, `taylor1_le`, `taylor2_le`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace ParabolicBasic

variable {d : ℕ}

/-! ### Approximation by a caloric function -/

/-- A bound on a set passes to the closure for a function continuous on the closure. -/
theorem abs_le_on_closure {s : Set (E d × ℝ)} {f : E d × ℝ → ℝ} (hf : ContinuousOn f (closure s))
    {M : ℝ} (h : ∀ q ∈ s, |f q| ≤ M) : ∀ q ∈ closure s, |f q| ≤ M := by
  intro q hq
  have h1 := (continuous_abs.comp_continuousOn hf).image_closure (mem_image_of_mem _ hq)
  have h2 : closure ((fun q ↦ |f q|) '' s) ⊆ Iic M :=
    closure_minimal (by rintro _ ⟨q, hq, rfl⟩; exact h q hq) isClosed_Iic
  exact h2 h1

/-- The parabolic boundary of `Q₁` lies in its closure. -/
theorem parBdry_subset_closure_cCyl_one :
    parBdry (ball (0 : E d) 1) (0 - 1 ^ 2) (0 + 1 ^ 2) ⊆ closure (cCyl (0 : E d) 0 1) := by
  rw [closure_cCyl (0 : E d) 0 one_pos, ← closure_ball (0 : E d) one_ne_zero]
  exact parBdry_subset_closure _ (by norm_num)

/-- **Caloric approximation, comparison part.** If `u` solves `dₜu − lapₓu = H` on `Q₁` with
`|H| ≤ δ` and `h` is smooth caloric on `Q₁`, continuous on `closure Q₁`, with the same values on the
parabolic boundary, then `|u − h| ≤ 2δ` on `closure Q₁`. -/
theorem abs_sub_caloric_le {u H h : E d × ℝ → ℝ} {δ : ℝ}
    (hu : ContinuousOn u (closure (cCyl (0 : E d) 0 1)))
    (hsol : IsHeatSolOn (cCyl (0 : E d) 0 1) H u) (hH : ∀ q ∈ cCyl (0 : E d) 0 1, |H q| ≤ δ)
    (hh : ContinuousOn h (closure (cCyl (0 : E d) 0 1)))
    (hcal : IsSmoothCaloricOn (cCyl (0 : E d) 0 1) h)
    (hbd : EqOn h u (parBdry (ball (0 : E d) 1) (0 - 1 ^ 2) (0 + 1 ^ 2))) :
    ∀ q ∈ closure (cCyl (0 : E d) 0 1), |u q - h q| ≤ 2 * δ := by
  have hO := isOpen_cCyl (0 : E d) 0 1
  have h2 : ContDiffOn ℝ 2 h (cCyl (0 : E d) 0 1) := hcal.1.of_le (WithTop.coe_le_coe.2 le_top)
  have hhsub : IsViscSubOn (cCyl (0 : E d) 0 1) (fun _ _ ↦ -(0 : ℝ)) h :=
    isViscSubOn_of_contDiffOn hO h2 fun p hp ↦ by rw [hcal.2 p hp]; simp
  have hhsuper : IsViscSuperOn (cCyl (0 : E d) 0 1) (fun _ _ ↦ -(0 : ℝ)) h :=
    isViscSuperOn_of_contDiffOn hO h2 fun p hp ↦ by rw [hcal.2 p hp]; simp
  have key := abs_sub_le_of_heat_source_cCyl (0 : E d) 0 one_pos (c := 0) (δ := δ) hu hh hsol.1
    hsol.2 hhsub hhsuper (fun p hp ↦ by simpa using hH p hp) (fun p hp ↦ (hbd hp).symm)
  intro q hq
  simpa using key q hq

/-- **Caloric approximation.** Let `u` be continuous on `closure Q₁`, a solution of
`dₜu − lapₓu = H` on `Q₁` with `|H| ≤ δ` and `|u| ≤ 1` there. The solution `h` of the heat Dirichlet
problem with data `u` on the parabolic boundary is smooth caloric on `Q₁`, `|h| ≤ 1`, and
`|u − h| ≤ 2δ` on `closure Q₁`. -/
theorem exists_caloric_approx {u H : E d × ℝ → ℝ} {δ : ℝ}
    (hu : ContinuousOn u (closure (cCyl (0 : E d) 0 1)))
    (hsol : IsHeatSolOn (cCyl (0 : E d) 0 1) H u) (hH : ∀ q ∈ cCyl (0 : E d) 0 1, |H q| ≤ δ)
    (hu1 : ∀ q ∈ cCyl (0 : E d) 0 1, |u q| ≤ 1) :
    ∃ h : E d × ℝ → ℝ, IsSmoothCaloricOn (cCyl (0 : E d) 0 1) h ∧
      (∀ q ∈ closure (cCyl (0 : E d) 0 1), |h q| ≤ 1) ∧
      ∀ q ∈ closure (cCyl (0 : E d) 0 1), |u q - h q| ≤ 2 * δ := by
  have hPB := parBdry_subset_closure_cCyl_one (d := d)
  have hu1' := abs_le_on_closure hu hu1
  obtain ⟨h, hhc, hcal, heq, hhb⟩ := caloric_dirichlet_cCyl (0 : E d) 0 one_pos (hu.mono hPB)
    (M := 1) fun q hq ↦ hu1' q (hPB hq)
  rw [← closure_cCyl (0 : E d) 0 one_pos] at hhc hhb
  exact ⟨h, hcal, hhb, abs_sub_caloric_le hu hsol hH hhc hcal heq⟩

/-! ### Caloric Taylor polynomials -/

/-- The (symmetrized) spatial Hessian matrix of `h` at the origin,
`Mᵢⱼ = (D²ₓh(0)[eᵢ, eⱼ] + D²ₓh(0)[eⱼ, eᵢ]) / 2`. For `C²` functions the symmetrization changes
nothing; it makes `M` symmetric by construction. -/
noncomputable def hessMat (h : E d × ℝ → ℝ) : Matrix (Fin d) (Fin d) ℝ := fun i j ↦
  (hessₓ h 0 ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] +
    hessₓ h 0 ![EuclideanSpace.single j 1, EuclideanSpace.single i 1]) / 2

theorem hessMat_isSymm (h : E d × ℝ → ℝ) : (hessMat h).IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ by simp only [hessMat]; ring

/-- The degree-`k` caloric Taylor polynomial of `h` at the origin:
`(h 0, 0, 0, 0)`, `(h 0, ∇ₓh 0, 0, 0)`, `(h 0, ∇ₓh 0, ∂ₜh 0, D²ₓh 0)` for `k = 0, 1, ≥ 2`. -/
noncomputable def taylorPoly (k : ℕ) (h : E d × ℝ → ℝ) : CaloricPoly d :=
  match k with
  | 0 => ⟨h 0, 0, 0, 0, Matrix.isSymm_zero⟩
  | 1 => ⟨h 0, gradₓ h 0, 0, 0, Matrix.isSymm_zero⟩
  | _ + 2 => ⟨h 0, gradₓ h 0, dₜ h 0, hessMat h, hessMat_isSymm h⟩

private theorem sum_symmetrize (a : Fin d → Fin d → ℝ) (v : Fin d → ℝ) :
    ∑ i, ∑ j, (a i j + a j i) / 2 * v i * v j = ∑ i, ∑ j, v i * v j * a i j := by
  have e1 : ∑ i, ∑ j, (a i j + a j i) / 2 * v i * v j =
      ∑ i, ∑ j, a i j * v i * v j / 2 + ∑ i, ∑ j, a j i * v i * v j / 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have e2 : ∑ i, ∑ j, a j i * v i * v j / 2 = ∑ i, ∑ j, a i j * v j * v i / 2 :=
    Finset.sum_comm
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Caloric Taylor approximation.** There is `C ≥ 0` (depending only on `d`) such that for `h`
smooth caloric on `Q₁` with `|h| ≤ 1` and `k ≤ 2`: `taylorPoly k h` has degree `≤ k`, `src = 0`,
coefficient norm `≤ C`, and `|h q − taylorPoly k h q| ≤ C ρ^{k+1}` on `cCyl 0 0 ρ`, `0 < ρ ≤ 1/2`.
-/
theorem taylor_approx : ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 2, ∀ {h : E d × ℝ → ℝ},
    IsSmoothCaloricOn (cCyl (0 : E d) 0 1) h → (∀ q ∈ cCyl (0 : E d) 0 1, |h q| ≤ 1) →
    (taylorPoly k h).IsDegLE k ∧ (taylorPoly k h).src = 0 ∧ (taylorPoly k h).coeffNorm ≤ C ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 → ∀ q ∈ cCyl (0 : E d) 0 ρ,
        |h q - (taylorPoly k h).eval q| ≤ C * ρ ^ (k + 1) := by
  obtain ⟨C0, hC0, hT0⟩ := IsSmoothCaloricOn.taylor0_le (d := d)
  obtain ⟨C1, hC1, hT1⟩ := IsSmoothCaloricOn.taylor1_le (d := d)
  obtain ⟨C2, hC2, hT2⟩ := IsSmoothCaloricOn.taylor2_le (d := d)
  obtain ⟨Cg, hCg, hG⟩ := IsSmoothCaloricOn.norm_gradₓ_le_of_cCyl (d := d)
  obtain ⟨Ct, hCt, hTt⟩ := IsSmoothCaloricOn.abs_dₜ_le_of_cCyl (d := d)
  obtain ⟨Ch, hCh, hHs⟩ := IsSmoothCaloricOn.abs_hessₓ_le_of_cCyl (d := d)
  set C := 1 + C0 + C1 + C2 + Cg + Ct + (d : ℝ) * d * Ch with hC
  have hdd : 0 ≤ (d : ℝ) * d * Ch := by positivity
  refine ⟨C, by positivity, fun k hk {h} hcal hh1 ↦ ?_⟩
  have hO := isOpen_cCyl (0 : E d) 0 1
  have e0 : ((0 : E d), (0 : ℝ)) = (0 : E d × ℝ) := rfl
  have hmem0 : (0 : E d × ℝ) ∈ cCyl (0 : E d) 0 1 := center_mem_cCyl (0 : E d) 0 one_pos
  have hC2at : ContDiffAt ℝ 2 h 0 :=
    (hcal.1.contDiffAt (hO.mem_nhds hmem0)).of_le (WithTop.coe_le_coe.2 le_top)
  have hh0 : |h 0| ≤ 1 := hh1 0 hmem0
  have hg : ‖gradₓ h 0‖ ≤ Cg := by
    simpa [Prod.mk_zero_zero] using hG hO one_pos subset_rfl hcal hh1
  have ht : |dₜ h 0| ≤ Ct := by
    simpa [Prod.mk_zero_zero] using hTt hO one_pos subset_rfl hcal hh1
  have hM : ∀ i j, |hessMat h i j| ≤ Ch := fun i j ↦ by
    have a := hHs hO one_pos subset_rfl hcal hh1 i j
    have b := hHs hO one_pos subset_rfl hcal hh1 j i
    simp only [mul_one, one_pow, div_one] at a b
    rw [e0] at a b
    simp only [hessMat, abs_div, abs_two]
    rw [div_le_iff₀ two_pos]
    linarith [abs_add_le (hessₓ h 0 ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
      (hessₓ h 0 ![EuclideanSpace.single j 1, EuclideanSpace.single i 1])]
  have hMsum : ∑ i, ∑ j, |hessMat h i j| ≤ (d : ℝ) * d * Ch := by
    calc ∑ i, ∑ j, |hessMat h i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, Ch :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hM i j
      _ = (d : ℝ) * d * Ch := by simp [Finset.sum_const]; ring
  -- the Hessian entries in partials
  have hMp : ∀ i j, hessₓ h 0 ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      partialDeriv i.castSucc (partialDeriv j.castSucc h) 0 := fun i j ↦
    iteratedFDeriv_two_sliceX_single hC2at i j
  interval_cases k
  · -- degree 0
    refine ⟨⟨rfl, rfl, rfl⟩, by simp [taylorPoly, CaloricPoly.src], ?_, fun ρ hρ hρ2 q hq ↦ ?_⟩
    · simp only [taylorPoly, CaloricPoly.coeffNorm, norm_zero, abs_zero, add_zero,
        Matrix.zero_apply, Finset.sum_const_zero]
      linarith
    · have a := hT0 hO subset_rfl hcal hh1 hρ (by linarith) q hq
      rw [e0] at a
      have hev : (taylorPoly 0 h).eval q = h 0 := by
        simp [taylorPoly, CaloricPoly.eval]
      rw [hev]
      calc |h q - h 0| ≤ C0 * 1 * (ρ / 1) := a
        _ = C0 * ρ ^ (0 + 1) := by ring
        _ ≤ C * ρ ^ (0 + 1) := by gcongr; linarith
  · -- degree 1
    refine ⟨⟨rfl, rfl⟩, by simp [taylorPoly, CaloricPoly.src], ?_, fun ρ hρ hρ2 q hq ↦ ?_⟩
    · simp only [taylorPoly, CaloricPoly.coeffNorm, abs_zero, add_zero,
        Matrix.zero_apply, Finset.sum_const_zero]
      linarith
    · have a := hT1 hO subset_rfl hcal hh1 hρ (by linarith) q hq
      rw [e0] at a
      have hev : (taylorPoly 1 h).eval q = caloricTaylor1 h 0 q := by
        simp [taylorPoly, CaloricPoly.eval, caloricTaylor1]
      rw [hev]
      calc _ ≤ C1 * 1 * (ρ / 1) ^ 2 := a
        _ = C1 * ρ ^ (1 + 1) := by ring
        _ ≤ C * ρ ^ (1 + 1) := by gcongr; linarith
  · -- degree 2
    refine ⟨trivial, ?_, ?_, fun ρ hρ hρ2 q hq ↦ ?_⟩
    · have hlap := lapₓ_eq_sum_partialDeriv_of_contDiffAt hC2at
      have hdt := hcal.2 0 hmem0
      simp only [taylorPoly, CaloricPoly.src, Matrix.trace, Matrix.diag, hessMat, hMp]
      rw [hdt, hlap]
      simp
    · simp only [taylorPoly, CaloricPoly.coeffNorm]
      linarith
    · have a := hT2 hO subset_rfl hcal hh1 hρ (by linarith) q hq
      rw [e0] at a
      have hq2 : hessₓ h 0 ![q.1, q.1] = ∑ i, ∑ j, hessMat h i j * q.1 i * q.1 j := by
        rw [hessₓ_apply_eq_sum hC2at]
        simp only [hessMat, hMp]
        rw [sum_symmetrize (fun i j ↦ partialDeriv i.castSucc (partialDeriv j.castSucc h) 0)]
      have hev : (taylorPoly 2 h).eval q = caloricTaylor2 h 0 q := by
        simp only [taylorPoly, CaloricPoly.eval, caloricTaylor2, caloricTaylor1,
          Prod.fst_zero, Prod.snd_zero, sub_zero, hq2]
      rw [hev]
      calc _ ≤ C2 * 1 * (ρ / 1) ^ 3 := a
        _ = C2 * ρ ^ (2 + 1) := by ring
        _ ≤ C * ρ ^ (2 + 1) := by gcongr; linarith

end ParabolicBasic
