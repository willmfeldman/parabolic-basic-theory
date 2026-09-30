/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Poly

/-!
# Coefficient extraction and the two-expansion comparison

* `CaloricPoly.coeff_bound`: if `|P| ≤ ε` on `cCyl 0 0 r`, then `|a| ≤ ε`, `|bᵢ| ≤ 2ε/r`,
  `‖b‖ ≤ 2√d ε/r`, `|c| ≤ 4ε/r²`, `|Mᵢᵢ| ≤ 16ε/r²`, `|Mᵢⱼ| ≤ 48ε/r²` (explicit finite differences
  at interior points).
* `CaloricPoly.eq_zero_of_abs_eval_le`: a polynomial of degree `≤ k` which is
  `O(pdist^{k+α})` at the origin vanishes (uniqueness of expansions).
* `CaloricPoly.two_expansions`: two order-`k+α` expansions of the same function at points at
  parabolic distance `δ < ρ₀/3` differ, after recentering, by at most `9Aδ^{k+α}` on
  `cCyl 0 0 δ` (factor `2^{k+α} + 1 ≤ 9`); `two_expansions_coeff` extracts the
  coefficient bounds.
-/

@[expose] public section

open Set Filter Topology
open scoped RealInnerProductSpace

namespace ParabolicBasic

variable {d : ℕ}

namespace CaloricPoly

/-- **Coefficient extraction.** -/
theorem coeff_bound {P : CaloricPoly d} {r ε : ℝ} (hr : 0 < r)
    (h : ∀ q ∈ cCyl 0 0 r, |P.eval q| ≤ ε) :
    |P.a| ≤ ε ∧ (∀ i, |P.b i| ≤ 2 * ε / r) ∧ ‖P.b‖ ≤ 2 * Real.sqrt d * ε / r ∧
      |P.c| ≤ 4 * ε / r ^ 2 ∧ (∀ i, |P.M i i| ≤ 16 * ε / r ^ 2) ∧
      ∀ i j, |P.M i j| ≤ 48 * ε / r ^ 2 := by
  have hmem : ∀ q : E d × ℝ, pdist q 0 < r → |P.eval q| ≤ ε := fun q hq ↦ h q (mem_cCyl_iff.2 hq)
  -- the constant term
  have ha : |P.a| ≤ ε := by
    have := hmem 0 (by simp [hr]); rwa [eval_zero_point] at this
  have hε : 0 ≤ ε := (abs_nonneg _).trans ha
  have hA := abs_le.1 ha
  -- the time coefficient
  have hc : |P.c| ≤ 4 * ε / r ^ 2 := by
    have hq : pdist ((0 : E d), r ^ 2 / 2) 0 < r := by
      simp only [pdist, Prod.fst_zero, Prod.snd_zero, sub_zero, norm_zero, max_lt_iff]
      refine ⟨hr, ?_⟩
      rw [Real.sqrt_lt' hr, abs_of_pos (by positivity)]
      nlinarith [sq_pos_of_pos hr]
    have h1 := abs_le.1 (hmem _ hq)
    have heval : P.eval ((0 : E d), r ^ 2 / 2) = P.a + P.c * (r ^ 2 / 2) := by simp [eval]
    rw [heval] at h1
    rw [le_div_iff₀ (by positivity), ← abs_of_pos (by positivity : (0 : ℝ) < r ^ 2), ← abs_mul,
      abs_le]
    constructor <;> nlinarith
  -- spatial second differences along `v`, `‖v‖ ≤ 1`, with step `r / 2`
  have hsp : ∀ v : E d, ‖v‖ ≤ 1 →
      |bilin P.M v v| ≤ 16 * ε / r ^ 2 ∧ |⟪P.b, v⟫| ≤ 2 * ε / r := by
    intro v hv
    set η := r / 2 with hη
    have hη0 : 0 < η := by positivity
    have hq : ∀ σ : ℝ, |σ| = 1 → pdist ((σ * η) • v, (0 : ℝ)) 0 < r := by
      intro σ hσ
      simp only [pdist, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_zero, Real.sqrt_zero,
        norm_smul, Real.norm_eq_abs, abs_mul, hσ, abs_of_pos hη0, one_mul]
      rw [max_lt_iff]
      refine ⟨?_, hr⟩
      calc η * ‖v‖ ≤ η * 1 := by gcongr
        _ < r := by rw [hη]; linarith
    have e : ∀ σ : ℝ, P.eval ((σ * η) • v, (0 : ℝ)) =
        P.a + σ * η * ⟪P.b, v⟫ + (1 / 2) * (σ * η) ^ 2 * bilin P.M v v := by
      intro σ
      simp only [eval_eq_bilin, real_inner_smul_right, map_smul, smul_apply,
        smul_eq_mul, mul_zero, add_zero]
      ring
    have h1 := abs_le.1 (hmem _ (hq 1 (by simp)))
    have h2 := abs_le.1 (hmem _ (hq (-1) (by simp)))
    rw [e] at h1 h2
    constructor
    · rw [show 16 * ε / r ^ 2 = 4 * ε / η ^ 2 by rw [hη]; field_simp; ring,
        le_div_iff₀ (by positivity), ← abs_of_pos (by positivity : (0 : ℝ) < η ^ 2), ← abs_mul,
        abs_le]
      constructor <;> nlinarith
    · rw [show 2 * ε / r = ε / η by rw [hη]; ring,
        le_div_iff₀ hη0, ← abs_of_pos hη0, ← abs_mul, abs_le]
      constructor <;> nlinarith
  have he : ∀ i, ‖(EuclideanSpace.single i (1 : ℝ) : E d)‖ = 1 := fun i ↦ by
    rw [PiLp.norm_single]; simp
  have hb : ∀ i, |P.b i| ≤ 2 * ε / r := fun i ↦ by
    have := (hsp _ (he i).le).2
    rwa [EuclideanSpace.inner_single_right, one_mul] at this
  have hMii : ∀ i, |P.M i i| ≤ 16 * ε / r ^ 2 := fun i ↦ by
    have := (hsp _ (he i).le).1
    rwa [bilin_single] at this
  have hMij : ∀ i j, |P.M i j| ≤ 48 * ε / r ^ 2 := by
    intro i j
    set v : E d := (1 / 2 : ℝ) • (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
    have hv : ‖v‖ ≤ 1 := by
      calc ‖v‖ = 1 / 2 * ‖EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        _ ≤ 1 / 2 * (1 + 1) := by
            gcongr; exact (norm_add_le _ _).trans (by rw [he, he])
        _ = 1 := by norm_num
    have hB : bilin P.M v v = (1 / 4) * (P.M i i + 2 * P.M i j + P.M j j) := by
      simp only [v, map_smul, map_add, smul_apply,
        add_apply, bilin_single, smul_eq_mul, P.symm.apply i j]
      ring
    have key : P.M i j = 2 * bilin P.M v v - (P.M i i + P.M j j) / 2 := by rw [hB]; ring
    have h1 := (hsp v hv).1
    have h2 := hMii i
    have h3 := hMii j
    rw [key]
    calc |2 * bilin P.M v v - (P.M i i + P.M j j) / 2|
        ≤ |2 * bilin P.M v v| + |(P.M i i + P.M j j) / 2| := abs_sub _ _
      _ ≤ 2 * |bilin P.M v v| + (|P.M i i| + |P.M j j|) / 2 := by
          rw [abs_mul, abs_two, abs_div, abs_two]
          gcongr
          exact abs_add_le _ _
      _ ≤ 2 * (16 * ε / r ^ 2) + (16 * ε / r ^ 2 + 16 * ε / r ^ 2) / 2 := by gcongr
      _ = 48 * ε / r ^ 2 := by ring
  have hbn : ‖P.b‖ ≤ 2 * Real.sqrt d * ε / r := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i, ‖P.b i‖ ^ 2 ≤ d * (2 * ε / r) ^ 2 := by
      calc ∑ i, ‖P.b i‖ ^ 2 ≤ ∑ _i : Fin d, (2 * ε / r) ^ 2 :=
            Finset.sum_le_sum fun i _ ↦ by
              rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
        _ = d * (2 * ε / r) ^ 2 := by simp
    calc Real.sqrt (∑ i, ‖P.b i‖ ^ 2) ≤ Real.sqrt (d * (2 * ε / r) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt d * (2 * ε / r) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by positivity)]
      _ = 2 * Real.sqrt d * ε / r := by ring
  exact ⟨ha, hb, hbn, hc, hMii, hMij⟩

/-- `coeff_bound` with `ε = K r^γ`, in `rpow` form. -/
theorem coeff_bound_rpow {P : CaloricPoly d} {r K γ : ℝ} (hr : 0 < r)
    (h : ∀ q ∈ cCyl 0 0 r, |P.eval q| ≤ K * r ^ γ) :
    |P.a| ≤ K * r ^ γ ∧ (∀ i, |P.b i| ≤ 2 * K * r ^ (γ - 1)) ∧
      ‖P.b‖ ≤ 2 * Real.sqrt d * K * r ^ (γ - 1) ∧ |P.c| ≤ 4 * K * r ^ (γ - 2) ∧
      ∀ i j, |P.M i j| ≤ 48 * K * r ^ (γ - 2) := by
  obtain ⟨ha, hb, hbn, hc, -, hM⟩ := coeff_bound hr h
  have e1 : r ^ (γ - 1) = r ^ γ / r := by rw [Real.rpow_sub hr, Real.rpow_one]
  have e2 : r ^ (γ - 2) = r ^ γ / r ^ 2 := by rw [Real.rpow_sub hr, Real.rpow_two]
  refine ⟨ha, fun i ↦ (hb i).trans_eq ?_, hbn.trans_eq ?_, hc.trans_eq ?_,
    fun i j ↦ (hM i j).trans_eq ?_⟩
  all_goals first | (rw [e1]; ring) | (rw [e2]; ring)

/-- The coefficient norm under the hypothesis of `coeff_bound`. -/
theorem coeffNorm_le_of_bound {P : CaloricPoly d} {r ε : ℝ} (hr : 0 < r)
    (h : ∀ q ∈ cCyl 0 0 r, |P.eval q| ≤ ε) :
    P.coeffNorm ≤ ε * (1 + 2 * Real.sqrt d / r + (4 + 48 * d ^ 2) / r ^ 2) := by
  obtain ⟨ha, -, hb, hc, -, hM⟩ := coeff_bound hr h
  have hS : ∑ i, ∑ j, |P.M i j| ≤ d ^ 2 * (48 * ε / r ^ 2) := by
    calc ∑ i, ∑ j, |P.M i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, 48 * ε / r ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hM i j
      _ = _ := by simp; ring
  have heq : ε * (1 + 2 * Real.sqrt d / r + (4 + 48 * d ^ 2) / r ^ 2) =
      ε + 2 * Real.sqrt d * ε / r + 4 * ε / r ^ 2 + d ^ 2 * (48 * ε / r ^ 2) := by
    field_simp; ring
  rw [heq, coeffNorm]
  linarith

/-- `d = 0`: `coeff_bound` still applies (all spatial sums are empty). -/
example {P : CaloricPoly 0} {r ε : ℝ} (hr : 0 < r) (h : ∀ q ∈ cCyl 0 0 r, |P.eval q| ≤ ε) :
    |P.a| ≤ ε ∧ |P.c| ≤ 4 * ε / r ^ 2 :=
  ⟨(coeff_bound hr h).1, (coeff_bound hr h).2.2.2.1⟩

/-- **Uniqueness of expansions.** A polynomial of degree `≤ k` (`k ≤ 2`) with
`|P q| ≤ A pdist(q, 0)^{k+α}` near the origin (`α > 0`) is zero. -/
theorem eq_zero_of_abs_eval_le {P : CaloricPoly d} {k : ℕ} {α A ρ : ℝ} (hP : P.IsDegLE k)
    (hk : k ≤ 2) (hα : 0 < α) (hρ : 0 < ρ)
    (h : ∀ q, pdist q 0 < ρ → |P.eval q| ≤ A * pdist q 0 ^ ((k : ℝ) + α)) : P = 0 := by
  set γ : ℝ := (k : ℝ) + α with hγ
  have hγ0 : 0 < γ := by positivity
  have hbd : ∀ r, 0 < r → r ≤ ρ → ∀ q ∈ cCyl 0 0 r, |P.eval q| ≤ max A 0 * r ^ γ := by
    intro r hr hrρ q hq
    have hq' : pdist q 0 < r := mem_cCyl_iff.1 hq
    refine (h q (hq'.trans_le hrρ)).trans ?_
    calc A * pdist q 0 ^ γ ≤ max A 0 * pdist q 0 ^ γ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (pdist_nonneg _ _) _)
      _ ≤ max A 0 * r ^ γ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pdist_nonneg _ _) hq'.le hγ0.le)
            (le_max_right _ _)
  have ha : P.a = 0 := by
    have := h 0 (by simp [hρ])
    simpa [Real.zero_rpow hγ0.ne'] using this
  have lim : ∀ x K γ' : ℝ, 0 < γ' → (∀ r, 0 < r → r ≤ ρ → |x| ≤ K * r ^ γ') → x = 0 := by
    intro x K γ' hγ' hx
    by_contra hne
    have hxpos : 0 < |x| := abs_pos.2 hne
    have ht : Tendsto (fun r : ℝ ↦ K * r ^ γ') (𝓝[>] 0) (𝓝 0) := by
      have : ContinuousAt (fun r : ℝ ↦ K * r ^ γ') 0 :=
        continuousAt_const.mul (Real.continuousAt_rpow_const 0 γ' (Or.inr hγ'.le))
      simpa [Real.zero_rpow hγ'.ne'] using this.tendsto.mono_left nhdsWithin_le_nhds
    obtain ⟨r, hr1, hr2⟩ := ((ht.eventually (gt_mem_nhds hxpos)).and (Ioc_mem_nhdsGT hρ)).exists
    exact absurd (hx r hr2.1 hr2.2) (not_le.2 hr1)
  have hk1 : ∀ i, 1 ≤ k → P.b i = 0 := fun i hk1 ↦ by
    refine lim _ (2 * max A 0) (γ - 1) ?_
      fun r hr hrρ ↦ (coeff_bound_rpow hr (hbd r hr hrρ)).2.1 i
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  have hk2c : 2 ≤ k → P.c = 0 := fun hk2 ↦ by
    refine lim _ (4 * max A 0) (γ - 2) ?_
      fun r hr hrρ ↦ (coeff_bound_rpow hr (hbd r hr hrρ)).2.2.2.1
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hk2M : ∀ i j, 2 ≤ k → P.M i j = 0 := fun i j hk2 ↦ by
    refine lim _ (48 * max A 0) (γ - 2) ?_
      fun r hr hrρ ↦ (coeff_bound_rpow hr (hbd r hr hrρ)).2.2.2.2 i j
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  rcases k with _ | _ | k
  · exact CaloricPoly.ext ha hP.1 hP.2.1 hP.2.2
  · exact CaloricPoly.ext ha (PiLp.ext fun i ↦ hk1 i le_rfl) hP.1 hP.2
  · exact CaloricPoly.ext ha (PiLp.ext fun i ↦ hk1 i (by omega)) (hk2c (by omega))
      (Matrix.ext fun i j ↦ hk2M i j (by omega))

/-- **Two expansions** (with the factor `9`). -/
theorem two_expansions {k : ℕ} {α A ρ₀ : ℝ} {u : E d × ℝ → ℝ} {P Q : CaloricPoly d}
    {p p' : E d × ℝ} (hk : k ≤ 2) (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A)
    (hP : ∀ q, pdist q p < ρ₀ → |u q - P.eval (q - p)| ≤ A * pdist q p ^ ((k : ℝ) + α))
    (hQ : ∀ q, pdist q p' < ρ₀ → |u q - Q.eval (q - p')| ≤ A * pdist q p' ^ ((k : ℝ) + α))
    (hδ : pdist p p' < ρ₀ / 3) :
    ∀ z ∈ cCyl 0 0 (pdist p p'),
      |(P.recenter (p' - p)).eval z - Q.eval z| ≤ 9 * A * pdist p p' ^ ((k : ℝ) + α) := by
  intro z hz
  set δ := pdist p p'
  set γ : ℝ := (k : ℝ) + α with hγ
  have hγ0 : 0 ≤ γ := by have := hα.1; positivity
  have hγ3 : γ ≤ 3 := by
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    linarith [hα.2]
  have hδ0 : 0 ≤ δ := pdist_nonneg _ _
  have hz' : pdist z 0 < δ := mem_cCyl_iff.1 hz
  set q := z + p' with hq
  have hq' : pdist q p' = pdist z 0 := by rw [← pdist_add_right z 0 p', zero_add]
  have hqp : pdist q p ≤ 2 * δ := by
    calc pdist q p ≤ pdist q p' + pdist p' p := pdist_triangle _ _ _
      _ ≤ δ + δ := by rw [pdist_comm p' p, hq']; linarith
      _ = 2 * δ := by ring
  have e1 := hP q (by linarith)
  have e2 := hQ q (by rw [hq']; linarith)
  have hqp' : q - p' = z := by rw [hq]; abel
  have hqp2 : q - p = z + (p' - p) := by rw [hq]; abel
  rw [hqp'] at e2
  rw [hqp2] at e1
  rw [recenter_eval]
  have hpow1 : pdist q p ^ γ ≤ (2 * δ) ^ γ := Real.rpow_le_rpow (pdist_nonneg _ _) hqp hγ0
  have hpow2 : pdist q p' ^ γ ≤ δ ^ γ :=
    Real.rpow_le_rpow (pdist_nonneg _ _) (by rw [hq']; exact hz'.le) hγ0
  have h2γ : (2 * δ) ^ γ ≤ 8 * δ ^ γ := by
    rw [Real.mul_rpow (by norm_num) hδ0]
    gcongr
    calc (2 : ℝ) ^ γ ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ3
      _ = 8 := by rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]; norm_num
  calc |P.eval (z + (p' - p)) - Q.eval z|
      ≤ |u q - P.eval (z + (p' - p))| + |u q - Q.eval z| := by
        have := abs_sub_le (P.eval (z + (p' - p))) (u q) (Q.eval z)
        rwa [abs_sub_comm (P.eval (z + (p' - p))) (u q)] at this
    _ ≤ A * pdist q p ^ γ + A * pdist q p' ^ γ := add_le_add e1 e2
    _ ≤ A * (8 * δ ^ γ) + A * δ ^ γ := by gcongr; exact hpow1.trans h2γ
    _ = 9 * A * δ ^ γ := by ring

/-- **Two expansions, coefficient form**: with `δ := pdist p p' ∈ (0, ρ₀/3)`,
`|P(p'-p) - a'| ≤ 9Aδ^{k+α}`, `|(b + M(p'-p)₁ - b')ᵢ| ≤ 18Aδ^{k+α-1}`,
`‖b + M(p'-p)₁ - b'‖ ≤ 18√d Aδ^{k+α-1}`, `|c - c'| ≤ 36Aδ^{k+α-2}`,
`|Mᵢⱼ - M'ᵢⱼ| ≤ 432Aδ^{k+α-2}`. -/
theorem two_expansions_coeff {k : ℕ} {α A ρ₀ : ℝ} {u : E d × ℝ → ℝ} {P Q : CaloricPoly d}
    {p p' : E d × ℝ} (hk : k ≤ 2) (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A)
    (hP : ∀ q, pdist q p < ρ₀ → |u q - P.eval (q - p)| ≤ A * pdist q p ^ ((k : ℝ) + α))
    (hQ : ∀ q, pdist q p' < ρ₀ → |u q - Q.eval (q - p')| ≤ A * pdist q p' ^ ((k : ℝ) + α))
    (hδ0 : 0 < pdist p p') (hδ : pdist p p' < ρ₀ / 3) :
    |P.eval (p' - p) - Q.a| ≤ 9 * A * pdist p p' ^ ((k : ℝ) + α) ∧
      (∀ i, |(P.b + Matrix.toEuclideanLin P.M (p' - p).1 - Q.b) i| ≤
        18 * A * pdist p p' ^ ((k : ℝ) + α - 1)) ∧
      ‖P.b + Matrix.toEuclideanLin P.M (p' - p).1 - Q.b‖ ≤
        18 * Real.sqrt d * A * pdist p p' ^ ((k : ℝ) + α - 1) ∧
      |P.c - Q.c| ≤ 36 * A * pdist p p' ^ ((k : ℝ) + α - 2) ∧
      ∀ i j, |P.M i j - Q.M i j| ≤ 432 * A * pdist p p' ^ ((k : ℝ) + α - 2) := by
  have hR := two_expansions hk hα hA hP hQ hδ
  have hR' : ∀ z ∈ cCyl 0 0 (pdist p p'),
      |(P.recenter (p' - p) - Q).eval z| ≤ (9 * A) * pdist p p' ^ ((k : ℝ) + α) := by
    intro z hz; rw [eval_sub]; exact hR z hz
  obtain ⟨ha, hb, hbn, hc, hM⟩ := coeff_bound_rpow hδ0 hR'
  simp only [sub_a, sub_b, sub_c, sub_M, recenter_a, recenter_b, recenter_c, recenter_M,
    Matrix.sub_apply] at ha hb hbn hc hM
  refine ⟨ha.trans_eq (by ring), fun i ↦ (hb i).trans_eq (by ring), hbn.trans_eq (by ring),
    hc.trans_eq (by ring), fun i j ↦ (hM i j).trans_eq (by ring)⟩

end CaloricPoly

end ParabolicBasic
