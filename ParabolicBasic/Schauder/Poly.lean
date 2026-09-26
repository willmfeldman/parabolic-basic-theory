/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ParabolicBasic.Schauder.Holder
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Caloric (parabolic-degree `≤ 2`) polynomials

A `CaloricPoly d` is a tuple `(a, b, c, M)` with `M` symmetric, evaluated as
`P (y, s) = a + ⟪b, y⟫ + c s + ½ ∑ᵢⱼ Mᵢⱼ yᵢ yⱼ`. It is an explicit structure, not an
`MvPolynomial`: we need evaluation, calculus and finite differences, never ring structure.

* `src P := c - tr M`, so `dₜ P - lapₓ P ≡ src P` (`dₜ_sub_lapₓ_eval`).
* `recenter P h` evaluates as `z ↦ P (z + h)`; `rescale P r λ` as `(y, s) ↦ P (r y, r² s) / λ`.
* `bilin M : E d →L[ℝ] E d →L[ℝ] ℝ`, `(v, w) ↦ ∑ᵢⱼ Mᵢⱼ vᵢ wⱼ`, with `‖bilin M‖ ≤ ∑ᵢⱼ |Mᵢⱼ|`.
* `coeffNorm P := |a| + ‖b‖ + |c| + ∑ᵢⱼ |Mᵢⱼ|`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian Gradient RealInnerProductSpace

namespace ParabolicBasic

variable {d : ℕ}

/-- A caloric polynomial of parabolic degree `≤ 2` on `E d × ℝ`:
`P (y, s) = a + ⟪b, y⟫ + c s + ½ yᵀ M y` with `M` symmetric. -/
@[ext]
structure CaloricPoly (d : ℕ) where
  /-- The constant term. -/
  a : ℝ
  /-- The spatial gradient at the origin. -/
  b : E d
  /-- The time derivative. -/
  c : ℝ
  /-- The spatial Hessian. -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- The Hessian is symmetric. -/
  symm : M.IsSymm

/-! ### Expansions of order `1 + β` give derivatives -/

/-- A remainder bounded by `A ‖x‖^{1+β}` near `0` (`β > 0`) is `o(x)`. -/
theorem isLittleO_of_abs_le_rpow {F : Type*} [NormedAddCommGroup F] {e : F → ℝ} {A ρ β : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (h : ∀ x : F, ‖x‖ < ρ → |e x| ≤ A * ‖x‖ ^ (1 + β)) :
    e =o[𝓝 0] fun x ↦ x := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have ht : Tendsto (fun x : F ↦ max A 0 * ‖x‖ ^ β) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun x : F ↦ max A 0 * ‖x‖ ^ β) :=
      continuous_const.mul (Continuous.rpow_const continuous_norm fun _ ↦ Or.inr hβ.le)
    simpa [Real.zero_rpow hβ.ne'] using this.tendsto 0
  filter_upwards [ht.eventually (gt_mem_nhds hc), Metric.ball_mem_nhds (0 : F) hρ] with x hx hxρ
  rw [mem_ball_zero_iff] at hxρ
  rw [Real.norm_eq_abs]
  have hxβ : 0 ≤ ‖x‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
  calc |e x| ≤ A * ‖x‖ ^ (1 + β) := h x hxρ
    _ ≤ max A 0 * ‖x‖ ^ (1 + β) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = (max A 0 * ‖x‖ ^ β) * ‖x‖ := by
      rw [Real.rpow_add' (norm_nonneg _) (by linarith), Real.rpow_one]; ring
    _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_right hx.le (norm_nonneg _)

/-- Single-point gradient identification: an expansion `|g (x + h) - g x - ⟪b, h⟫| ≤ A ‖h‖^{1+β}`
for `‖h‖ < ρ` (`β > 0`) gives `HasGradientAt g b x`. -/
theorem hasGradientAt_of_expansion1 {g : E d → ℝ} {x b : E d} {A ρ β : ℝ} (hρ : 0 < ρ)
    (hβ : 0 < β) (h : ∀ h : E d, ‖h‖ < ρ → |g (x + h) - g x - ⟪b, h⟫| ≤ A * ‖h‖ ^ (1 + β)) :
    HasGradientAt g b x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  refine isLittleO_of_abs_le_rpow (A := A) hρ hβ fun y hy ↦ ?_
  simpa [InnerProductSpace.toDual_apply_apply] using h y hy

/-- One-variable analogue: `|g (t + s) - g t - c s| ≤ A |s|^{1+β}` for `|s| < ρ` (`β > 0`) gives
the two-sided `HasDerivAt g c t`. -/
theorem hasDerivAt_of_expansion1 {g : ℝ → ℝ} {t c A ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (h : ∀ s : ℝ, |s| < ρ → |g (t + s) - g t - c * s| ≤ A * |s| ^ (1 + β)) :
    HasDerivAt g c t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine isLittleO_of_abs_le_rpow (A := A) hρ hβ fun s hs ↦ ?_
  rw [Real.norm_eq_abs] at hs ⊢
  rw [smul_eq_mul, mul_comm s c]
  exact h s hs

namespace CaloricPoly

/-! ### Evaluation and degree -/

/-- Evaluation `P (y, s) = a + ⟪b, y⟫ + c s + ½ ∑ᵢⱼ Mᵢⱼ yᵢ yⱼ`. -/
noncomputable def eval (P : CaloricPoly d) (q : E d × ℝ) : ℝ :=
  P.a + ⟪P.b, q.1⟫ + P.c * q.2 + (1 / 2) * ∑ i, ∑ j, P.M i j * q.1 i * q.1 j

/-- The source defect `c - tr M`: `P` is caloric iff `src P = 0`. -/
def src (P : CaloricPoly d) : ℝ := P.c - Matrix.trace P.M

/-- Degree `≤ 0`: `b = 0`, `c = 0`, `M = 0`. -/
def IsDeg0 (P : CaloricPoly d) : Prop := P.b = 0 ∧ P.c = 0 ∧ P.M = 0

/-- Degree `≤ 1`: `c = 0`, `M = 0`. -/
def IsDeg1 (P : CaloricPoly d) : Prop := P.c = 0 ∧ P.M = 0

/-- Parabolic degree `≤ k` (every `P` has degree `≤ 2`). -/
def IsDegLE (P : CaloricPoly d) : ℕ → Prop
  | 0 => P.IsDeg0
  | 1 => P.IsDeg1
  | _ + 2 => True

/-- The coefficient norm `|a| + ‖b‖ + |c| + ∑ᵢⱼ |Mᵢⱼ|`. -/
noncomputable def coeffNorm (P : CaloricPoly d) : ℝ :=
  |P.a| + ‖P.b‖ + |P.c| + ∑ i, ∑ j, |P.M i j|

/-! ### Coefficientwise operations -/

instance : Zero (CaloricPoly d) := ⟨⟨0, 0, 0, 0, Matrix.isSymm_zero⟩⟩

instance : Add (CaloricPoly d) :=
  ⟨fun P Q ↦ ⟨P.a + Q.a, P.b + Q.b, P.c + Q.c, P.M + Q.M, P.symm.add Q.symm⟩⟩

instance : Neg (CaloricPoly d) := ⟨fun P ↦ ⟨-P.a, -P.b, -P.c, -P.M, P.symm.neg⟩⟩

instance : Sub (CaloricPoly d) :=
  ⟨fun P Q ↦ ⟨P.a - Q.a, P.b - Q.b, P.c - Q.c, P.M - Q.M, P.symm.sub Q.symm⟩⟩

instance : SMul ℝ (CaloricPoly d) := ⟨fun r P ↦ ⟨r * P.a, r • P.b, r * P.c, r • P.M, P.symm.smul r⟩⟩

@[simp] theorem zero_a : (0 : CaloricPoly d).a = 0 := rfl
@[simp] theorem zero_b : (0 : CaloricPoly d).b = 0 := rfl
@[simp] theorem zero_c : (0 : CaloricPoly d).c = 0 := rfl
@[simp] theorem zero_M : (0 : CaloricPoly d).M = 0 := rfl
@[simp] theorem add_a (P Q : CaloricPoly d) : (P + Q).a = P.a + Q.a := rfl
@[simp] theorem add_b (P Q : CaloricPoly d) : (P + Q).b = P.b + Q.b := rfl
@[simp] theorem add_c (P Q : CaloricPoly d) : (P + Q).c = P.c + Q.c := rfl
@[simp] theorem add_M (P Q : CaloricPoly d) : (P + Q).M = P.M + Q.M := rfl
@[simp] theorem neg_a (P : CaloricPoly d) : (-P).a = -P.a := rfl
@[simp] theorem neg_b (P : CaloricPoly d) : (-P).b = -P.b := rfl
@[simp] theorem neg_c (P : CaloricPoly d) : (-P).c = -P.c := rfl
@[simp] theorem neg_M (P : CaloricPoly d) : (-P).M = -P.M := rfl
@[simp] theorem sub_a (P Q : CaloricPoly d) : (P - Q).a = P.a - Q.a := rfl
@[simp] theorem sub_b (P Q : CaloricPoly d) : (P - Q).b = P.b - Q.b := rfl
@[simp] theorem sub_c (P Q : CaloricPoly d) : (P - Q).c = P.c - Q.c := rfl
@[simp] theorem sub_M (P Q : CaloricPoly d) : (P - Q).M = P.M - Q.M := rfl
@[simp] theorem smul_a (r : ℝ) (P : CaloricPoly d) : (r • P).a = r * P.a := rfl
@[simp] theorem smul_b (r : ℝ) (P : CaloricPoly d) : (r • P).b = r • P.b := rfl
@[simp] theorem smul_c (r : ℝ) (P : CaloricPoly d) : (r • P).c = r * P.c := rfl
@[simp] theorem smul_M (r : ℝ) (P : CaloricPoly d) : (r • P).M = r • P.M := rfl

@[simp] theorem eval_zero (q : E d × ℝ) : (0 : CaloricPoly d).eval q = 0 := by
  simp [eval]

@[simp] theorem eval_add (P Q : CaloricPoly d) (q : E d × ℝ) :
    (P + Q).eval q = P.eval q + Q.eval q := by
  simp only [eval, add_a, add_b, add_c, add_M, inner_add_left, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

@[simp] theorem eval_neg (P : CaloricPoly d) (q : E d × ℝ) : (-P).eval q = -P.eval q := by
  simp only [eval, neg_a, neg_b, neg_c, neg_M, inner_neg_left, Matrix.neg_apply, neg_mul,
    Finset.sum_neg_distrib]
  ring

@[simp] theorem eval_sub (P Q : CaloricPoly d) (q : E d × ℝ) :
    (P - Q).eval q = P.eval q - Q.eval q := by
  simp only [eval, sub_a, sub_b, sub_c, sub_M, inner_sub_left, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]
  ring

@[simp] theorem eval_smul (r : ℝ) (P : CaloricPoly d) (q : E d × ℝ) :
    (r • P).eval q = r * P.eval q := by
  simp only [eval, smul_a, smul_b, smul_c, smul_M, real_inner_smul_left, Matrix.smul_apply,
    smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

@[simp] theorem eval_zero_point (P : CaloricPoly d) : P.eval 0 = P.a := by
  simp [eval]

theorem src_add (P Q : CaloricPoly d) : (P + Q).src = P.src + Q.src := by
  simp only [src, add_c, add_M, Matrix.trace_add]; ring

theorem src_sub (P Q : CaloricPoly d) : (P - Q).src = P.src - Q.src := by
  simp only [src, sub_c, sub_M, Matrix.trace_sub]; ring

@[simp] theorem src_zero : (0 : CaloricPoly d).src = 0 := by
  simp [src]

theorem coeffNorm_nonneg (P : CaloricPoly d) : 0 ≤ P.coeffNorm := by
  unfold coeffNorm; positivity

theorem coeffNorm_add_le (P Q : CaloricPoly d) : (P + Q).coeffNorm ≤ P.coeffNorm + Q.coeffNorm := by
  simp only [coeffNorm, add_a, add_b, add_c, add_M, Matrix.add_apply]
  have h1 := abs_add_le P.a Q.a
  have h2 := norm_add_le P.b Q.b
  have h3 := abs_add_le P.c Q.c
  have h4 : ∑ i, ∑ j, |P.M i j + Q.M i j| ≤ ∑ i, ∑ j, |P.M i j| + ∑ i, ∑ j, |Q.M i j| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ ↦ abs_add_le _ _
  linarith

/-! ### Degree -/

theorem isDegLE_two_add (P : CaloricPoly d) (k : ℕ) : P.IsDegLE (k + 2) := trivial

theorem IsDegLE.mono {P : CaloricPoly d} {k l : ℕ} (h : P.IsDegLE k) (hkl : k ≤ l) :
    P.IsDegLE l := by
  rcases k with _ | _ | k <;> rcases l with _ | _ | l
  all_goals first | exact trivial | exact h | omega | exact ⟨h.2.1, h.2.2⟩

theorem IsDegLE.add {P Q : CaloricPoly d} {k : ℕ} (hP : P.IsDegLE k) (hQ : Q.IsDegLE k) :
    (P + Q).IsDegLE k := by
  rcases k with _ | _ | k
  · obtain ⟨h1, h2, h3⟩ := hP; obtain ⟨h1', h2', h3'⟩ := hQ
    exact ⟨by simp [h1, h1'], by simp [h2, h2'], by simp [h3, h3']⟩
  · obtain ⟨h2, h3⟩ := hP; obtain ⟨h2', h3'⟩ := hQ
    exact ⟨by simp [h2, h2'], by simp [h3, h3']⟩
  · exact trivial

theorem IsDegLE.sub {P Q : CaloricPoly d} {k : ℕ} (hP : P.IsDegLE k) (hQ : Q.IsDegLE k) :
    (P - Q).IsDegLE k := by
  rcases k with _ | _ | k
  · obtain ⟨h1, h2, h3⟩ := hP; obtain ⟨h1', h2', h3'⟩ := hQ
    exact ⟨by simp [h1, h1'], by simp [h2, h2'], by simp [h3, h3']⟩
  · obtain ⟨h2, h3⟩ := hP; obtain ⟨h2', h3'⟩ := hQ
    exact ⟨by simp [h2, h2'], by simp [h3, h3']⟩
  · exact trivial

theorem isDegLE_zero : ∀ k, (0 : CaloricPoly d).IsDegLE k
  | 0 => ⟨rfl, rfl, rfl⟩
  | 1 => ⟨rfl, rfl⟩
  | _ + 2 => trivial

/-- Degree `≤ 1` polynomials are caloric. -/
theorem IsDegLE.src_eq_zero {P : CaloricPoly d} {k : ℕ} (hP : P.IsDegLE k) (hk : k ≤ 1) :
    P.src = 0 := by
  rcases k with _ | _ | k
  · simp [src, hP.2.1, hP.2.2]
  · simp [src, hP.1, hP.2]
  · omega

/-! ### The bilinear form of a matrix -/

/-- The continuous bilinear form `(v, w) ↦ ∑ᵢⱼ Mᵢⱼ vᵢ wⱼ` of a matrix. -/
noncomputable def bilin (M : Matrix (Fin d) (Fin d) ℝ) : E d →L[ℝ] E d →L[ℝ] ℝ :=
  ∑ i, ∑ j, M i j • (EuclideanSpace.proj i : E d →L[ℝ] ℝ).smulRight
    (EuclideanSpace.proj j : E d →L[ℝ] ℝ)

theorem bilin_apply (M : Matrix (Fin d) (Fin d) ℝ) (v w : E d) :
    bilin M v w = ∑ i, ∑ j, M i j * v i * w j := by
  simp [bilin, ContinuousLinearMap.sum_apply, mul_assoc]

theorem bilin_add (M M' : Matrix (Fin d) (Fin d) ℝ) : bilin (M + M') = bilin M + bilin M' := by
  simp [bilin, add_smul, Finset.sum_add_distrib]

theorem bilin_sub (M M' : Matrix (Fin d) (Fin d) ℝ) : bilin (M - M') = bilin M - bilin M' := by
  simp [bilin, sub_smul, Finset.sum_sub_distrib]

theorem bilin_smul (r : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : bilin (r • M) = r • bilin M := by
  simp [bilin, mul_smul, Finset.smul_sum]

theorem norm_bilin_le (M : Matrix (Fin d) (Fin d) ℝ) : ‖bilin M‖ ≤ ∑ i, ∑ j, |M i j| := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  rw [bilin_apply, Real.norm_eq_abs, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  have hv := PiLp.norm_apply_le v i
  have hw := PiLp.norm_apply_le w j
  rw [Real.norm_eq_abs] at hv hw
  rw [abs_mul, abs_mul]
  gcongr

theorem bilin_single (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    bilin M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = M i j := by
  simp [bilin_apply, PiLp.single_apply]

/-- Every continuous bilinear form on `E d` is `bilin` of its matrix on the standard basis. -/
theorem eq_bilin (T : E d →L[ℝ] E d →L[ℝ] ℝ) :
    T = bilin (Matrix.of fun i j ↦ T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  ext v w
  rw [bilin_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v,
    ← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, Matrix.of_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

theorem bilin_injective : Function.Injective (bilin (d := d)) := by
  intro M N h
  ext i j
  have := congrArg (fun T : E d →L[ℝ] E d →L[ℝ] ℝ ↦
    T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) h
  simpa [bilin_single] using this

theorem bilin_symm {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (v w : E d) :
    bilin M v w = bilin M w v := by
  rw [bilin_apply, bilin_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hM.apply]; ring

theorem toEuclideanLin_apply_coord (M : Matrix (Fin d) (Fin d) ℝ) (v : E d) (i : Fin d) :
    Matrix.toEuclideanLin M v i = ∑ j, M i j * v j := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

theorem inner_toEuclideanLin {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (v w : E d) :
    ⟪Matrix.toEuclideanLin M v, w⟫ = bilin M v w := by
  rw [bilin_symm hM, bilin_apply]
  simp only [PiLp.inner_apply, toEuclideanLin_apply_coord, RCLike.inner_apply, conj_trivial,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

theorem eval_eq_bilin (P : CaloricPoly d) (q : E d × ℝ) :
    P.eval q = P.a + ⟪P.b, q.1⟫ + P.c * q.2 + (1 / 2) * bilin P.M q.1 q.1 := by
  rw [eval, bilin_apply]

/-! ### Recentering and rescaling -/

/-- Recentering at `h`: `(P.recenter h).eval z = P.eval (z + h)`. -/
noncomputable def recenter (P : CaloricPoly d) (h : E d × ℝ) : CaloricPoly d where
  a := P.eval h
  b := P.b + Matrix.toEuclideanLin P.M h.1
  c := P.c
  M := P.M
  symm := P.symm

/-- Parabolic rescaling: `(P.rescale r λ).eval (y, s) = P.eval (r y, r² s) / λ`. -/
noncomputable def rescale (P : CaloricPoly d) (r lam : ℝ) : CaloricPoly d where
  a := P.a / lam
  b := (r / lam) • P.b
  c := r ^ 2 * P.c / lam
  M := (r ^ 2 / lam) • P.M
  symm := P.symm.smul _

@[simp] theorem recenter_a (P : CaloricPoly d) (h : E d × ℝ) : (P.recenter h).a = P.eval h := rfl
@[simp] theorem recenter_b (P : CaloricPoly d) (h : E d × ℝ) :
    (P.recenter h).b = P.b + Matrix.toEuclideanLin P.M h.1 := rfl
@[simp] theorem recenter_c (P : CaloricPoly d) (h : E d × ℝ) : (P.recenter h).c = P.c := rfl
@[simp] theorem recenter_M (P : CaloricPoly d) (h : E d × ℝ) : (P.recenter h).M = P.M := rfl
@[simp] theorem rescale_a (P : CaloricPoly d) (r lam : ℝ) : (P.rescale r lam).a = P.a / lam := rfl
@[simp] theorem rescale_b (P : CaloricPoly d) (r lam : ℝ) :
    (P.rescale r lam).b = (r / lam) • P.b := rfl
@[simp] theorem rescale_c (P : CaloricPoly d) (r lam : ℝ) :
    (P.rescale r lam).c = r ^ 2 * P.c / lam := rfl
@[simp] theorem rescale_M (P : CaloricPoly d) (r lam : ℝ) :
    (P.rescale r lam).M = (r ^ 2 / lam) • P.M := rfl

theorem recenter_eval (P : CaloricPoly d) (h z : E d × ℝ) :
    (P.recenter h).eval z = P.eval (z + h) := by
  simp only [eval_eq_bilin, recenter_a, recenter_b, recenter_c, recenter_M, Prod.fst_add,
    Prod.snd_add, inner_add_left, inner_add_right, map_add, ContinuousLinearMap.add_apply,
    inner_toEuclideanLin P.symm, bilin_symm P.symm z.1 h.1, real_inner_comm z.1 P.b]
  ring

@[simp] theorem src_recenter (P : CaloricPoly d) (h : E d × ℝ) : (P.recenter h).src = P.src := rfl

theorem IsDegLE.recenter {P : CaloricPoly d} {k : ℕ} (hP : P.IsDegLE k) (h : E d × ℝ) :
    (P.recenter h).IsDegLE k := by
  rcases k with _ | _ | k
  · obtain ⟨h1, h2, h3⟩ := hP
    exact ⟨by simp [h1, h3], h2, h3⟩
  · exact hP
  · exact trivial

theorem rescale_eval (P : CaloricPoly d) (r lam : ℝ) (q : E d × ℝ) :
    (P.rescale r lam).eval q = P.eval (r • q.1, r ^ 2 * q.2) / lam := by
  simp only [eval_eq_bilin, rescale_a, rescale_b, rescale_c, rescale_M, bilin_smul,
    real_inner_smul_left, real_inner_smul_right, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem src_rescale (P : CaloricPoly d) (r lam : ℝ) :
    (P.rescale r lam).src = r ^ 2 * P.src / lam := by
  simp only [src, rescale_c, rescale_M, Matrix.trace_smul, smul_eq_mul]
  ring

theorem IsDegLE.rescale {P : CaloricPoly d} {k : ℕ} (hP : P.IsDegLE k) (r lam : ℝ) :
    (P.rescale r lam).IsDegLE k := by
  rcases k with _ | _ | k
  · obtain ⟨h1, h2, h3⟩ := hP
    exact ⟨by simp [h1], by simp [h2], by simp [h3]⟩
  · obtain ⟨h2, h3⟩ := hP
    exact ⟨by simp [h2], by simp [h3]⟩
  · exact trivial

theorem coeffNorm_rescale_le (P : CaloricPoly d) {r lam : ℝ} (hr : 0 ≤ r) (hlam : 0 < lam) :
    (P.rescale r lam).coeffNorm ≤ max 1 (max r (r ^ 2)) * P.coeffNorm / lam := by
  set m := max 1 (max r (r ^ 2))
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmr : r ≤ m := (le_max_left r (r ^ 2)).trans (le_max_right _ _)
  have hmr2 : r ^ 2 ≤ m := (le_max_right r (r ^ 2)).trans (le_max_right _ _)
  have hS : 0 ≤ ∑ i, ∑ j, |P.M i j| := by positivity
  have heq : (P.rescale r lam).coeffNorm =
      (|P.a| + r * ‖P.b‖ + r ^ 2 * |P.c| + r ^ 2 * ∑ i, ∑ j, |P.M i j|) / lam := by
    simp only [coeffNorm, rescale_a, rescale_b, rescale_c, rescale_M, Matrix.smul_apply,
      smul_eq_mul, abs_div, abs_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hlam,
      abs_of_nonneg hr, abs_of_nonneg (sq_nonneg r), ← Finset.mul_sum]
    ring
  rw [heq, coeffNorm]
  gcongr
  nlinarith [mul_le_mul_of_nonneg_right hm1 (abs_nonneg P.a),
    mul_le_mul_of_nonneg_right hmr (norm_nonneg P.b),
    mul_le_mul_of_nonneg_right hmr2 (abs_nonneg P.c), mul_le_mul_of_nonneg_right hmr2 hS]

/-! ### Calculus -/

theorem contDiff_eval (P : CaloricPoly d) : ContDiff ℝ ∞ P.eval := by
  have h : P.eval = fun q ↦ P.a + ⟪P.b, q.1⟫ + P.c * q.2 + (1 / 2) * bilin P.M q.1 q.1 :=
    funext (eval_eq_bilin P)
  have h1 : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ bilin P.M q.1 q.1) :=
    ((bilin P.M).contDiff.comp contDiff_fst).clm_apply contDiff_fst
  rw [h]
  exact ((contDiff_const.add (ContDiff.inner ℝ (contDiff_const (c := P.b)) contDiff_fst)).add
    (contDiff_const.mul contDiff_snd)).add (contDiff_const.mul h1)

theorem continuous_eval (P : CaloricPoly d) : Continuous P.eval :=
  P.contDiff_eval.continuous

theorem hasDerivAt_eval_time (P : CaloricPoly d) (q : E d × ℝ) :
    HasDerivAt (fun s ↦ P.eval (q.1, s)) P.c q.2 := by
  have : (fun s ↦ P.eval (q.1, s)) = fun s ↦
      (P.a + ⟪P.b, q.1⟫ + (1 / 2) * ∑ i, ∑ j, P.M i j * q.1 i * q.1 j) + P.c * s := by
    funext s; simp only [eval]; ring
  rw [this]
  simpa using ((hasDerivAt_id q.2).const_mul P.c).const_add
    (P.a + ⟪P.b, q.1⟫ + (1 / 2) * ∑ i, ∑ j, P.M i j * q.1 i * q.1 j)

theorem dₜ_eval (P : CaloricPoly d) (q : E d × ℝ) : dₜ P.eval q = P.c :=
  (P.hasDerivAt_eval_time q).deriv

/-- The spatial Fréchet derivative of a slice: `y ↦ ⟪b, ·⟫ + bilin M y`. -/
theorem hasFDerivAt_eval_slice (P : CaloricPoly d) (s : ℝ) (y : E d) :
    HasFDerivAt (fun y ↦ P.eval (y, s)) (innerSL ℝ P.b + bilin P.M y) y := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have key : ∀ h, P.eval (y + h, s) - P.eval (y, s) - (innerSL ℝ P.b + bilin P.M y) h =
      (1 / 2) * bilin P.M h h := by
    intro h
    simp only [eval_eq_bilin, map_add, ContinuousLinearMap.add_apply, innerSL_apply_apply,
      inner_add_right, bilin_symm P.symm h y]
    ring
  simp only [key]
  refine isLittleO_of_abs_le_rpow (A := 1 / 2 * ‖bilin P.M‖) one_pos one_pos fun h _ ↦ ?_
  have := (bilin P.M).le_opNorm₂ h h
  rw [Real.norm_eq_abs] at this
  rw [abs_mul, show (1 : ℝ) + 1 = (2 : ℕ) by norm_num, Real.rpow_natCast, abs_of_pos one_half_pos]
  calc 1 / 2 * |bilin P.M h h| ≤ 1 / 2 * (‖bilin P.M‖ * ‖h‖ * ‖h‖) := by gcongr
    _ = 1 / 2 * ‖bilin P.M‖ * ‖h‖ ^ 2 := by ring

theorem hasGradientAt_eval_slice (P : CaloricPoly d) (q : E d × ℝ) :
    HasGradientAt (fun y ↦ P.eval (y, q.2)) (P.b + Matrix.toEuclideanLin P.M q.1) q.1 := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert P.hasFDerivAt_eval_slice q.2 q.1 using 1
  ext v
  simp [inner_toEuclideanLin P.symm]

theorem gradₓ_eval (P : CaloricPoly d) (q : E d × ℝ) :
    gradₓ P.eval q = P.b + Matrix.toEuclideanLin P.M q.1 :=
  (P.hasGradientAt_eval_slice q).gradient

theorem iteratedFDeriv_two_slice_eval (P : CaloricPoly d) (s : ℝ) (x v w : E d) :
    iteratedFDeriv ℝ 2 (fun y ↦ P.eval (y, s)) x ![v, w] = bilin P.M v w := by
  rw [iteratedFDeriv_two_apply]
  have hf : fderiv ℝ (fun y ↦ P.eval (y, s)) = fun y ↦ innerSL ℝ P.b + bilin P.M y :=
    funext fun y ↦ (P.hasFDerivAt_eval_slice s y).fderiv
  rw [hf, ((bilin P.M).hasFDerivAt.const_add (innerSL ℝ P.b)).fderiv]
  simp

theorem lapₓ_eval (P : CaloricPoly d) (q : E d × ℝ) : lapₓ P.eval q = Matrix.trace P.M := by
  rw [lapₓ, laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [iteratedFDeriv_two_slice_eval, EuclideanSpace.basisFun_apply, bilin_single]
  rfl

theorem dₜ_sub_lapₓ_eval (P : CaloricPoly d) (q : E d × ℝ) :
    dₜ P.eval q - lapₓ P.eval q = P.src := by
  rw [dₜ_eval, lapₓ_eval, src]

end CaloricPoly

end ParabolicBasic
