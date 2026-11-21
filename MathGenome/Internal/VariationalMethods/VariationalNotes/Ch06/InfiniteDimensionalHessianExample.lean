import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.InfiniteDimensionalHessianExample
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped Topology ContDiff
open Filter
namespace VariationalNotes.Ch06.InfiniteHessian

lemma weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  positivity

lemma infinite_dimensional : ¬ FiniteDimensional ℝ H := by
  intro h
  let := h
  let b : HilbertBasis ℕ ℝ H := ⟨LinearIsometryEquiv.refl ℝ H⟩
  exact Module.Finite.not_linearIndependent_of_infinite b b.orthonormal.linearIndependent

lemma weight_exact (n : ℕ) : weight n = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  simp only [weight, zpow_neg, zpow_natCast, one_div, inv_pow]

lemma sqrt_weight_exact (n : ℕ) :
    Real.sqrt (weight n) = (2 : ℝ) ^ (-((n : ℝ) + 1) / 2) := by
  rw [Real.sqrt_eq_rpow, weight_exact, ← Real.rpow_intCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

lemma weight_summable : Summable weight := by
  change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
  simpa only [pow_succ] using
    (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_right (1 / 2)

lemma weight_tsum : ∑' n, weight n = 1 := by
  simp only [weight, pow_succ, tsum_mul_right]
  rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
  norm_num

lemma weighted_product_bound (x y : H) (n : ℕ) :
    ‖weight n * x n * y n‖ ≤ weight n * (‖x‖ * ‖y‖) := by
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (weight_pos n).le]
  have hx := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x n
  have hy := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) y n
  calc
    weight n * ‖x n‖ * ‖y n‖ ≤ weight n * ‖x‖ * ‖y‖ := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx (weight_pos n).le) hy
        (norm_nonneg _) (mul_nonneg (weight_pos n).le (norm_nonneg _))
    _ = weight n * (‖x‖ * ‖y‖) := by ring

lemma weighted_product_summable (x y : H) :
    Summable (fun n => weight n * x n * y n) :=
  Summable.of_norm_bounded (weight_summable.mul_right (‖x‖ * ‖y‖))
    (weighted_product_bound x y)

lemma weighted_product_tsum_bound (x y : H) :
    ‖∑' n, weight n * x n * y n‖ ≤ ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ∑' n, ‖weight n * x n * y n‖ :=
      norm_tsum_le_tsum_norm (weighted_product_summable x y).norm
    _ ≤ ∑' n, weight n * (‖x‖ * ‖y‖) :=
      (weighted_product_summable x y).norm.tsum_le_tsum
        (weighted_product_bound x y) (weight_summable.mul_right _)
    _ = ‖x‖ * ‖y‖ := by rw [tsum_mul_right, weight_tsum, one_mul]

noncomputable def weightedLinear : H →ₗ[ℝ] H →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑' n, weight n * x n * y n)
    (by
      intro x z y
      simp only [lp.coeFn_add, Pi.add_apply, mul_add, add_mul]
      exact (weighted_product_summable x y).tsum_add (weighted_product_summable z y))
    (by
      intro c x y
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp_rw [show ∀ n, weight n * (c * x n) * y n = c * (weight n * x n * y n) by
        intro n; ring]
      exact tsum_mul_left)
    (by
      intro x y z
      simp only [lp.coeFn_add, Pi.add_apply, mul_add]
      exact (weighted_product_summable x y).tsum_add (weighted_product_summable x z))
    (by
      intro c x y
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp_rw [show ∀ n, weight n * x n * (c * y n) = c * (weight n * x n * y n) by
        intro n; ring]
      exact tsum_mul_left)

noncomputable def B : H →L[ℝ] H →L[ℝ] ℝ :=
  weightedLinear.mkContinuous₂ 1 (by
    intro x y
    simpa [weightedLinear] using weighted_product_tsum_bound x y)

lemma B_apply (x y : H) : B x y = ∑' n, weight n * x n * y n := rfl

lemma B_symm (x y : H) : B x y = B y x := by
  simp only [B_apply]
  congr 1
  funext n
  ring

lemma quadratic_eq_B (x : H) : quadratic x = B x x := by
  simp only [quadratic, B_apply, pow_two, mul_assoc]

lemma quadratic_summable (x : H) : Summable (fun n => weight n * (x n) ^ 2) := by
  simpa only [pow_two, mul_assoc] using weighted_product_summable x x

lemma quadratic_nonneg (x : H) : 0 ≤ quadratic x :=
  tsum_nonneg (fun n => mul_nonneg (weight_pos n).le (sq_nonneg _))

lemma quadratic_bound (x : H) : quadratic x ≤ ‖x‖ ^ 2 := by
  rw [quadratic_eq_B, pow_two]
  exact (le_abs_self _).trans (weighted_product_tsum_bound x x)

lemma quadratic_pos (x : H) (hx : x ≠ 0) : 0 < quadratic x := by
  have hn : ∃ n, x n ≠ 0 := by
    by_contra! hn
    apply hx
    ext n
    exact hn n
  obtain ⟨n, hn⟩ := hn
  exact (quadratic_summable x).tsum_pos
    (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _)) n
    (mul_pos (weight_pos n) (sq_pos_of_ne_zero hn))

lemma quadratic_smooth : ContDiff ℝ ∞ quadratic := by
  rw [show quadratic = (fun x : H => B x x) from funext quadratic_eq_B]
  exact B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)

lemma F_smooth : ContDiff ℝ ∞ F := by
  have hn : ContDiff ℝ ∞ (fun x : H => ‖x‖ ^ 4) := by
    convert (contDiff_norm_sq ℝ (E := H)).pow 2 using 1
    simp [← pow_mul]
  exact (contDiff_const.mul quadratic_smooth).sub hn

lemma hasFDerivAt_quadratic (x : H) :
    HasFDerivAt quadratic (2 • B x) x := by
  rw [show quadratic = (fun x : H => B x x) from funext quadratic_eq_B]
  convert! B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x) using 1
  ext h
  simp [ContinuousLinearMap.precompR, B_symm, two_smul]

noncomputable def D (x : H) : H →L[ℝ] ℝ :=
  B x - (4 * ‖x‖ ^ 2) • innerSL ℝ x

lemma hasFDerivAt_F (x : H) : HasFDerivAt F (D x) x := by
  have hq := (hasFDerivAt_quadratic x).const_mul (1 / 2 : ℝ)
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := hq.sub (hn.mul hn)
  convert h using 1
  · funext y
    simp only [F, Pi.sub_apply, Pi.mul_apply]
    ring
  · ext y
    simp [D]
    ring

lemma fderiv_F : fderiv ℝ F = D := funext fun x => (hasFDerivAt_F x).fderiv

lemma derivative_zero : fderiv ℝ F 0 = 0 := by
  simp [fderiv_F, D]

lemma hasFDerivAt_D_zero : HasFDerivAt D B 0 := by
  have hn := ((hasStrictFDerivAt_norm_sq (0 : H)).hasFDerivAt).const_mul (4 : ℝ)
  have h := B.hasFDerivAt.sub (hn.smul ((innerSL ℝ (E := H)).hasFDerivAt))
  convert! h using 1
  simp

lemma hessian (h : H) : fderiv ℝ (fderiv ℝ F) 0 h h = quadratic h := by
  rw [fderiv_F, hasFDerivAt_D_zero.fderiv, quadratic_eq_B]

lemma quadratic_single (n : ℕ) (a : ℝ) :
    quadratic (lp.single 2 n a) = weight n * a ^ 2 := by
  unfold quadratic
  rw [tsum_eq_single n]
  · simp
  · intro k hk
    simp [lp.single_apply, hk]

lemma norm_witness (n : ℕ) : ‖witness n‖ = Real.sqrt (weight n) := by
  rw [witness, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact Real.norm_of_nonneg (Real.sqrt_nonneg _)

lemma F_zero : F 0 = 0 := by
  simp [F, quadratic]

lemma F_witness (n : ℕ) : F (witness n) = -(weight n) ^ 2 / 2 := by
  have hs := Real.sq_sqrt (weight_pos n).le
  rw [F, norm_witness]
  rw [witness, quadratic_single, hs]
  nlinarith [sq_nonneg (weight n)]

lemma F_witness_lt (n : ℕ) : F (witness n) < F 0 := by
  rw [F_witness, F_zero]
  have := sq_pos_of_pos (weight_pos n)
  linarith

lemma weight_tendsto : Tendsto weight atTop (nhds 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
  change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (nhds 0)
  simpa only [pow_succ, zero_mul] using h

lemma witness_tendsto : Tendsto witness atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [norm_witness]
  convert! Real.continuous_sqrt.continuousAt.tendsto.comp weight_tendsto using 1
  simp

lemma not_local_min : ¬ IsLocalMin F 0 := by
  intro h
  have he : ∀ᶠ n in atTop, F 0 ≤ F (witness n) := witness_tendsto.eventually h
  obtain ⟨n, hn⟩ := he.exists
  exact (F_witness_lt n).not_ge hn

lemma no_uniform_bound : ¬ (∃ m : ℝ, 0 < m ∧ ∀ h : H,
    m * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) 0 h h) := by
  rintro ⟨m, hm, hbound⟩
  have hb : ∀ n, m ≤ weight n := by
    intro n
    have h := hbound (lp.single 2 n 1)
    rw [hessian, quadratic_single, lp.norm_single (by norm_num : (0 : ENNReal) < 2)] at h
    simpa using h
  have hm0 : m ≤ 0 := ge_of_tendsto weight_tendsto (Eventually.of_forall hb)
  exact hm.not_ge hm0

lemma F_witness_exact (n : ℕ) :
    F (witness n) = -(2 : ℝ) ^ (-((2 * (n + 1) : ℕ) : ℤ)) / 2 := by
  rw [F_witness, weight_exact]
  congr 2
  rw [zpow_neg, zpow_natCast, ← inv_pow, ← pow_mul]
  rw [zpow_neg, zpow_natCast, Nat.mul_comm 2, inv_pow]

/-- The unnumbered ℓ² example following the unconstrained optimality tests. -/
theorem example_properties : Specs.properties := by
  refine ⟨infinite_dimensional, weight_exact, sqrt_weight_exact, quadratic_summable,
    ?_, quadratic_smooth.continuous,
    (fun x => ⟨quadratic_nonneg x, quadratic_bound x⟩), F_smooth,
    derivative_zero, hessian, quadratic_pos, F_zero,
    (fun n => ⟨F_witness n, F_witness_exact n, F_witness_lt n⟩), witness_tendsto,
    not_local_min, no_uniform_bound⟩
  exact ⟨B, B_apply, B_symm, weighted_product_tsum_bound, quadratic_eq_B⟩

end VariationalNotes.Ch06.InfiniteHessian
