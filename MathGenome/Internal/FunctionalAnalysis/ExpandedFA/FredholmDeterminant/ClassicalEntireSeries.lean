import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalEntireSeries
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalDefinitions
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Filter
open scoped Topology
universe u

namespace ExpandedFA.FredholmDeterminant.ClassicalEntireSeries

open ClassicalDefinitions.Spec Spec.Data

noncomputable def fredholmMinorKernel : Spec.MinorKernelType.{u} := @Spec.MinorKernelValue

lemma hadamardBound_eq_rpow (M : ℝ) (n : ℕ) :
    hadamardBound M n = (n : ℝ) ^ ((n : ℝ) / 2) * M ^ n := by
  unfold hadamardBound
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 2
  ring

/-- The entrywise Hadamard bound, with no nonempty-dimension restriction. -/
lemma norm_det_le_hadamard (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A.det‖ ≤ (Real.sqrt n) ^ n * M ^ n := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun i => WithLp.toLp 2 (fun j => A j i)
  let a := EuclideanSpace.basisFun (Fin n) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) :=
    by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim v
  have he : a.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have hc : ‖a.toBasis.det v‖ = ‖b.toBasis.det v‖ := by
    conv_lhs => rw [a.toBasis.det.eq_smul_basis_det b.toBasis]
    simp only [smul_apply, smul_eq_mul, norm_mul]
    change ‖a.toBasis.det b‖ * ‖b.toBasis.det v‖ = _
    rw [a.det_to_matrix_orthonormalBasis b, one_mul]
  rw [← he, hc, InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  calc
    ∏ i : Fin n, ‖inner ℂ (b i) (v i)‖ ≤ ∏ i : Fin n, Real.sqrt n * M := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      calc
        ‖inner ℂ (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
        _ = ‖v i‖ := by rw [b.norm_eq_one, one_mul]
        _ = Real.sqrt (∑ j : Fin n, ‖A j i‖ ^ 2) := EuclideanSpace.norm_eq _
        _ ≤ Real.sqrt ((n : ℝ) * M ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc
            ∑ j : Fin n, ‖A j i‖ ^ 2 ≤ ∑ _ : Fin n, M ^ 2 :=
              Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA j i) _
            _ = _ := by simp
        _ = Real.sqrt n * M := by rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hM]
    _ = _ := by simp [mul_pow]

theorem pointwise_hadamard_bounds : Spec.PointwiseHadamardBounds.{u} := by
  intro Q _ _ k n t
  constructor
  · exact norm_det_le_hadamard n _ ‖k‖ (norm_nonneg _) fun i j =>
      k.norm_coe_le_norm (t i, t j)
  · intro x y
    exact norm_det_le_hadamard (n + 1) _ ‖k‖ (norm_nonneg _) fun i j =>
      k.norm_coe_le_norm (Fin.cons (α := fun _ => Q) x t i,
        Fin.cons (α := fun _ => Q) y t j)

lemma continuous_augmentedKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    (k : C(Q × Q, ℂ)) (n : ℕ) : Continuous (augmentedKernel k n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply k.continuous.comp
  apply Continuous.prodMk
  · have hc : Continuous (fun p : (Fin n → Q) × (Q × Q) =>
        Fin.cons (α := fun _ => Q) p.2.1 p.1) :=
      Continuous.finCons (A := fun _ => Q)
        (continuous_fst.comp continuous_snd) continuous_fst
    exact (continuous_apply i).comp hc
  · have hc : Continuous (fun p : (Fin n → Q) × (Q × Q) =>
        Fin.cons (α := fun _ => Q) p.2.2 p.1) :=
      Continuous.finCons (A := fun _ => Q)
        (continuous_snd.comp continuous_snd) continuous_fst
    exact (continuous_apply j).comp hc

theorem coefficient_identification : Spec.CoefficientIdentification.{u} := by
  intro Q _ _ _ _ μ _ k n
  have : IsFiniteMeasure (MeasurePowerValue μ n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ)))
  have hi : Integrable (augmentedKernel k n) (MeasurePowerValue μ n) :=
    (continuous_augmentedKernel k n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  refine ⟨hi, ?_, ?_⟩
  · intro x y
    exact ContinuousMap.integral_apply hi (x, y)
  · intro z x y
    change ((-z) ^ n / (n.factorial : ℂ)) * minorCoefficient μ k n (x, y) =
      ((-z) ^ n / (n.factorial : ℂ)) * MinorIntegralValue μ k n x y
    exact congrArg (fun a : ℂ => ((-z) ^ n / (n.factorial : ℂ)) * a)
      (ContinuousMap.integral_apply hi (x, y))

theorem integral_hadamard_bounds : Spec.IntegralHadamardBounds.{u} := by
  intro Q _ _ _ _ μ _ k n
  have : IsFiniteMeasure (MeasurePowerValue μ n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ)))
  have hm : (MeasurePowerValue μ n).real Set.univ = MeasureMassValue μ ^ n := by
    simp [MeasurePowerValue, MeasureMassValue, measureReal_def, Measure.pi_univ]
  constructor
  · exact hm ▸ norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun t => (pointwise_hadamard_bounds k n t).1)
  · change ‖∫ t, augmentedKernel k n t ∂MeasurePowerValue μ n‖ ≤ _
    rw [← hm]
    apply norm_integral_le_of_norm_le_const
    apply Filter.Eventually.of_forall
    intro t
    apply (ContinuousMap.norm_le _ (by unfold hadamardBound; positivity)).mpr
    intro p
    exact (pointwise_hadamard_bounds k n t).2 p.1 p.2

theorem uniform_term_bounds : Spec.UniformTermBounds.{u} := by
  intro Q _ _ _ _ μ _ k R hR z hz n
  have hd := (integral_hadamard_bounds μ k n).1
  have hb := (integral_hadamard_bounds μ k n).2
  have hf : (0 : ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
  have hz' : ‖(-z) ^ n / (n.factorial : ℂ)‖ ≤ R ^ n / (n.factorial : ℝ) := by
    simp only [norm_div, norm_pow, norm_neg, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz n) hf
  constructor
  · change ‖(-z) ^ n / (n.factorial : ℂ) * DeterminantIntegralValue μ k n‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hz' hd (norm_nonneg _) (div_nonneg (pow_nonneg hR _) hf)
  · change ‖((-z) ^ n / (n.factorial : ℂ)) • minorCoefficient μ k n‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul hz' hb (norm_nonneg _) (div_nonneg (pow_nonneg hR _) hf)

/-- A square bound by exponential-series coefficients implies summability.
The comparison uses a geometric series and a rescaled exponential series. -/
lemma summable_of_sq_le_factorial (f : ℕ → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, f n ^ 2 ≤ A * B ^ n / (n.factorial : ℝ)) : Summable f := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have he := (Real.summable_pow_div_factorial (2 * B)).mul_left A
  apply Summable.of_nonneg_of_le hf _ (hg.add he)
  intro n
  have hq : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hy : 0 ≤ A * ((2 * B) ^ n / (n.factorial : ℝ)) := by positivity
  have hqy : (1 / 2 : ℝ) ^ n * (A * ((2 * B) ^ n / (n.factorial : ℝ))) =
      A * B ^ n / (n.factorial : ℝ) := by
    rw [mul_pow]
    have hn : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = A * (((1 / 2 : ℝ) ^ n * 2 ^ n) * B ^ n) / (n.factorial : ℝ) := by ring
      _ = _ := by rw [hn]; ring
  have hh := h n
  rw [← hqy] at hh
  nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ n - A * ((2 * B) ^ n / (n.factorial : ℝ)))]

lemma summable_hadamard_weights (C : ℝ) (hC : 0 ≤ C) :
    Summable (fun n : ℕ => (Real.sqrt n * C) ^ n / (n.factorial : ℝ)) := by
  apply summable_of_sq_le_factorial _ 1 (Real.exp 1 * C ^ 2)
    (by positivity) (by positivity) (fun _ => by positivity)
  intro n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  calc
    ((Real.sqrt n * C) ^ n / (n.factorial : ℝ)) ^ 2 =
        (((n : ℝ) ^ n / (n.factorial : ℝ)) * (C ^ 2) ^ n) /
          (n.factorial : ℝ) := by
      rw [div_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg n), mul_pow]
      ring
    _ ≤ (Real.exp n * (C ^ 2) ^ n) / (n.factorial : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp n (Nat.cast_nonneg n) n)
          (by positivity)) hf.le
    _ = 1 * (Real.exp 1 * C ^ 2) ^ n / (n.factorial : ℝ) := by
      rw [mul_pow, ← Real.exp_nat_mul, mul_one, one_mul]

lemma summable_augmented_hadamard_weights (C : ℝ) (hC : 0 ≤ C) :
    Summable (fun n : ℕ => (Real.sqrt (n + 1)) ^ (n + 1) * C ^ n /
      (n.factorial : ℝ)) := by
  apply summable_of_sq_le_factorial _ (Real.exp 1) (2 * Real.exp 1 * C ^ 2)
    (by positivity) (by positivity) (fun _ => by positivity)
  intro n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have htwo : (n : ℝ) + 1 ≤ 2 ^ n := by
    clear hf
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.cast_add_one, pow_succ]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
  have hn : ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ≤
      Real.exp ((n : ℝ) + 1) * ((n : ℝ) + 1) := by
    apply (div_le_iff₀ hf).mpr
    have he := (div_le_iff₀ (show (0 : ℝ) < ((n + 1).factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp (n + 1) (by positivity) (n + 1))
    simpa [Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, mul_assoc] using he
  calc
    ((Real.sqrt (n + 1)) ^ (n + 1) * C ^ n / (n.factorial : ℝ)) ^ 2 =
        ((((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ)) * (C ^ 2) ^ n) /
          (n.factorial : ℝ) := by
      rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul,
        Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm n 2, pow_mul]
      ring
    _ ≤ (Real.exp ((n : ℝ) + 1) * 2 ^ n * (C ^ 2) ^ n) / (n.factorial : ℝ) := by
      gcongr
      exact hn.trans (mul_le_mul_of_nonneg_left htwo (by positivity))
    _ = Real.exp 1 * (2 * Real.exp 1 * C ^ 2) ^ n / (n.factorial : ℝ) := by
      rw [Real.exp_add, show Real.exp (n : ℝ) = Real.exp 1 ^ n by simp]
      simp only [mul_pow]
      ring

theorem majorants_summable : Spec.MajorantsSummable := by
  intro m M R hm hM hR
  constructor
  · convert summable_hadamard_weights (R * M * m) (by positivity) using 1
    ext n
    simp only [determinantMajorant, hadamardBound, mul_pow]
    ring
  · convert (summable_augmented_hadamard_weights (R * M * m) (by positivity)).mul_left M using 1
    ext n
    simp only [minorMajorant, hadamardBound, mul_pow, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem absolute_convergence : Spec.AbsoluteConvergence.{u} := by
  intro Q _ _ _ _ μ _ k z
  have hs := majorants_summable (MeasureMassValue μ) ‖k‖ ‖z‖
    (by exact measureReal_nonneg) (norm_nonneg _) (norm_nonneg _)
  have hb := uniform_term_bounds μ k ‖z‖ (norm_nonneg _) z le_rfl
  exact ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (hb n).1) hs.1,
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (hb n).2) hs.2⟩

theorem uniform_convergence_on_disks : Spec.UniformConvergenceOnDisks.{u} := by
  intro Q _ _ _ _ μ _ k R hR
  have hs := majorants_summable (MeasureMassValue μ) ‖k‖ R
    (by exact measureReal_nonneg) (norm_nonneg _) hR
  constructor
  · exact tendstoUniformlyOn_tsum_nat hs.1 fun n z hz =>
      (uniform_term_bounds μ k R hR z (by simpa using hz) n).1
  · exact tendstoUniformlyOn_tsum_nat hs.2 fun n z hz =>
      (uniform_term_bounds μ k R hR z (by simpa using hz) n).2

theorem minor_kernel_identification : Spec.MinorKernelIdentification.{u} := by
  intro Q _ _ _ _ μ _ k z x y
  change (ContinuousMap.evalCLM ℂ (x, y)) (∑' n, minorKernelTerm μ k z n) = _
  rw [(ContinuousMap.evalCLM ℂ (x, y)).map_tsum
    (absolute_convergence μ k z).2.of_norm]
  change (∑' n, minorKernelTerm μ k z n (x, y)) = ∑' n, MinorTermValue μ k x y z n
  exact tsum_congr fun n => (coefficient_identification μ k n).2.2 z x y

private lemma differentiable_determinantTerm {Q : Type u} [TopologicalSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (n : ℕ) :
    Differentiable ℂ (fun z => DeterminantTermValue μ k z n) := by
  change Differentiable ℂ (fun z : ℂ =>
    (-z) ^ n / (n.factorial : ℂ) * DeterminantIntegralValue μ k n)
  fun_prop

private lemma differentiable_minorKernelTerm {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (n : ℕ) :
    Differentiable ℂ (fun z => minorKernelTerm μ k z n) := by
  change Differentiable ℂ (fun z : ℂ =>
    ((-z) ^ n / (n.factorial : ℂ)) • minorCoefficient μ k n)
  fun_prop

theorem entire_functions : Spec.EntireFunctions.{u} := by
  intro Q _ _ _ _ μ _ k
  constructor <;> intro z
  · have hs := (majorants_summable (MeasureMassValue μ) ‖k‖ (‖z‖ + 1)
        (by exact measureReal_nonneg) (norm_nonneg _) (by positivity)).1
    have hd := Complex.differentiableOn_tsum_of_summable_norm hs
      (fun n => (differentiable_determinantTerm μ k n).differentiableOn)
      (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ‖z‖ + 1))
      (fun n w hw => (uniform_term_bounds μ k (‖z‖ + 1) (by positivity) w
        (le_of_lt (by simpa using hw)) n).1)
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))
  · have hs := (majorants_summable (MeasureMassValue μ) ‖k‖ (‖z‖ + 1)
        (by exact measureReal_nonneg) (norm_nonneg _) (by positivity)).2
    have hd := Complex.differentiableOn_tsum_of_summable_norm hs
      (fun n => (differentiable_minorKernelTerm μ k n).differentiableOn)
      (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ‖z‖ + 1))
      (fun n w hw => (uniform_term_bounds μ k (‖z‖ + 1) (by positivity) w
        (le_of_lt (by simpa using hw)) n).2)
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))

theorem termwise_differentiation : Spec.TermwiseDifferentiation.{u} := by
  intro Q _ _ _ _ μ _ k z
  have hs := majorants_summable (MeasureMassValue μ) ‖k‖ (‖z‖ + 1)
    (by exact measureReal_nonneg) (norm_nonneg _) (by positivity)
  constructor
  · exact Complex.hasSum_deriv_of_summable_norm hs.1
      (fun n => (differentiable_determinantTerm μ k n).differentiableOn)
      (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ‖z‖ + 1))
      (fun n w hw => (uniform_term_bounds μ k (‖z‖ + 1) (by positivity) w
        (le_of_lt (by simpa using hw)) n).1) (by simp)
  · exact Complex.hasSum_deriv_of_summable_norm hs.2
      (fun n => (differentiable_minorKernelTerm μ k n).differentiableOn)
      (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ‖z‖ + 1))
      (fun n w hw => (uniform_term_bounds μ k (‖z‖ + 1) (by positivity) w
        (le_of_lt (by simpa using hw)) n).2) (by simp)

theorem values_at_zero : Spec.ValuesAtZero.{u} := by
  intro Q _ _ _ μ k
  constructor
  · change (∑' n, DeterminantTermValue μ k 0 n) = 1
    rw [tsum_eq_single 0]
    · exact (ClassicalDefinitions.zeroth_terms μ k).2.2.1 0
    · intro n hn
      simp [DeterminantTermValue, zero_pow hn]
  · change (∑' n, minorKernelTerm μ k 0 n) = k
    rw [tsum_eq_single 0]
    · simp only [minorKernelTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        one_smul]
      change (∫ t : Fin 0 → Q, augmentedKernel k 0 t ∂MeasurePowerValue μ 0) = k
      have heq : (fun t : Fin 0 → Q => augmentedKernel k 0 t) = fun _ => k := by
        funext t
        ext p
        simp [augmentedKernel, AugmentedMatrixValue]
      rw [heq, integral_const]
      simp [MeasurePowerValue, measureReal_def]
    · intro n hn
      simp [minorKernelTerm, zero_pow hn]

end ExpandedFA.FredholmDeterminant.ClassicalEntireSeries
