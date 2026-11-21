import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalLogDerivative
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalProduct
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalFredholm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.ContinuousTraceDiagonal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalLogDerivative
open ClassicalDefinitions.Spec ClassicalProduct.Spec.Data Spec.Data
open IntegralOperators.ContinuousTraceDiagonal.Spec
open TraceIdeals.TraceClassDefinitions.Spec

variable {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q]
  [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]

lemma norm_compositionKernel_le (k l : C(Q × Q, ℂ)) :
    ‖compositionKernel μ k l‖ ≤ μ.real Set.univ * ‖k‖ * ‖l‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall (ClassicalProduct.norm_compositionIntegrand_le k l))
  change ‖∫ t, compositionIntegrand k l t ∂μ‖ ≤ _
  calc
    _ ≤ ‖k‖ * ‖l‖ * μ.real Set.univ := h
    _ = _ := by ring

lemma iteratedKernel_formula (k : C(Q × Q, ℂ)) (n : ℕ) (x y : Q) :
    iteratedKernel μ k (n + 1) (x, y) =
      ∫ t, k (x, t) * iteratedKernel μ k n (t, y) ∂μ :=
  ClassicalProduct.composition_formula μ k (iteratedKernel μ k n) x y

/-- The elementary geometric bound from the source proof, including μ=0. -/
lemma norm_iteratedKernel_le (k : C(Q × Q, ℂ)) (n : ℕ) :
    ‖iteratedKernel μ k n‖ ≤ ‖k‖ ^ (n + 1) * μ.real Set.univ ^ n := by
  induction n with
  | zero => simp [iteratedKernel]
  | succ n ih =>
    calc
      _ ≤ μ.real Set.univ * ‖k‖ * ‖iteratedKernel μ k n‖ :=
        norm_compositionKernel_le μ k _
      _ ≤ μ.real Set.univ * ‖k‖ * (‖k‖ ^ (n + 1) * μ.real Set.univ ^ n) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (measureReal_nonneg) (norm_nonneg _))
      _ = _ := by simp only [pow_succ]; ring

lemma norm_diagonalCoefficient_le (k : C(Q × Q, ℂ)) (n : ℕ) :
    ‖diagonalCoefficient μ k n‖ ≤ (μ.real Set.univ * ‖k‖) ^ (n + 1) := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall fun t => (iteratedKernel μ k n).norm_coe_le_norm (t,t))
  calc
    _ ≤ ‖iteratedKernel μ k n‖ * μ.real Set.univ := h
    _ ≤ (‖k‖ ^ (n + 1) * μ.real Set.univ ^ n) * μ.real Set.univ :=
      mul_le_mul_of_nonneg_right (norm_iteratedKernel_le μ k n) measureReal_nonneg
    _ = _ := by rw [mul_pow, pow_succ (μ.real Set.univ)]; ring

/-- The canonical maps C(Q)→L² intertwine the two original kernel operators. -/
lemma kernel_toLp (k : C(Q × Q, ℂ)) (f : C(Q, ℂ)) :
    continuousKernelOperator μ k (ContinuousMap.toLp 2 μ ℂ f) =
      ContinuousMap.toLp 2 μ ℂ (KernelOperatorValue μ k f) := by
  apply Lp.ext
  have h := IntegralOperators.ContinuousTraceDiagonal.continuousKernelOperator_ae μ k
    (ContinuousMap.toLp 2 μ ℂ f)
  have hg := ContinuousMap.coeFn_toLp (𝕜 := ℂ) μ (KernelOperatorValue μ k f) (p := 2)
  have hi (x : Q) : (∫ y, k (x, y) * (ContinuousMap.toLp 2 μ ℂ f) y ∂μ) =
      KernelOperatorValue μ k f x := by
    rw [(ClassicalDefinitions.data_identification μ k).1 f x]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) μ f (p := 2)] with y hy
    rw [hy]
  filter_upwards [h, hg] with x hx hxg
  exact hx.trans ((hi x).trans hxg.symm)

lemma continuousOperator_composition (k l : C(Q × Q, ℂ)) :
    KernelOperatorValue μ (compositionKernel μ k l) =
      (KernelOperatorValue μ k).comp (KernelOperatorValue μ l) := by
  ext f x
  rw [(ClassicalDefinitions.data_identification μ _).1,
    ClassicalResolventIdentities.kernelOperator_comp_apply]
  simp only [ClassicalProduct.composition_formula μ k l]

lemma l2Operator_composition (k l : C(Q × Q, ℂ)) :
    continuousKernelOperator μ (compositionKernel μ k l) =
      (continuousKernelOperator μ k).comp (continuousKernelOperator μ l) := by
  have hd := ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  apply DFunLike.coe_injective
  apply hd.equalizer
  · exact (continuousKernelOperator μ _).continuous
  · exact ((continuousKernelOperator μ k).comp (continuousKernelOperator μ l)).continuous
  · funext f
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, kernel_toLp,
      continuousOperator_composition]

theorem iterated_operator : Spec.IteratedOperator.{u} := by
  intro Q _ _ _ _ μ _ k n
  induction n with
  | zero => simp [iteratedKernel]
  | succ n ih =>
    change continuousKernelOperator μ (compositionKernel μ k (iteratedKernel μ k n)) = _
    rw [l2Operator_composition, ih]
    change continuousKernelOperator μ k * continuousKernelOperator μ k ^ (n + 1) = _
    exact (pow_succ' _ _).symm

/-- Positive powers stay in the trace ideal. The identity need not be trace class. -/
lemma traceClass_pow_succ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsTraceClassValue T) (n : ℕ) :
    IsTraceClassValue (T ^ (n + 1)) := by
  have h := (TraceIdeals.TraceNormIdeal.two_sided_ideal ℂ H H H H T (T ^ n) 1 hT).1
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at h
  change IsTraceClassValue (T ^ n * T) at h
  simpa only [pow_succ] using h

theorem trace_power_coefficients : Spec.TracePowerCoefficients.{u} := by
  intro Q _ _ _ _ μ _ k hk n
  refine ⟨traceClass_pow_succ _ hk n, ?_⟩
  have ht := IntegralOperators.ContinuousTraceDiagonal.diagonal_trace Q μ
    (iteratedKernel μ k n)
  rw [iterated_operator μ k n] at ht
  exact (ht (traceClass_pow_succ _ hk n)).symm


lemma norm_logarithmicTerm_le (k : C(Q × Q, ℂ)) (z : ℂ) (n : ℕ) :
    ‖-(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * diagonalCoefficient μ k n)‖ ≤
      (‖z‖ * (μ.real Set.univ * ‖k‖)) ^ (n + 1) := by
  rw [norm_neg, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  calc
    _ ≤ ‖z‖ ^ (n + 1) * ‖diagonalCoefficient μ k n‖ :=
      mul_le_mul_of_nonneg_right (div_le_self (by positivity) hn) (norm_nonneg _)
    _ ≤ ‖z‖ ^ (n + 1) * (μ.real Set.univ * ‖k‖) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (norm_diagonalCoefficient_le μ k n) (by positivity)
    _ = _ := (mul_pow _ _ _).symm

lemma summable_logarithmic_terms (k : C(Q × Q, ℂ)) (z : ℂ)
    (hz : ‖z‖ * (μ.real Set.univ * ‖k‖) < 1) :
    Summable (fun n : ℕ => -(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) *
      diagonalCoefficient μ k n)) := by
  have hg := (summable_geometric_of_lt_one (by positivity :
    0 ≤ ‖z‖ * (μ.real Set.univ * ‖k‖)) hz).mul_right
      (‖z‖ * (μ.real Set.univ * ‖k‖))
  apply hg.of_norm_bounded
  intro n
  simpa only [← pow_succ] using norm_logarithmicTerm_le μ k z n

/-- Already proved multiplication-stage clauses retain their original types. -/
theorem uniform_kernel_continuity : ClassicalProduct.Spec.UniformKernelContinuity.{u} :=
  ClassicalProduct.uniform_kernel_continuity

theorem locally_uniform_kernel_limit : ClassicalProduct.Spec.LocallyUniformKernelLimit.{u} :=
  ClassicalProduct.locally_uniform_kernel_limit

theorem multiplication : ClassicalProduct.Spec.Multiplication.{u} :=
  ClassicalProduct.multiplication

theorem scalar_multiplication : ClassicalProduct.Spec.ScalarMultiplication.{u} :=
  ClassicalProduct.scalar_multiplication

open ClassicalEntireSeries.Spec.Data

lemma l2Operator_identity (k a b c : C(Q × Q, ℂ)) (D z : ℂ)
    (h : ∀ x y, c (x, y) = D * k (x, y) +
      z * ∫ t, a (x, t) * b (t, y) ∂μ) :
    continuousKernelOperator μ c = D • continuousKernelOperator μ k +
      z • (continuousKernelOperator μ a).comp (continuousKernelOperator μ b) := by
  have hc := ClassicalResolventIdentities.operator_identity_of_kernel_identity μ k a b c D z h
  have hd := ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  apply DFunLike.coe_injective
  apply hd.equalizer (continuousKernelOperator μ c).continuous
    (D • continuousKernelOperator μ k +
      z • (continuousKernelOperator μ a).comp (continuousKernelOperator μ b)).continuous
  funext f
  have he := congrArg (fun A : C(Q, ℂ) →L[ℂ] C(Q, ℂ) =>
    ContinuousMap.toLp 2 μ ℂ (A f)) hc
  simpa only [Function.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, map_add, map_smul,
    ← kernel_toLp] using he

lemma minor_operator_identity (k : C(Q × Q, ℂ)) (z : ℂ) :
    (1 - z • continuousKernelOperator μ k) *
      continuousKernelOperator μ (minorKernel μ k z) =
        FredholmDeterminantValue μ k z • continuousKernelOperator μ k := by
  have he := l2Operator_identity μ k k (minorKernel μ k z) (minorKernel μ k z)
    (FredholmDeterminantValue μ k z) z (fun x y => by
      simpa only [ClassicalEntireSeries.minor_kernel_identification μ k z] using
        (ClassicalResolventIdentities.kernel_identities μ k z x y).1)
  rw [sub_mul, one_mul, smul_mul_assoc]
  change continuousKernelOperator μ (minorKernel μ k z) - z •
    (continuousKernelOperator μ k).comp (continuousKernelOperator μ (minorKernel μ k z)) = _ 
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he)

lemma trace_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (c : ℂ) (T : H →L[ℂ] H) :
    TraceValue (c • T) = c * TraceValue T := by
  simp only [TraceValue, smul_apply, inner_smul_right, tsum_mul_left]

/-- The scalar and exterior determinants satisfy the same linear ODE wherever
I-zK is invertible. This uses the general diagonal trace, without positivity. -/
lemma classical_hasDerivAt_of_l2_unit (k : C(Q × Q, ℂ))
    (hk : IsTraceClassValue (continuousKernelOperator μ k)) (z : ℂ)
    (a : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)ˣ)
    (ha : (a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) = 1 - z • continuousKernelOperator μ k) :
    HasDerivAt (FredholmDeterminantValue μ k)
      (FredholmDeterminantValue μ k z *
        (-TraceValue ((↑(a⁻¹) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).comp
          (continuousKernelOperator μ k)))) z := by
  let T := continuousKernelOperator μ k
  let B := continuousKernelOperator μ (minorKernel μ k z)
  let U := (↑(a⁻¹) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).comp T
  have hU : IsTraceClassValue U :=
    (TraceDeterminantContinuity.traceNorm_comp_left_le _ T hk).1
  have hB : B = FredholmDeterminantValue μ k z • U := by
    have he : (a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) * B =
        FredholmDeterminantValue μ k z • T := by
      rw [ha]
      exact minor_operator_identity μ k z
    have he' := congrArg (fun X => (↑(a⁻¹) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) * X) he
    rw [← mul_assoc, Units.inv_mul, one_mul] at he'
    simpa only [mul_smul_comm, ContinuousLinearMap.mul_def] using he'
  have hBt : IsTraceClassValue B := by
    rw [hB]
    exact (TraceIdeals.TraceNormIdeal.traceClass_smul _ U hU).1
  have htrace := IntegralOperators.ContinuousTraceDiagonal.diagonal_trace Q μ
    (minorKernel μ k z) hBt
  have hd := ClassicalResolventIdentities.diagonal_derivative μ k z
  simp_rw [← ClassicalEntireSeries.minor_kernel_identification μ k z] at hd
  rw [← htrace] at hd
  change deriv (FredholmDeterminantValue μ k) z = -TraceValue B at hd
  rw [hB, trace_smul] at hd
  have hd' := ((ClassicalEntireSeries.entire_functions μ k).1 z).hasDerivAt
  convert hd' using 1
  rw [hd]
  ring

lemma exterior_negative_hasDerivAt_of_unit (k : C(Q × Q, ℂ))
    (hk : IsTraceClassValue (continuousKernelOperator μ k)) (z : ℂ)
    (a : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)ˣ)
    (ha : (a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) = 1 - z • continuousKernelOperator μ k) :
    HasDerivAt (fun w : ℂ => TraceClassDefinitions.Spec.FredholmDeterminantValue
      (continuousKernelOperator μ k) (-w))
      (TraceClassDefinitions.Spec.FredholmDeterminantValue (continuousKernelOperator μ k) (-z) *
        (-TraceValue ((↑(a⁻¹) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).comp
          (continuousKernelOperator μ k)))) z := by
  have hd := TraceFredholmDeterminant.determinant_hasDerivAt_of_unit
    (continuousKernelOperator μ k) hk (-z) a (by simpa only [neg_smul, sub_eq_add_neg, ContinuousLinearMap.one_def] using ha)
  have hh := hd.comp z ((hasDerivAt_id z).neg)
  convert hh using 1 <;> simp only [Function.comp_def, mul_neg, mul_one]

lemma determinant_comparison_near_zero (k : C(Q × Q, ℂ))
    (hk : IsTraceClassValue (continuousKernelOperator μ k)) :
    FredholmDeterminantValue μ k =ᶠ[𝓝 (0 : ℂ)]
      (fun z => TraceClassDefinitions.Spec.FredholmDeterminantValue
        (continuousKernelOperator μ k) (-z)) := by
  let T := continuousKernelOperator μ k
  let D := FredholmDeterminantValue μ k
  let E := fun z : ℂ => TraceClassDefinitions.Spec.FredholmDeterminantValue T (-z)
  have hD := (ClassicalEntireSeries.entire_functions μ k).1
  have hE : Differentiable ℂ E :=
    (TraceDeterminantContinuity.determinant_differentiable T hk).comp differentiable_neg
  have hD0 : D 0 = 1 := (ClassicalEntireSeries.values_at_zero μ k).1
  have hE0 : E 0 = 1 := by simpa only [E, neg_zero] using TraceClassDefinitions.determinant_at_zero (Lp ℂ 2 μ) T
  have hopen : IsOpen {z : ℂ | E z ≠ 0 ∧ IsUnit (1 - z • T)} :=
    (isOpen_ne_fun hE.continuous continuous_const).inter
      (Units.isOpen.preimage (continuous_const.sub (continuous_id.smul continuous_const)))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by
    refine ⟨by rw [hE0]; exact one_ne_zero, ?_⟩
    have h0 : (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) - (0 : ℂ) • T = 1 :=
      sub_eq_self.mpr (zero_smul ℂ T)
    exact h0.symm ▸ (isUnit_one : IsUnit (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)))
  have hq : DifferentiableOn ℂ (fun z => D z / E z) (Metric.ball 0 r) := by
    intro z hz
    exact ((hD z).div (hE z) (hball hz).1).differentiableWithinAt
  have hq' : (Metric.ball (0 : ℂ) r).EqOn (deriv (fun z => D z / E z)) 0 := by
    intro z hz
    let a := (hball hz).2.unit
    have ha : (a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) = 1 - z • T := (hball hz).2.unit_spec
    have hd := classical_hasDerivAt_of_l2_unit μ k hk z a ha
    have he := exterior_negative_hasDerivAt_of_unit μ k hk z a ha
    have hder := (hd.div he (hball hz).1).deriv
    change deriv (fun z => D z / E z) z = _ at hder
    change _ = (0 : ℂ)
    rw [hder]
    ring
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
  have heq := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) r).isPreconnected hq hq' (y := (0 : ℂ)) hz (by simp [hr])
  rw [hD0, hE0, div_one] at heq
  exact (div_eq_one_iff_eq (hball hz).1).mp heq

theorem trace_determinant_comparison : Spec.TraceDeterminantComparison.{u} := by
  intro Q _ _ _ _ μ _ k hk
  have hD := (ClassicalEntireSeries.entire_functions μ k).1
  have hE := (TraceDeterminantContinuity.determinant_differentiable
    (continuousKernelOperator μ k) hk).comp differentiable_neg
  have hh := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hD).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hE)
    (determinant_comparison_near_zero μ k hk)
  exact congrFun hh


lemma columns_iteratedKernel (k : C(Q × Q, ℂ)) (n : ℕ) (y : Q) :
    (KernelOperatorValue μ k ^ n) (ClassicalFredholm.columns k y) =
      ClassicalFredholm.columns (iteratedKernel μ k n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih]
    ext x
    rw [(ClassicalDefinitions.data_identification μ k).1]
    exact (iteratedKernel_formula μ k n x y).symm

lemma operatorDiagonal_pow (k : C(Q × Q, ℂ)) (n : ℕ) :
    ClassicalFredholm.operatorDiagonal μ k (KernelOperatorValue μ k ^ n) =
      diagonalCoefficient μ k n := by
  change (∫ t, (KernelOperatorValue μ k ^ n) (ClassicalFredholm.columns k t) t ∂μ) = _
  simp_rw [columns_iteratedKernel]
  rfl

lemma norm_smul_kernelOperator_lt_one (k : C(Q × Q, ℂ)) (z : ℂ)
    (hz : ‖z‖ * (μ.real Set.univ * ‖k‖) < 1) :
    ‖z • KernelOperatorValue μ k‖ < 1 := by
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left
    (PartV.ContinuousKernel.Spec.KernelOperatorValue_norm_le μ k) (norm_nonneg z)).trans_lt hz

lemma diagonal_resolvent_hasSum (k : C(Q × Q, ℂ)) (z : ℂ)
    (hz : ‖z‖ * (μ.real Set.univ * ‖k‖) < 1) :
    HasSum (fun n : ℕ => z ^ n * diagonalCoefficient μ k n)
      (ClassicalFredholm.operatorDiagonal μ k
        (Ring.inverse (1 - z • KernelOperatorValue μ k))) := by
  have hs := (hasSum_geom_series_inverse (z • KernelOperatorValue μ k)
    (norm_smul_kernelOperator_lt_one μ k z hz)).mapL (ClassicalFredholm.operatorDiagonal μ k)
  convert hs using 1
  funext n
  rw [smul_pow, map_smul, operatorDiagonal_pow, smul_eq_mul]

lemma classical_logDeriv_hasSum (k : C(Q × Q, ℂ)) (z : ℂ)
    (hz : ‖z‖ * (μ.real Set.univ * ‖k‖) < 1) :
    HasSum (fun n : ℕ => -(z ^ n * diagonalCoefficient μ k n))
      (deriv (FredholmDeterminantValue μ k) z / FredholmDeterminantValue μ k z) := by
  have hu := isUnit_one_sub_of_norm_lt_one (x := z • KernelOperatorValue μ k)
    (norm_smul_kernelOperator_lt_one μ k z hz)
  have hD := (ClassicalFredholm.invertibility μ k z).mp hu
  have he := ClassicalFredholm.derivative_eq_mul_inverse μ k z hu
  convert (diagonal_resolvent_hasSum μ k z hz).neg using 1
  rw [he]
  field_simp

noncomputable def logarithmicSum (k : C(Q × Q, ℂ)) (z : ℂ) : ℂ :=
  ∑' n : ℕ, -(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * diagonalCoefficient μ k n)

lemma logarithmicTerm_deriv (k : C(Q × Q, ℂ)) (n : ℕ) (z : ℂ) :
    deriv (fun w : ℂ => -(w ^ (n + 1) / ((n + 1 : ℕ) : ℂ) *
      diagonalCoefficient μ k n)) z = -(z ^ n * diagonalCoefficient μ k n) := by
  have hd : HasDerivAt (fun w : ℂ => -(w ^ (n + 1) / ((n + 1 : ℕ) : ℂ) *
      diagonalCoefficient μ k n)) _ z :=
    (((hasDerivAt_pow (n + 1) z).div_const ((n + 1 : ℕ) : ℂ)).mul_const
      (diagonalCoefficient μ k n)).neg
  rw [hd.deriv]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [Nat.add_sub_cancel]
  field_simp

lemma logarithmicSum_differentiableOn (k : C(Q × Q, ℂ)) (R : ℝ)
    (hR : R * (μ.real Set.univ * ‖k‖) < 1) (hR0 : 0 ≤ R) :
    DifferentiableOn ℂ (logarithmicSum μ k) (Metric.ball 0 R) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R,
        HasSum (fun n : ℕ => -(z ^ n * diagonalCoefficient μ k n))
          (deriv (logarithmicSum μ k) z) := by
  have hg := (summable_geometric_of_lt_one (by positivity :
    0 ≤ R * (μ.real Set.univ * ‖k‖)) hR).mul_right (R * (μ.real Set.univ * ‖k‖))
  have hf (n : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => -(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * diagonalCoefficient μ k n))
      (Metric.ball 0 R) := by fun_prop
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) :
      ‖-(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * diagonalCoefficient μ k n)‖ ≤
        (R * (μ.real Set.univ * ‖k‖)) ^ n * (R * (μ.real Set.univ * ‖k‖)) := by
    rw [← pow_succ]
    exact (norm_logarithmicTerm_le μ k z n).trans
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hz).le (by positivity)) _)
  refine ⟨Complex.differentiableOn_tsum_of_summable_norm hg hf Metric.isOpen_ball hb, ?_⟩
  intro z hz
  have hd := Complex.hasSum_deriv_of_summable_norm hg hf Metric.isOpen_ball hb hz
  change HasSum (fun n : ℕ => -(z ^ n * diagonalCoefficient μ k n))
    (deriv (fun w : ℂ => ∑' n : ℕ, -(w ^ (n + 1) / ((n + 1 : ℕ) : ℂ) *
      diagonalCoefficient μ k n)) z)
  simpa only [logarithmicTerm_deriv] using hd

theorem logarithmic_series : Spec.LogarithmicSeries.{u} := by
  intro Q _ _ _ _ μ _ k
  let A : ℝ := μ.real Set.univ * ‖k‖
  have hA : 0 ≤ A := by positivity
  let R : ℝ := (A + 1)⁻¹
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hR : R * A < 1 := by
    dsimp [R]
    rw [inv_mul_eq_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hseries := logarithmicSum_differentiableOn μ k R hR hR0.le
  let D := FredholmDeterminantValue μ k
  have hD := (ClassicalEntireSeries.entire_functions μ k).1
  have hD0 : D 0 = 1 := (ClassicalEntireSeries.values_at_zero μ k).1
  have hs : ∀ᶠ z : ℂ in 𝓝 0, D z ∈ Complex.slitPlane :=
    (hD.continuous.tendsto 0).eventually (Complex.isOpen_slitPlane.mem_nhds
      (by change D 0 ∈ Complex.slitPlane; rw [hD0]; exact Complex.one_mem_slitPlane))
  have hb : ∀ᶠ z : ℂ in 𝓝 0, z ∈ Metric.ball (0 : ℂ) R :=
    Metric.ball_mem_nhds (0 : ℂ) hR0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hb.and hs)
  have hmem {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) :
      z ∈ Metric.ball (0 : ℂ) R ∧ D z ∈ Complex.slitPlane := hball (Metric.mem_ball.mp hz)
  have hzA {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) : ‖z‖ * A < 1 :=
    (mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp (hmem hz).1).le hA).trans_lt hR
  have hlog : DifferentiableOn ℂ (fun z => Complex.log (D z)) (Metric.ball 0 r) :=
    hD.differentiableOn.clog (fun z hz => (hmem hz).2)
  have hF := hseries.1.mono (fun z hz => (hmem hz).1)
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) r,
      deriv (fun w => Complex.log (D w)) z = deriv (logarithmicSum μ k) z := by
    intro z hz
    have hl := ((hD z).hasDerivAt.clog (hmem hz).2).deriv
    have he := (classical_logDeriv_hasSum μ k z (hzA hz)).unique
      (hseries.2 z (hmem hz).1)
    exact hl.trans he
  have hdiff := hlog.sub hF
  have hzero : (Metric.ball (0 : ℂ) r).EqOn
      (deriv (fun z => Complex.log (D z) - logarithmicSum μ k z)) 0 := by
    intro z hz
    rw [deriv_fun_sub
      ((hlog z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      ((hF z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)), heq z hz, sub_self]
    rfl
  refine ⟨r, hr, fun z hz => ?_⟩
  have hz' : z ∈ Metric.ball (0 : ℂ) r := mem_ball_zero_iff.mpr hz
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) r).isPreconnected hdiff hzero
    (y := (0 : ℂ)) hz' (by simp [hr])
  have hF0 : logarithmicSum μ k 0 = 0 := by simp [logarithmicSum]
  change Complex.log (D z) - logarithmicSum μ k z =
    Complex.log (D 0) - logarithmicSum μ k 0 at hconst
  rw [hD0, Complex.log_one, hF0, sub_self] at hconst
  have hvalue := sub_eq_zero.mp hconst
  have hsum := (summable_logarithmic_terms μ k z (hzA hz')).hasSum
  rw [show (∑' n : ℕ, -(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) *
    diagonalCoefficient μ k n)) = logarithmicSum μ k z from rfl, ← hvalue] at hsum
  exact hsum

theorem multiplication_and_logarithmic_derivative :
    Spec.MultiplicationAndLogarithmicDerivative.{u} :=
  ⟨uniform_kernel_continuity, locally_uniform_kernel_limit, multiplication,
    scalar_multiplication, logarithmic_series, trace_power_coefficients,
    trace_determinant_comparison⟩

end ExpandedFA.FredholmDeterminant.ClassicalLogDerivative
