import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.LawsAndTransfer
import Mathlib.Probability.Independence.CharacteristicFunction
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.CharacteristicBasics

/-! Proposition 7.1 (paper.tex:2375–2395) and its finite independent-sum consequence.
The difference estimate and quadratic-form identity use bounded exponential
kernels, so no moment assumptions or completeness of the probability space
are needed. All statements include dimension zero and empty finite families. -/

open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate

namespace ProbabilityFoundations.Ch07

universe u v

variable {d : ℕ}

theorem characteristicFunction_zero (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ] :
    characteristicFunction μ 0 = 1 := by
  simp [characteristicFunction]

theorem characteristicFunction_neg (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ]
    (t : Euclidean d) :
    characteristicFunction μ (-t) = conj (characteristicFunction μ t) :=
  charFun_neg t

theorem norm_characteristicFunction_le_one (μ : Measure (Euclidean d))
    [IsProbabilityMeasure μ] (t : Euclidean d) : ‖characteristicFunction μ t‖ ≤ 1 :=
  norm_charFun_le_one t

theorem characteristicFunction_convolution (μ ν : Measure (Euclidean d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : Euclidean d) :
    characteristicFunction (convolution μ ν) t =
      characteristicFunction μ t * characteristicFunction ν t :=
  charFun_conv t

theorem characteristicFunction_independent_sum
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → Euclidean d) (hX : Measurable X) (hY : Measurable Y)
    (hInd : ProbabilityTheory.IndepFun X Y P) (t : Euclidean d) :
    characteristicFunction (Ch01.law P (fun ω => X ω + Y ω)) t =
      characteristicFunction (Ch01.law P X) t * characteristicFunction (Ch01.law P Y) t := by
  exact congrFun (hInd.charFun_map_fun_add_eq_mul hX.aemeasurable hY.aemeasurable) t

theorem characteristicFunction_independent_finite_sum
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → Euclidean d)
    (hX : ∀ i, Measurable (X i)) (hInd : Ch02.IndependentRandomElements P X)
    (s : Finset I) (t : Euclidean d) :
    characteristicFunction (Ch01.law P (fun ω => ∑ i ∈ s, X i ω)) t =
      ∏ i ∈ s, characteristicFunction (Ch01.law P (X i)) t := by
  have h := (Ch02.independentRandomElements_iff_iIndepFun P X).mp hInd
  simpa only [Finset.prod_apply, characteristicFunction, Ch01.law] using
    congrFun ((h.restrict s).charFun_map_fun_finsetSum_eq_prod
      (fun i _ => (hX i).aemeasurable)) t

/-- The unit-modulus exponential appearing in the characteristic integral. -/
private noncomputable def kernel (t x : Euclidean d) : ℂ :=
  Complex.exp ((inner ℝ x t : ℂ) * Complex.I)

private lemma norm_kernel (t x : Euclidean d) : ‖kernel t x‖ = 1 := by
  simp [kernel]

private lemma integrable_kernel (μ : Measure (Euclidean d)) [IsFiniteMeasure μ]
    (t : Euclidean d) : Integrable (kernel t) μ := by
  exact (BoundedContinuousFunction.innerProbChar t).integrable μ

private lemma kernel_sub (a b x : Euclidean d) :
    kernel (a - b) x = kernel a x * conj (kernel b x) := by
  unfold kernel
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_right, Complex.ofReal_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The source's quadratic form is the integral of a squared modulus. -/
private theorem characteristicQuadraticForm_eq_integral (μ : Measure (Euclidean d))
    [IsProbabilityMeasure μ] {n : ℕ} (t : Fin n → Euclidean d) (c : Fin n → ℂ) :
    characteristicQuadraticForm (characteristicFunction μ) t c =
      ((∫ x, ‖∑ j, c j * kernel (t j) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hint (j k : Fin n) :
      Integrable (fun x => c j * conj (c k) * kernel (t j - t k) x) μ :=
    (integrable_kernel μ _).const_mul _
  calc
    _ = ∫ x, ∑ j, ∑ k, c j * conj (c k) * kernel (t j - t k) x ∂μ := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun k _ => hint j k)]
      simp only [integral_const_mul, characteristicFunction,
        charFun, kernel]
    _ = ∫ x, ((‖∑ j, c j * kernel (t j) x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      rw [Finset.sum_mul]
      simp only [map_sum, map_mul, Finset.mul_sum, kernel_sub]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := integral_ofReal

theorem characteristicFunction_positiveDefinite (μ : Measure (Euclidean d))
    [IsProbabilityMeasure μ] : IsPositiveDefinite (characteristicFunction μ) := by
  intro n t c
  rw [characteristicQuadraticForm_eq_integral]
  constructor
  · simp
  · simpa using integral_nonneg (μ := μ) (fun x => sq_nonneg ‖∑ j, c j * kernel (t j) x‖)

/-- The bound depends only on the difference of the frequencies. -/
private lemma characteristicFunction_difference_bound (μ : Measure (Euclidean d))
    [IsProbabilityMeasure μ] (a b : Euclidean d) :
    ‖characteristicFunction μ a - characteristicFunction μ b‖ ≤
      ∫ x, ‖kernel (a - b) x - 1‖ ∂μ := by
  change ‖(∫ x, kernel a x ∂μ) - ∫ x, kernel b x ∂μ‖ ≤ _
  rw [← integral_sub (integrable_kernel μ a) (integrable_kernel μ b)]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [] with x
  have h : kernel a x - kernel b x = (kernel (a - b) x - 1) * kernel b x := by
    rw [kernel_sub]
    have hc : conj (kernel b x) * kernel b x = 1 := by
      rw [mul_comm, Complex.mul_conj', norm_kernel]
      norm_num
    calc
      _ = kernel a x * (conj (kernel b x) * kernel b x) - kernel b x := by rw [hc, mul_one]
      _ = _ := by ring
  rw [h, norm_mul, norm_kernel, mul_one]

theorem characteristicFunction_uniformContinuous (μ : Measure (Euclidean d))
    [IsProbabilityMeasure μ] : UniformContinuous (characteristicFunction μ) := by
  let F : Euclidean d → ℝ := fun h => ∫ x, ‖kernel h x - 1‖ ∂μ
  have hF : Continuous F := by
    apply continuous_of_dominated (bound := fun _ => (2 : ℝ))
    · intro h
      exact (by unfold kernel; fun_prop : Continuous (fun x => ‖kernel h x - 1‖)).aestronglyMeasurable
    · intro h
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_norm] using
        (norm_sub_le (kernel h x) 1).trans_eq (by rw [norm_kernel]; norm_num)
    · exact integrable_const _
    · filter_upwards [] with x
      unfold kernel
      fun_prop
  have hzero : F 0 = 0 := by simp [F, kernel]
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.mp hF.continuousAt ε hε
  refine ⟨δ, hδ, fun {a b} hab => ?_⟩
  have hsmall : ‖F (a - b)‖ < ε := by
    simpa [hzero, dist_eq_norm] using hδF (show dist (a - b) 0 < δ by
      simpa [dist_eq_norm] using hab)
  calc
    dist (characteristicFunction μ a) (characteristicFunction μ b)
      ≤ F (a - b) := by simpa [dist_eq_norm, F] using characteristicFunction_difference_bound μ a b
    _ ≤ ‖F (a - b)‖ := le_abs_self _
    _ < ε := hsmall

end ProbabilityFoundations.Ch07

