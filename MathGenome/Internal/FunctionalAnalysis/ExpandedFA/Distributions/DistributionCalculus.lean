import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionFiniteOrder
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus

open Set TopologicalSpace Filter
open scoped Distributions ContDiff Topology Manifold

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- Integration against a locally integrable density, retaining scalar linearity. -/
noncomputable def regularDistribution (μ : MeasureTheory.Measure (Domain d))
    (f : Domain d → 𝕜) : ScalarDistribution 𝕜 Ω :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul 𝕜 𝕜) μ f

@[simp] theorem regularDistribution_apply (μ : MeasureTheory.Measure (Domain d))
    (f : Domain d → 𝕜) (hf : MeasureTheory.LocallyIntegrableOn f Ω μ)
    (φ : Tests 𝕜 Ω) : regularDistribution μ f φ = ∫ x, f x * φ x ∂μ := by
  rw [regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral hf]
  congr 1
  funext x
  exact mul_comm _ _

theorem integration : Specs.ExpandedFA.Distributions.DistributionCalculus.integrationType := by
  intro 𝕜 _ d Ω μ f hf
  exact ⟨regularDistribution μ f, regularDistribution_apply μ f hf⟩

theorem testPartial_formula :
    Specs.ExpandedFA.Distributions.DistributionCalculus.testPartialFormulaType := by
  intro 𝕜 _ d Ω w φ
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change TestFunction.lineDerivCLM 𝕜 (coordinateVector i) (testPartialCLM w φ) x = _
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    change fderiv ℝ (testPartialCLM w φ) x (coordinateVector i) = _
    rw [ih]
    rfl

noncomputable def distributionDerivative :
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeType :=
  Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue

@[simp] theorem distributionDerivative_apply (w : List (Fin d))
    (u : ScalarDistribution 𝕜 Ω) (φ : Tests 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω w u φ = (-1 : 𝕜) ^ w.length * u (testPartialCLM w φ) := rfl

/-- The word representation has exactly the original multi-index order. -/
@[simp] theorem multiIndexWord_length (α : Fin d → ℕ) :
    (multiIndexWord α).length = ∑ i, α i := by
  simp [multiIndexWord, List.map_ofFn, List.sum_ofFn]

/-- Every coordinate occurs with precisely its prescribed multiplicity. -/
@[simp] theorem multiIndexWord_count (α : Fin d → ℕ) (i : Fin d) :
    (multiIndexWord α).count i = α i := by
  simp [multiIndexWord, List.count_flatMap, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, List.count_replicate, beq_iff_eq]

noncomputable def distributionMultiIndexDerivative :
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeType :=
  Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue

theorem multiIndex_formula :
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexFormulaType := by
  intro 𝕜 _ d Ω α u φ
  change distributionDerivative 𝕜 d Ω (multiIndexWord α) u φ = _
  rw [distributionDerivative_apply, multiIndexWord_length]

/-- Ordered partials are the actual multilinear Fréchet derivatives evaluated
on coordinate directions, linking the calculus to the upstream seminorms. -/
theorem partialFunction_ofFn (k : ℕ) (a : Fin k → Fin d)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ ∞ f) (x : Domain d) :
    partialFunction (List.ofFn a) f x =
      iteratedFDeriv ℝ k f x (fun j => coordinateVector (a j)) := by
  induction k generalizing x with
  | zero => simp [partialFunction]
  | succ k ih =>
    rw [List.ofFn_succ, partialFunction]
    have heq : partialFunction (List.ofFn (Fin.tail a)) f =
        fun y => iteratedFDeriv ℝ k f y (fun j => coordinateVector (Fin.tail a j)) :=
      funext fun y => ih (Fin.tail a) y
    change fderiv ℝ (partialFunction (List.ofFn (Fin.tail a)) f) x (coordinateVector (a 0)) = _
    rw [heq]
    symm
    exact DifferentiableAt.iteratedFDeriv_succ_apply_left'
      ((hf.iteratedFDeriv_right (m := 1) (i := k) (by simp)).differentiable (by simp) x)

/-- A smooth coefficient on Ω has a globally smooth representative near any
compact subset. Smooth Urysohn separation supplies a cutoff vanishing near Ωᶜ. -/
theorem smooth_extension_on_compact (a : SmoothCoefficient 𝕜 Ω)
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω) :
    ∃ g : Domain d → 𝕜, ContDiff ℝ ∞ g ∧ EqOn g a.val K := by
  obtain ⟨χ, hχ0, hχ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, Domain d)) Ω.isOpen.isClosed_compl K.isCompact.isClosed
    (disjoint_compl_left_iff.mpr hK) (n := ⊤)
  let g : Domain d → 𝕜 := fun x => χ x • a.val x
  have hχ : ContDiff ℝ ∞ χ := (contMDiff_iff_contDiff.mp χ.contMDiff)
  refine ⟨g, contDiff_iff_contDiffAt.mpr (fun x => ?_), ?_⟩
  · by_cases hx : x ∈ Ω
    · exact hχ.contDiffAt.smul ((a.property x hx).contDiffAt (Ω.isOpen.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
      have hz : ∀ᶠ y in 𝓝 x, χ y = 0 := hχ0.filter_mono (nhds_le_nhdsSet hx)
      filter_upwards [hz] with y hy
      simp [g, hy]
  · intro x hx
    have hx1 : χ x = 1 := hχ1.self_of_nhdsSet x hx
    simp [g, hx1]

/-- Multiplying a compactly supported test by a coefficient smooth on Ω remains
smooth globally, since the test vanishes on a neighbourhood of every point off Ω. -/
theorem smooth_mul_test (a : SmoothCoefficient 𝕜 Ω) (φ : Tests 𝕜 Ω) :
    ContDiff ℝ ∞ (fun x => a.val x * φ x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact ((a.property x (φ.tsupport_subset hx)).contDiffAt
      (Ω.isOpen.mem_nhds (φ.tsupport_subset hx))).mul φ.contDiff.contDiffAt
  · apply (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

noncomputable def coefficientMulTest (a : SmoothCoefficient 𝕜 Ω) (φ : Tests 𝕜 Ω) : Tests 𝕜 Ω :=
  ⟨fun x => a.val x * φ x, smooth_mul_test a φ,
    φ.hasCompactSupport.mul_left,
    (tsupport_mul_subset_right).trans φ.tsupport_subset⟩

@[simp] theorem coefficientMulTest_apply (a : SmoothCoefficient 𝕜 Ω) (φ : Tests 𝕜 Ω) (x) :
    coefficientMulTest a φ x = a.val x * φ x := rfl

/-- The LF universal property reduces continuity to multiplication by a global
extension on each compact step. No global regularity of a is assumed. -/
noncomputable def multiplyTestCLM (a : SmoothCoefficient 𝕜 Ω) :
    Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω :=
  TestFunction.mkCLM 𝕜 (coefficientMulTest a)
    (fun φ ψ => by ext x; simp [coefficientMulTest, mul_add])
    (fun c φ => by ext x; simp [coefficientMulTest, mul_left_comm])
    (fun K hK => by
      obtain ⟨g, hg, heq⟩ := smooth_extension_on_compact a K hK
      have h := ((TestFunction.bilinLeftCLM (ContinuousLinearMap.mul 𝕜 𝕜) hg).continuous).comp
        (TestFunction.continuous_ofSupportedIn (F := 𝕜) (n := ⊤) hK)
      apply h.congr
      intro φ
      ext x
      change φ x * g x = a.val x * φ x
      by_cases hx : x ∈ K
      · rw [heq hx, mul_comm]
      · rw [φ.zero_on_compl hx, Pi.zero_apply, zero_mul, mul_zero])

@[simp] theorem multiplyTestCLM_apply (a : SmoothCoefficient 𝕜 Ω)
    (φ : Tests 𝕜 Ω) (x) : multiplyTestCLM a φ x = a.val x * φ x := rfl

theorem test_multiplication :
    Specs.ExpandedFA.Distributions.DistributionCalculus.testMultiplicationType := by
  intro 𝕜 _ d Ω a
  exact ⟨multiplyTestCLM a, fun _ _ => rfl⟩

/-- Multiplication of a distribution by any smooth coefficient on its domain. -/
noncomputable def multiplyDistribution (a : SmoothCoefficient 𝕜 Ω)
    (u : ScalarDistribution 𝕜 Ω) : ScalarDistribution 𝕜 Ω :=
  u.comp (multiplyTestCLM a)

@[simp] theorem multiplyDistribution_apply (a : SmoothCoefficient 𝕜 Ω)
    (u : ScalarDistribution 𝕜 Ω) (φ : Tests 𝕜 Ω) :
    multiplyDistribution a u φ = u (multiplyTestCLM a φ) := rfl

theorem multiplication : Specs.ExpandedFA.Distributions.DistributionCalculus.multiplicationType := by
  intro 𝕜 _ d Ω a u
  exact ⟨multiplyDistribution a u, fun φ => ⟨multiplyTestCLM a φ, fun _ => rfl, rfl⟩⟩

@[simp] theorem testPartial_single_apply (i : Fin d) (φ : Tests 𝕜 Ω) (x) :
    testPartialCLM [i] φ x = fderiv ℝ φ x (coordinateVector i) := by
  rw [testPartial_formula 𝕜 d Ω [i] φ]
  rfl

/-- The ordinary product rule on tests, including points outside Ω. -/
theorem partial_multiplyTest (i : Fin d) (a : SmoothCoefficient 𝕜 Ω) (φ : Tests 𝕜 Ω) :
    testPartialCLM [i] (multiplyTestCLM a φ) =
      multiplyTestCLM (coefficientPartial i a) φ + multiplyTestCLM a (testPartialCLM [i] φ) := by
  ext x
  by_cases hx : x ∈ Ω
  · have ha : DifferentiableAt ℝ a.val x :=
      ((a.property x hx).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hφ : DifferentiableAt ℝ φ x := φ.contDiff.differentiable (by simp) x
    rw [testPartial_single_apply]
    change fderiv ℝ (fun y => a.val y * φ y) x (coordinateVector i) = _
    rw [show (fun y => a.val y * φ y) = a.val * (φ : Domain d → 𝕜) from rfl, fderiv_mul ha hφ]
    simp [coefficientPartial, mul_comm, add_comm]
  · rw [(testPartialCLM [i] (multiplyTestCLM a φ)).zero_on_compl hx,
      (multiplyTestCLM (coefficientPartial i a) φ +
        multiplyTestCLM a (testPartialCLM [i] φ)).zero_on_compl hx]

/-- The scalar-linear dual of the test product rule is the distribution Leibniz rule. -/
theorem distribution_leibniz (i : Fin d) (a : SmoothCoefficient 𝕜 Ω)
    (u : ScalarDistribution 𝕜 Ω) :
    -(multiplyDistribution a u).comp (testPartialCLM [i]) =
      multiplyDistribution (coefficientPartial i a) u +
      multiplyDistribution a (-u.comp (testPartialCLM [i])) := by
  ext φ
  have h := congrArg u (partial_multiplyTest i a φ)
  simp only [map_add] at h
  change -u (multiplyTestCLM a (testPartialCLM [i] φ)) =
    u (multiplyTestCLM (coefficientPartial i a) φ) + -u (testPartialCLM [i] (multiplyTestCLM a φ))
  rw [h]
  abel

theorem leibniz : Specs.ExpandedFA.Distributions.DistributionCalculus.leibnizType := by
  intro 𝕜 _ d Ω a u i
  exact ⟨coefficientPartial i a, multiplyTestCLM a, multiplyTestCLM (coefficientPartial i a),
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, distribution_leibniz i a u⟩

@[simp] theorem distributionDerivative_nil (u : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω [] u = u := by
  ext φ
  simp [distributionDerivative_apply, testPartialCLM]

theorem distributionDerivative_cons (i : Fin d) (w : List (Fin d))
    (u : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω (i :: w) u =
      distributionDerivative 𝕜 d Ω w (-u.comp (testPartialCLM [i])) := by
  ext φ
  simp [distributionDerivative_apply, testPartialCLM, pow_succ]

theorem distributionDerivative_add (w : List (Fin d)) (u v : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω w (u + v) =
      distributionDerivative 𝕜 d Ω w u + distributionDerivative 𝕜 d Ω w v := by
  ext φ
  simp [distributionDerivative_apply, mul_add]

/-- Every finite coordinate derivative satisfies the expanded product rule. -/
theorem full_leibniz :
    Specs.ExpandedFA.Distributions.DistributionCalculus.fullLeibnizType := by
  intro 𝕜 _ d Ω
  refine ⟨multiplyTestCLM, fun _ _ _ => rfl, ?_⟩
  intro w
  change ∀ a u, distributionDerivative 𝕜 d Ω w (multiplyDistribution a u) = _
  induction w with
  | nil =>
    intro a u
    exact distributionDerivative_nil _
  | cons i w ih =>
    intro a u
    rw [distributionDerivative_cons, distribution_leibniz, distributionDerivative_add]
    rw [ih, ih]
    rfl

section ScalarMeasures
open MeasureTheory

/-- Scalar multiplication commutes with the genuine scalar vector-measure
integral, even though its library construction is initially real-bilinear. -/
theorem scalar_measure_integral_smul (ν : VectorMeasure (Domain d) 𝕜)
    (c : 𝕜) (f : Domain d → 𝕜) :
    ν.integral (c • f) (ContinuousLinearMap.mul ℝ 𝕜) =
      c • ν.integral f (ContinuousLinearMap.mul ℝ 𝕜) := by
  apply setToFun_smul
  intro c s x
  simp [VectorMeasure.transpose, mul_left_comm]

/-- Any finite-variation scalar measure defines a scalar-linear map on tests. -/
noncomputable def finiteScalarMeasureLM (ν : VectorMeasure (Domain d) 𝕜)
    [IsFiniteMeasure ν.variation] : Tests 𝕜 Ω →ₗ[𝕜] 𝕜 where
  toFun φ := ν.integral φ (ContinuousLinearMap.mul ℝ 𝕜)
  map_add' φ ψ := VectorMeasure.integral_add
    (φ.integrable (locallyIntegrableOn_const (1 : ℝ)))
    (ψ.integrable (locallyIntegrableOn_const (1 : ℝ)))
  map_smul' c φ := scalar_measure_integral_smul ν c φ

/-- The order-zero estimate for integration against a finite scalar measure. -/
theorem finiteScalarMeasure_estimate (ν : VectorMeasure (Domain d) 𝕜)
    [IsFiniteMeasure ν.variation] (K : Compacts (Domain d))
    (hK : (K : Set (Domain d)) ⊆ Ω) (φ : Step 𝕜 K) :
    ‖finiteScalarMeasureLM (Ω := Ω) ν (TestFunction.ofSupportedIn hK φ)‖ ≤
      (‖ContinuousLinearMap.mul ℝ 𝕜‖ * ν.variation.real univ) * stepSeminorm 𝕜 K 0 φ := by
  have hφ : ∀ x, ‖φ x‖ ≤ stepSeminorm 𝕜 K 0 φ := by
    intro x
    have h := (step_seminorm_formula 𝕜 d K 0 φ _ (apply_nonneg _ _)).mp le_rfl
      0 le_rfl Fin.elim0 x
    simpa using h
  exact (VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := ν) (B := ContinuousLinearMap.mul ℝ 𝕜) (Filter.Eventually.of_forall hφ)).trans_eq
      (by ring)

/-- Finite scalar measures are continuous functionals for the LF topology. -/
noncomputable def finiteScalarMeasureDistribution (ν : VectorMeasure (Domain d) 𝕜)
    [IsFiniteMeasure ν.variation] : ScalarDistribution 𝕜 Ω :=
  { finiteScalarMeasureLM ν with
    cont := (finite_order_criterion 𝕜 d Ω (finiteScalarMeasureLM ν)).mpr fun K hK =>
      ⟨‖ContinuousLinearMap.mul ℝ 𝕜‖ * ν.variation.real univ,
        mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) ENNReal.toReal_nonneg, 0,
        finiteScalarMeasure_estimate ν K hK⟩ }

/-- The local scalar measure integral is independent of which compact containing
the support is used. This follows from actual restriction compatibility. -/
theorem localScalarMeasureIntegral_eq (μ : LocalScalarRadonMeasure 𝕜 Ω)
    (φ : Tests 𝕜 Ω) (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω)
    (hs : tsupport φ ⊆ K) :
    localScalarMeasureIntegral μ φ =
      (μ.onCompact K hK).integral φ (ContinuousLinearMap.mul ℝ 𝕜) := by
  let S : Compacts (Domain d) := ⟨tsupport φ, φ.hasCompactSupport⟩
  let L := S ⊔ K
  have hL : (L : Set (Domain d)) ⊆ Ω := union_subset φ.tsupport_subset hK
  let ν := μ.onCompact L hL
  have hS := VectorMeasure.setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := ν) (B := ContinuousLinearMap.mul ℝ 𝕜) S.isCompact.measurableSet
    (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have hK' := VectorMeasure.setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := ν) (B := ContinuousLinearMap.mul ℝ 𝕜) K.isCompact.measurableSet
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)))
  change (μ.onCompact S φ.tsupport_subset).integral φ _ = _
  rw [← μ.restrict_eq S φ.tsupport_subset L hL le_sup_left,
    ← μ.restrict_eq K hK L hL le_sup_right]
  exact hS.trans hK'.symm

/-- A locally finite scalar Radon measure defines an LF-continuous distribution;
its total mass need not be finite. -/
noncomputable def localScalarMeasureDistribution (μ : LocalScalarRadonMeasure 𝕜 Ω) :
    ScalarDistribution 𝕜 Ω :=
  TestFunction.limitCLM 𝕜 (localScalarMeasureIntegral μ)
    (fun K hK => by
      letI := μ.finiteVariation K hK
      exact (finiteScalarMeasureDistribution (μ.onCompact K hK)).comp
        (TestFunction.ofSupportedInCLM 𝕜 hK))
    (fun K hK φ => by
      change localScalarMeasureIntegral μ (TestFunction.ofSupportedIn hK φ) =
        (μ.onCompact K hK).integral (TestFunction.ofSupportedIn hK φ : Tests 𝕜 Ω) _
      exact localScalarMeasureIntegral_eq μ _ K hK φ.tsupport_subset)

@[simp] theorem localScalarMeasureDistribution_apply (μ : LocalScalarRadonMeasure 𝕜 Ω)
    (φ : Tests 𝕜 Ω) : localScalarMeasureDistribution μ φ = localScalarMeasureIntegral μ φ := rfl

theorem scalar_measure : Specs.ExpandedFA.Distributions.DistributionCalculus.scalarMeasureType := by
  intro 𝕜 _ d Ω μ
  exact ⟨localScalarMeasureDistribution μ, fun _ => rfl⟩

/-- The usual finite scalar measure embeds by its actual compact restrictions. -/
noncomputable def LocalScalarRadonMeasure.ofFinite (ν : VectorMeasure (Domain d) 𝕜)
    [IsFiniteMeasure ν.variation] : LocalScalarRadonMeasure 𝕜 Ω where
  onCompact K _ := ν.restrict K
  finiteVariation _ _ := inferInstance
  restrict_eq K _ L _ hKL := by
    rw [ν.restrict_restrict K.isCompact.measurableSet L.isCompact.measurableSet,
      inter_eq_left.mpr hKL]

/-- This embedding preserves the genuine scalar-measure integral. -/
theorem localScalarMeasureIntegral_ofFinite (ν : VectorMeasure (Domain d) 𝕜)
    [IsFiniteMeasure ν.variation] (φ : Tests 𝕜 Ω) :
    localScalarMeasureIntegral (LocalScalarRadonMeasure.ofFinite ν) φ =
      ν.integral φ (ContinuousLinearMap.mul ℝ 𝕜) := by
  apply VectorMeasure.setIntegral_eq_integral_of_forall_compl_eq_zero
    φ.hasCompactSupport.measurableSet
  intro x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- The chart variations really are Radon measures, rather than arbitrary
nonregular measure extensions. -/
theorem LocalScalarRadonMeasure.regular (μ : LocalScalarRadonMeasure 𝕜 Ω)
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω) :
    Measure.Regular (μ.onCompact K hK).variation := by
  let := μ.finiteVariation K hK
  infer_instance

end ScalarMeasures

end ExpandedFA.Distributions
