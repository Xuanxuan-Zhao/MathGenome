import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BoundedBorelBidual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov

noncomputable section

namespace ExpandedFA.Supplements.BoundedBorelBidual

open MeasureTheory Set
open scoped ENNReal ZeroAtInfty
open BoundedBorelBidualSpec
open FunctionSpaces.ScalarRieszMarkovSpec
open FunctionSpaces.ScalarRieszMarkov
open FunctionSpaces.PositiveRadonRepresentation
universe u

variable {K : Type u} [MeasurableSpace K] {𝕜 : Type} [RCLike 𝕜]

@[simp] theorem coe_add (h g : BoundedBorel K 𝕜) :
    ⇑(h + g) = fun x => h x + g x := rfl

@[simp] theorem coe_smul (c : 𝕜) (h : BoundedBorel K 𝕜) :
    ⇑(c • h) = fun x => c • h x := rfl

theorem measurable (h : BoundedBorel K 𝕜) : Measurable (h : K → 𝕜) := h.property

theorem norm_apply_le (h : BoundedBorel K 𝕜) (x : K) : ‖h x‖ ≤ ‖h‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero h.val x

theorem norm_le (h : BoundedBorel K 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖h x‖ ≤ C) : ‖h‖ ≤ C :=
  lp.norm_le_of_forall_le hC hbound

theorem integrable (h : BoundedBorel K 𝕜) (μ : Measure K) [IsFiniteMeasure μ] :
    Integrable h μ :=
  Integrable.mono' (integrable_const ‖h‖) (measurable h).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_apply_le h))

theorem integral_bound (h : BoundedBorel K 𝕜) (ν : VectorMeasure K 𝕜)
    [IsFiniteMeasure ν.variation] :
    ‖scalarIntegral ν h‖ ≤ ‖h‖ * ν.variation.real univ := by
  calc
    _ ≤ ‖h‖ * ‖ContinuousLinearMap.mul ℝ 𝕜‖ * ν.variation.real univ :=
      VectorMeasure.norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (norm_apply_le h))
    _ ≤ ‖h‖ * 1 * ν.variation.real univ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ 𝕜
    _ = _ := by ring

/-- Scalar linearity in the measure, including complex scalars. -/
theorem scalarIntegral_smul_measure (ν : VectorMeasure K 𝕜) (c : 𝕜) (f : K → 𝕜) :
    scalarIntegral (c • ν) f = c • scalarIntegral ν f := by
  let T := ν.transpose (ContinuousLinearMap.mul ℝ 𝕜)
  let U := (c • ν).transpose (ContinuousLinearMap.mul ℝ 𝕜)
  let A : 𝕜 →L[ℝ] 𝕜 := (ContinuousLinearMap.mul ℝ 𝕜) c
  have hT := dominatedFinMeasAdditive_cbmApplyMeasure ν (ContinuousLinearMap.mul ℝ 𝕜)
  have hU : DominatedFinMeasAdditive ν.variation U
      (‖c‖ * ‖ContinuousLinearMap.mul ℝ 𝕜‖) := by
    have heq : U = fun s => c • T s := by
      funext s
      ext z
      change z * (c * ν s) = c * (z * ν s)
      ring
    rw [heq]
    exact hT.smul c
  have hscaled := dominatedFinMeasAdditive_cbmApplyMeasure (c • ν)
    (ContinuousLinearMap.mul ℝ 𝕜)
  have hscaled' : DominatedFinMeasAdditive (‖c‖₊ • ν.variation) U
      ‖ContinuousLinearMap.mul ℝ 𝕜‖ := by
    simpa only [VectorMeasure.variation_smul] using hscaled
  change setToFun (c • ν).variation U hscaled f = A (setToFun ν.variation T hT f)
  calc
    _ = setToFun ν.variation U hU f := by
      simpa only [VectorMeasure.variation_smul] using
        (setToFun_congr_smul_measure' ‖c‖₊ hU hscaled' f).symm
    _ = _ := by
      apply setToFun_postcompose hT hU A
      intro s hs hsf
      ext z
      change z * (c * ν s) = c * (z * ν s)
      ring

section Compact

variable [TopologicalSpace K] [CompactSpace K] [T2Space K] [BorelSpace K]

omit [CompactSpace K] in
/-- Finite scalar Radon measures form a vector space. -/
theorem finiteScalarRadon_add (ν η : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η) :
    FiniteScalarRadon (ν + η) := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : IsFiniteMeasure η.variation := ⟨hη.1⟩
  have : ν.variation.Regular := (positiveRadon_iff_regular _).mp hν.2
  have : η.variation.Regular := (positiveRadon_iff_regular _).mp hη.2
  have : (ν.variation + η.variation).Regular := regular_add _ _
  have hv := VectorMeasure.variation_add_le (μ := ν) (ν := η)
  have : IsFiniteMeasure (ν + η).variation := isFiniteMeasure_of_le _ hv
  exact ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr (regular_of_le hv)⟩

omit [CompactSpace K] [T2Space K] [BorelSpace K] in
theorem finiteScalarRadon_smul (ν : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (c : 𝕜) : FiniteScalarRadon (c • ν) := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : ν.variation.Regular := (positiveRadon_iff_regular _).mp hν.2
  refine ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr ?_⟩
  rw [VectorMeasure.variation_smul]
  infer_instance

/-- Continuous tests on the compact space determine a finite scalar Radon measure. -/
theorem continuous_tests_injective (ν η : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η)
    (h : ∀ f : C(K, 𝕜), scalarIntegral ν f = scalarIntegral η f) : ν = η := by
  obtain ⟨e, _, he⟩ := compact_identification K 𝕜
  apply scalarIntegral_injective ν η hν hη
  intro f
  have heq : (e.symm f : K → 𝕜) = f := funext (he f)
  simpa only [heq] using h (e.symm f)

/-- Transport the accepted representation theorem from `C₀(K)` to `C(K)`. -/
theorem exists_representing_measure (hr : ScalarRepresentation.{u} 𝕜)
    (L : StrongDual 𝕜 C(K, 𝕜)) :
    ∃ ν : VectorMeasure K 𝕜, FiniteScalarRadon ν ∧
      (∀ f : C(K, 𝕜), L f = scalarIntegral ν f) ∧ ‖L‖ = ν.variation.real univ := by
  obtain ⟨e, he, _⟩ := compact_identification K 𝕜
  obtain ⟨ν, hν, hrep, hn, _⟩ := hr K (L.comp e.symm.toLinearIsometry.toContinuousLinearMap)
  refine ⟨ν, hν, ?_, ?_⟩
  · intro f
    have heq : (e f : K → 𝕜) = f := funext (he f)
    have hf := (hrep (e f)).2
    change L (e.symm (e f)) = scalarIntegral ν (e f) at hf
    simpa only [e.symm_apply_apply, heq] using hf
  · exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv L e.symm).symm.trans hn

/-- A chosen representative is used only internally; uniqueness makes the
result independent of the choice. -/
def representingMeasure (hr : ScalarRepresentation.{u} 𝕜)
    (L : StrongDual 𝕜 C(K, 𝕜)) : VectorMeasure K 𝕜 :=
  (exists_representing_measure hr L).choose

theorem representingMeasure_properties (hr : ScalarRepresentation.{u} 𝕜)
    (L : StrongDual 𝕜 C(K, 𝕜)) :
    FiniteScalarRadon (representingMeasure hr L) ∧
      (∀ f : C(K, 𝕜), L f = scalarIntegral (representingMeasure hr L) f) ∧
      ‖L‖ = (representingMeasure hr L).variation.real univ :=
  (exists_representing_measure hr L).choose_spec

theorem representingMeasure_eq (hr : ScalarRepresentation.{u} 𝕜)
    (L : StrongDual 𝕜 C(K, 𝕜)) (ν : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hL : ∀ f : C(K, 𝕜), L f = scalarIntegral ν f) :
    representingMeasure hr L = ν := by
  apply continuous_tests_injective _ _ (representingMeasure_properties hr L).1 hν
  intro f
  exact ((representingMeasure_properties hr L).2.1 f).symm.trans (hL f)

theorem representingMeasure_add (hr : ScalarRepresentation.{u} 𝕜)
    (L M : StrongDual 𝕜 C(K, 𝕜)) :
    representingMeasure hr (L + M) = representingMeasure hr L + representingMeasure hr M := by
  have hL := representingMeasure_properties hr L
  have hM := representingMeasure_properties hr M
  have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
  have : IsFiniteMeasure (representingMeasure hr M).variation := ⟨hM.1.1⟩
  apply representingMeasure_eq hr (L + M) _ (finiteScalarRadon_add _ _ hL.1 hM.1)
  intro f
  change L f + M f = _
  rw [hL.2.1 f, hM.2.1 f]
  exact (VectorMeasure.integral_add_vectorMeasure ((BoundedContinuousFunction.mkOfCompact f).integrable _)
    ((BoundedContinuousFunction.mkOfCompact f).integrable _)).symm

theorem representingMeasure_smul (hr : ScalarRepresentation.{u} 𝕜)
    (c : 𝕜) (L : StrongDual 𝕜 C(K, 𝕜)) :
    representingMeasure hr (c • L) = c • representingMeasure hr L := by
  have hL := representingMeasure_properties hr L
  apply representingMeasure_eq hr (c • L) _ (finiteScalarRadon_smul _ hL.1 c)
  intro f
  change c • L f = _
  rw [hL.2.1 f, scalarIntegral_smul_measure]

/-- Integration of a bounded Borel function against the representing measure
is a bounded scalar-linear functional on the continuous dual. -/
def integrationFunctional (hr : ScalarRepresentation.{u} 𝕜) (h : BoundedBorel K 𝕜) :
    StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜)) :=
  LinearMap.mkContinuous
    { toFun := fun L => scalarIntegral (representingMeasure hr L) h
      map_add' := by
        intro L M
        have hL := representingMeasure_properties hr L
        have hM := representingMeasure_properties hr M
        have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
        have : IsFiniteMeasure (representingMeasure hr M).variation := ⟨hM.1.1⟩
        rw [representingMeasure_add]
        exact VectorMeasure.integral_add_vectorMeasure (integrable h _) (integrable h _)
      map_smul' := by
        intro c L
        rw [representingMeasure_smul, scalarIntegral_smul_measure]
        rfl }
    ‖h‖ (by
      intro L
      change ‖scalarIntegral (representingMeasure hr L) h‖ ≤ ‖h‖ * ‖L‖
      have hL := representingMeasure_properties hr L
      have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
      simpa only [hL.2.2] using integral_bound h (representingMeasure hr L))

@[simp] theorem integrationFunctional_apply (hr : ScalarRepresentation.{u} 𝕜)
    (h : BoundedBorel K 𝕜) (L : StrongDual 𝕜 C(K, 𝕜)) :
    integrationFunctional hr h L = scalarIntegral (representingMeasure hr L) h := rfl

theorem integrationFunctional_norm_le (hr : ScalarRepresentation.{u} 𝕜)
    (h : BoundedBorel K 𝕜) : ‖integrationFunctional hr h‖ ≤ ‖h‖ := by
  apply (integrationFunctional hr h).opNorm_le_bound (norm_nonneg h)
  intro L
  have hL := representingMeasure_properties hr L
  have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
  simpa only [integrationFunctional_apply, hL.2.2] using
    integral_bound h (representingMeasure hr L)

omit [CompactSpace K] in
/-- Point masses are regular without a metrizability assumption on `K`. -/
theorem dirac_regular (x : K) : (Measure.dirac x).Regular := by
  apply regular_of_small_compact_complements
  intro A hA ε hε
  by_cases hx : x ∈ A
  · refine ⟨{x}, singleton_subset_iff.mpr hx, isCompact_singleton, ?_⟩
    simpa using (bot_lt_iff_ne_bot.mpr hε : (0 : ℝ≥0∞) < ε)
  · refine ⟨∅, empty_subset _, isCompact_empty, ?_⟩
    simpa [Measure.dirac_apply', hx] using (bot_lt_iff_ne_bot.mpr hε : (0 : ℝ≥0∞) < ε)

omit [CompactSpace K] in
theorem finiteScalarRadon_dirac (x : K) :
    FiniteScalarRadon (VectorMeasure.dirac x (1 : 𝕜)) := by
  have hv : (VectorMeasure.dirac x (1 : 𝕜)).variation = Measure.dirac x := by
    simp [VectorMeasure.variation_dirac]
  refine ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr ?_⟩
  rw [hv]
  exact dirac_regular x

/-- Dirac tests give the value at each point, before taking any supremum. -/
theorem integrationFunctional_eval (hr : ScalarRepresentation.{u} 𝕜)
    (h : BoundedBorel K 𝕜) (x : K) :
    integrationFunctional hr h (ContinuousMap.evalCLM 𝕜 x) = h x := by
  have heq : representingMeasure hr (ContinuousMap.evalCLM 𝕜 x) =
      VectorMeasure.dirac x (1 : 𝕜) := by
    apply representingMeasure_eq hr _ _ (finiteScalarRadon_dirac x)
    intro f
    simp [scalarIntegral]
  rw [integrationFunctional_apply, heq]
  simp [scalarIntegral]

/-- Norm equality uses only pointwise lower bounds, so it covers both an
unattained supremum and the empty compact space. -/
theorem integrationFunctional_norm (hr : ScalarRepresentation.{u} 𝕜)
    (h : BoundedBorel K 𝕜) : ‖integrationFunctional hr h‖ = ‖h‖ := by
  apply le_antisymm (integrationFunctional_norm_le hr h)
  apply norm_le h (norm_nonneg (integrationFunctional hr h))
  intro x
  have hev : ‖(ContinuousMap.evalCLM 𝕜 x : StrongDual 𝕜 C(K, 𝕜))‖ ≤ 1 := by
    apply (ContinuousMap.evalCLM 𝕜 x : StrongDual 𝕜 C(K, 𝕜)).opNorm_le_bound zero_le_one
    intro f
    simpa using f.norm_coe_le_norm x
  calc
    ‖h x‖ = ‖integrationFunctional hr h (ContinuousMap.evalCLM 𝕜 x)‖ := by
      rw [integrationFunctional_eval]
    _ ≤ ‖integrationFunctional hr h‖ * ‖(ContinuousMap.evalCLM 𝕜 x : StrongDual 𝕜 C(K, 𝕜))‖ :=
      (integrationFunctional hr h).le_opNorm _
    _ ≤ ‖integrationFunctional hr h‖ :=
      mul_le_of_le_one_right (norm_nonneg (integrationFunctional hr h)) hev

/-- The bounded Borel inclusion in the bidual. -/
def borelEmbedding (hr : ScalarRepresentation.{u} 𝕜) :
    BoundedBorel K 𝕜 →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜)) where
  toFun := integrationFunctional hr
  map_add' h g := by
    ext L
    have hL := representingMeasure_properties hr L
    have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
    exact VectorMeasure.integral_fun_add (integrable h _) (integrable g _)
  map_smul' c h := by
    ext L
    exact scalarIntegral_smul _ c h
  norm_map' := integrationFunctional_norm hr

/-- The internal construction agrees with integration against every finite
Radon measure, independently of all choices made in Riesz--Markov. -/
theorem borelEmbedding_integral (hr : ScalarRepresentation.{u} 𝕜)
    (h : BoundedBorel K 𝕜) (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν)
    (L : StrongDual 𝕜 C(K, 𝕜)) (hL : ∀ f : C(K, 𝕜), L f = scalarIntegral ν f) :
    borelEmbedding hr h L = scalarIntegral ν h := by
  change scalarIntegral (representingMeasure hr L) h = _
  rw [representingMeasure_eq hr L ν hν hL]

end Compact

theorem borelEmbedding_of_representation (hr : ScalarRepresentation.{u} 𝕜) :
    BorelEmbedding.{u} 𝕜 := by
  intro K _ _ _ _ _
  refine ⟨borelEmbedding hr, ?_⟩
  intro h ν hν
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  exact ⟨integrable h _, fun L hL => borelEmbedding_integral hr h ν hν L hL⟩

/-- The real assertion, for arbitrary compact Hausdorff spaces including `∅`. -/
theorem real_borel_embedding : BorelEmbedding.{u} ℝ :=
  borelEmbedding_of_representation real_representation

/-- The complex assertion uses a scalar-linear dual and multiplication pairing. -/
theorem complex_borel_embedding : BorelEmbedding.{u} ℂ :=
  borelEmbedding_of_representation complex_representation


end ExpandedFA.Supplements.BoundedBorelBidual
