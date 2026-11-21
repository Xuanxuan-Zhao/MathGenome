import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.ReflexiveSpaceWithoutAP
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.TraceObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.TraceOneZeroOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.FiniteDimensionalBanachSumReflexivity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.ComplementedAPAndComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15CompactApproximation

noncomputable section
namespace ExpandedFA.AP.ReflexiveSpaceWithoutAP
open ExpandedFA.P1.C15Basis ExpandedFA.P1.C15CoordinateContinuity
open ExpandedFA.P1.C15CompactApproximation
open Compactness

/-- The bounded finite-rank partial sums approximate the identity on every
compact set. No operator-norm bound is added to the definition of AP. -/
theorem schauderBasis_implies_ap : Spec.SchauderBasisImpliesAP := by
  intro 𝕜 E _ _ _ _ e h
  classical
  apply (hasApproximationProperty_iff_pointwise 𝕜 E).mpr
  intro K hK ε hε
  obtain ⟨b, _, _, hbp⟩ := raw_native_basis h
  obtain ⟨N, hN⟩ := raw_basis_uniform_compact_convergence h K hK ε hε
  refine ⟨b.proj N, ?_, ?_⟩
  · rw [b.range_proj_eq_span]
    exact FiniteDimensional.span_of_finite 𝕜 ((Finset.range N).finite_toSet.image b)
  · intro x hx
    simpa only [hbp] using hN N le_rfl x hx

/-- The finite-list convention, including the empty basis, also implies AP. -/
theorem finiteBasis_implies_ap : Spec.FiniteBasisImpliesAP := by
  intro 𝕜 E _ _ _ _ d e h
  let := finiteBasis_finiteDimensional h
  apply (hasApproximationProperty_iff_pointwise 𝕜 E).mpr
  intro K _ ε hε
  refine ⟨ContinuousLinearMap.id 𝕜 E, inferInstance, ?_⟩
  intro x _
  simpa using hε

/-- The absolutely convergent rank-one series has trace one and zero operator,
so the trace obstruction applies to the original ordinary AP. -/
theorem constructed_space_without_ap : Spec.ConstructedSpaceWithoutAP := by
  intro D
  let := EnfloSpace.x_complete D
  obtain ⟨l, _, _, _, habs, htrace, _, hzero⟩ :=
    TraceOneZeroOperator.trace_one_zero_series D
  apply trace_obstruction ℝ (EnfloSpace.X D)
    (fun j => (SummableTensorFlatteningSpec.flattenedPair l j).1)
    (fun j => (SummableTensorFlatteningSpec.flattenedPair l j).2) habs
    (fun x => (hzero x).tsum_eq)
  rw [htrace.tsum_eq]
  exact one_ne_zero

/-- An actual incidence family supplies a separable reflexive real Banach
space without AP; neither an infinite nor a finite Schauder basis can exist. -/
theorem real_counterexample : Spec.RealCounterexample := by
  obtain ⟨D⟩ := EnfloSpace.data_exists
  let := EnfloSpace.x_complete D
  refine ⟨EnfloSpace.X D, inferInstance, inferInstance, inferInstance,
    EnfloSpace.x_separable D,
    FiniteDimensionalBanachSumReflexivity.closed_span_reflexive D,
    constructed_space_without_ap D, ?_, ?_⟩
  · intro e h
    exact constructed_space_without_ap D (schauderBasis_implies_ap h)
  · intro d e h
    exact constructed_space_without_ap D (finiteBasis_implies_ap h)

/-- The complete complexification has a complemented real copy of the real
counterexample, so complex AP would imply the impossible real AP. -/
theorem complex_counterexample : Spec.ComplexCounterexample := by
  obtain ⟨D⟩ := EnfloSpace.data_exists
  let := EnfloSpace.x_complete D
  obtain ⟨C⟩ := exists_completeComplexification (EnfloSpace.X D)
  refine ⟨C.carrier, inferInstance, inferInstance, inferInstance, ?_⟩
  intro h
  exact constructed_space_without_ap D (C.ap_implies h)

end ExpandedFA.AP.ReflexiveSpaceWithoutAP
