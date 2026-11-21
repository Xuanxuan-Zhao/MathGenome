import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorEstimates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FiniteDomainOperators

/-! Operator norm axioms and estimates, without completeness hypotheses.
The native operator maps carry precisely the norm and operations fixed by
the accepted operator-space interface. Finite coordinates and norm comparisons
reuse the accepted finite-domain results without additional assumptions. -/

namespace ExpandedFA.P1.C03OperatorEstimates

theorem operator_norm_axioms : Spec.OperatorNormAxioms := by
  intro 𝕜 E F _ _ _ _ _
  exact ⟨⟨norm_nonneg, norm_smul, norm_add_le⟩, fun _ => norm_eq_zero⟩

theorem operator_evaluation_bound : Spec.EvaluationBound := by
  intro 𝕜 E F _ _ _ _ _ T x
  exact T.le_opNorm x

theorem operator_composition_bound : Spec.CompositionBound := by
  intro 𝕜 E F G _ _ _ _ _ _ _ S T
  exact S.opNorm_comp_le T

theorem operator_domain_restriction_bound : Spec.DomainRestrictionBound := by
  intro 𝕜 E F _ _ _ _ _ T M
  exact (T.domRestrict M).opNorm_le_bound (norm_nonneg T) fun x => T.le_opNorm x

theorem operator_codomain_restriction_norm : Spec.CodomainRestrictionNorm := by
  intro 𝕜 E F _ _ _ _ _ T N h
  apply le_antisymm
  · exact (T.codRestrict N h).opNorm_le_bound (norm_nonneg T) fun x => T.le_opNorm x
  · exact T.opNorm_le_bound (norm_nonneg _) fun x => (T.codRestrict N h).le_opNorm x

theorem operator_restriction_bound : Spec.RestrictionBound := by
  intro 𝕜 E F _ _ _ _ _ T M N h
  exact (T.restrict h).opNorm_le_bound (norm_nonneg T) fun x => T.le_opNorm x

theorem finite_domain_linear_maps_bounded : Spec.FiniteDomainBoundedness :=
  FiniteDomainOperators.finite_domain_linear_maps_bounded

theorem finite_matrix_coordinates : Spec.MatrixCoordinates :=
  FiniteDomainOperators.finite_matrix_coordinates

theorem operator_norm_for_native : Spec.NativeNormFormula :=
  FiniteDomainOperators.operator_norm_for_native

theorem operator_norm_for_isLeastBound : Spec.NormForIsLeastBound :=
  FiniteDomainOperators.operator_norm_for_isLeastBound

theorem finite_operator_norm_change : Spec.NormChangeComparison :=
  FiniteDomainOperators.finite_operator_norm_change

theorem finite_coordinate_norm_comparison : Spec.CoordinateNormComparison :=
  FiniteDomainOperators.finite_coordinate_norm_comparison

theorem finite_basis_change_comparison : Spec.BasisChangeComparison :=
  FiniteDomainOperators.finite_basis_change_comparison

end ExpandedFA.P1.C03OperatorEstimates
