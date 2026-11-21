import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.ComplexRealification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.ScaledLimit
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.EmptyMinimizerDivergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.EnvelopeGradient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Conventions

/-!
The complex-space convention of paper.tex:8696–8707.
Restriction of scalars keeps H, its norm, topology and completeness unchanged.
Thus each real theorem applies directly. Explicit pairing and Riesz bridges
below identify the transported definitions with Re⟪w,v⟫ and continuous REAL
functionals. Proximal maps and gradients remain ordinary, possibly nonlinear,
functions; no complex-linear structure is asserted.
-/
noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.Proximal
universe u

theorem complex_geometry : ComplexSpec.Geometry.{u} := by
  intro H _ _
  exact Hilbert.Conventions.realification_geometry ℂ H

theorem complex_objective_and_envelope : ComplexSpec.ObjectiveAndEnvelope.{u} := by
  intro H _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  intro φ μ f v
  exact ⟨rfl, moreauEnvelope_formula H φ μ f⟩

theorem complex_conjugate_formula : ComplexSpec.ConjugateFormula.{u} := by
  intro H _ _ φ x
  rfl

theorem complex_subgradient_formula : ComplexSpec.SubgradientFormula.{u} := by
  intro H _ _ φ x
  rfl

theorem complex_real_riesz_representation : ComplexSpec.RealRieszRepresentation.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  intro F
  obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℝ H).surjective F
  refine ⟨w, ?_, ?_⟩
  · intro v
    exact (congrArg (fun G : H →L[ℝ] ℝ => G v) hw).symm
  · intro z hz
    apply (InnerProductSpace.toDual ℝ H).injective
    apply ContinuousLinearMap.ext
    intro v
    exact (hz v).symm.trans ((congrArg (fun G : H →L[ℝ] ℝ => G v) hw).symm)

theorem complex_subgradient_riesz_image : ComplexSpec.SubgradientRieszImage.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact hilbertSubdifferential_riesz_image H

theorem complex_conjugate_riesz_identification : ComplexSpec.ConjugateRieszIdentification.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact hilbertConjugate_eq_banachConjugate H

theorem complex_exists_unique_proximalMinimizer : ComplexSpec.UniqueMinimizer.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact exists_unique_proximalMinimizer H

theorem complex_moreauEnvelope_finite : ComplexSpec.FiniteEnvelope.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact moreauEnvelope_finite H

theorem complex_proximalMap_minimizes : ComplexSpec.ProximalMapMinimizes.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_minimizes H

theorem complex_minimizer_iff_variational : ComplexSpec.MinimizerIffVariational.{u} := by
  intro H _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact minimizer_iff_variational H

theorem complex_variational_iff_subgradient : ComplexSpec.VariationalIffSubgradient.{u} := by
  intro H _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact variational_iff_subgradient H

theorem complex_proximalMap_characterization : ComplexSpec.ProximalCharacterization.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_characterization H

theorem complex_proximalMap_firm : ComplexSpec.FirmBound.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_firm H

theorem complex_proximalMap_nonexpansive : ComplexSpec.Nonexpansive.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_nonexpansive H

theorem complex_proximalMap_indicator : ComplexSpec.IndicatorProjection.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_indicator H

theorem complex_conjugateFunction_identification : ComplexSpec.ConjugateIdentification.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact conjugateFunction_identification H

theorem complex_conjugateFunction_regular : ComplexSpec.ConjugateRegularity.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact conjugateFunction_regular H

theorem complex_moreau_decomposition : ComplexSpec.Decomposition.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact moreau_decomposition H

theorem complex_moreau_unit_parameter : ComplexSpec.UnitParameter.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact moreau_unit_parameter H

theorem complex_moreauEnvelope_regularity : ComplexSpec.Regularity.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact moreauEnvelope_regularity H

theorem complex_moreauGradient_dual_identification : ComplexSpec.DualIdentification.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact moreauGradient_dual_identification H

theorem complex_proximalMap_smallParameter : ComplexSpec.SmallParameterLimit.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_smallParameter H

theorem complex_minimizer_set_geometry : ComplexSpec.MinimizerSetGeometry.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact minimizer_set_geometry H

theorem complex_proximalMap_largeParameter_limit : ComplexSpec.LargeParameterLimit.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_largeParameter_limit H

theorem complex_proximalMap_norm_tendsto_atTop_of_argmin_empty : ComplexSpec.EmptyMinimizerDivergence.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_norm_tendsto_atTop_of_argmin_empty H

theorem complex_proximalMap_scaledLimit : ComplexSpec.ScaledLimit.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  exact proximalMap_scaledLimit H

theorem complex_gradient_pairing : ComplexSpec.GradientPairing.{u} := by
  intro H _ _ _
  let := Hilbert.Conventions.Spec.RealificationValue ℂ H
  intro φ hp hc hl μ hμ f v
  have hd := (moreauEnvelope_regularity H φ hp hc hl μ hμ).2.2.2.1 f
  exact congrArg (fun F : H →L[ℝ] ℝ => F v) hd

end ExpandedFA.Proximal
