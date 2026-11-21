import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.CoordinateMultiplicationModel

/-! The absolute-continuity/full-support warning in `fa2:p3:translation-model`.
The graph comparison includes the complete maximal domains on both sides.
No separability assumption is imposed on the comparison multiplicity. -/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.Models.TranslationMultiplicityWarning.Spec
open ExpandedFA.Models.FullTranslationModel
universe u

/-- A sufficient measurable support for the warning. -/
def WarningSet (E : Set ℝ) : Prop :=
  MeasurableSet E ∧
  (∀ a b : ℝ, a < b → 0 < volume (E ∩ Ioo a b)) ∧
  0 < volume Eᶜ

/-- Existence of the support set is a helper, not the full warning. -/
def WarningSetExists : Prop := ∃ E : Set ℝ, WarningSet E

/-- An exact unitary equivalence of both maximal coordinate graphs. -/
def CoordinateGraphEquivalence (E : Set ℝ)
    (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    (W : RestrictedL2 E ≃ₗᵢ[ℂ] L2 M) : Prop :=
  ∀ f g : RestrictedL2 E,
    RestrictedCoordinateGraph E f g ↔ CoordinateGraph (W f) (W g)

/-- The substantive counterexample, with its actual self-adjoint spectral
realization and universal inequivalence even for nonseparable multiplicity. -/
def NonconstantMultiplicityWarning : Prop :=
  ∃ E : Set ℝ, WarningSet E ∧ RestrictedSpectralModel E ∧
    ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
      [CompleteSpace M] [Nontrivial M],
      ¬ ∃ W : RestrictedL2 E ≃ₗᵢ[ℂ] L2 M, CoordinateGraphEquivalence E M W

end ExpandedFA.Models.TranslationMultiplicityWarning.Spec
