import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.TranslationFourierModel

/-! Replacement ownership for the source's representation predicates.
This file is a new, explicit coordinated handoff; it does not claim to recover
the unavailable historical parent draft. Every model is an existence predicate
for an actual unitary, and operator models compare the entire graphs.
-/
noncomputable section
open MeasureTheory

namespace ExpandedFA.Models.FullTranslationModel
open ExpandedFA.Unbounded ExpandedFA.Semigroups.Stone
open ExpandedFA.Unbounded.SymmetryAndDeficienciesSpec
universe u v

section Representations
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

def OperatorTranslationModel (A : Operator ℂ H H) : Prop :=
  ∃ W : H ≃ₗᵢ[ℂ] L2 M, ∀ f g : H,
    (f, g) ∈ A.graph ↔ SpatialGraph (W f) (W g)

def OperatorLebesgueModel (A : Operator ℂ H H) : Prop :=
  ∃ W : H ≃ₗᵢ[ℂ] L2 M, ∀ f g : H,
    (f, g) ∈ A.graph ↔ CoordinateGraph (W f) (W g)

def GroupTranslationModel (U : UnitaryGroup H) : Prop :=
  ∃ W : H ≃ₗᵢ[ℂ] L2 M, ∀ t f,
    W (U.operators t f) = translate t (W f)

def GroupLebesgueModel (U : UnitaryGroup H) : Prop :=
  ∃ W : H ≃ₗᵢ[ℂ] L2 M, ∀ t f,
    (W (U.operators t f) : ℝ → M) =ᵐ[volume]
      fun r => Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) • W f r

end Representations

namespace Spec

/-- Both concrete generators, on their full graph domains, for every complex
Hilbert multiplicity. No separability or nonzero-space premise is imposed. -/
def CanonicalModels : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M],
    ∃ (V W : UnitaryGroup (L2 M)) (A B : Operator ℂ (L2 M) (L2 M))
      (F : L2 M ≃ₗᵢ[ℂ] L2 M),
      IsTranslationGroup V ∧ IsCoordinateGroup W ∧
      selfAdjointValue A ∧ SpectralExponential A V ∧ DerivativeGraph V A ∧
      (∀ f g, (f, g) ∈ A.graph ↔ SpatialGraph f g) ∧
      selfAdjointValue B ∧ SpectralExponential B W ∧ DerivativeGraph W B ∧
      (∀ f g, (f, g) ∈ B.graph ↔ CoordinateGraph f g) ∧
      AngularFourierAgreement F ∧ FourierConjugacy V W F ∧
      (∀ f g, (f, g) ∈ A.graph ↔ (F f, F g) ∈ B.graph)

def OperatorCriterion : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    (A : Operator ℂ H H), selfAdjointValue A →
      (OperatorTranslationModel M A ↔ OperatorLebesgueModel M A)

def GroupCriterion : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    (U : UnitaryGroup H), GroupTranslationModel M U ↔ GroupLebesgueModel M U

def FullConclusion : Prop :=
  CanonicalModels.{u} ∧ OperatorCriterion.{u, v} ∧ GroupCriterion.{u, v}

end Spec
end ExpandedFA.Models.FullTranslationModel
