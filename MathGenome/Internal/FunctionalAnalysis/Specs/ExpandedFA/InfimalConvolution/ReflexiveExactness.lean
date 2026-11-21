import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.DomainConjugateIdentities
import Mathlib.Analysis.Normed.Group.Bounded

/-! Exactness and attainment in `fa2:p1:infconv-full-cone`, paper.tex:7160–7237.
All function values and infima retain the shared full extended-real conventions.
Reflexivity is surjectivity of the canonical evaluation map. -/
namespace ExpandedFA.InfimalConvolution.ReflexiveExactness.Spec

open scoped Pointwise
open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates.Spec
open ExpandedFA.P1.C04CanonicalMap.Spec
open ExpandedFA.InfimalConvolution.Definitions.Spec
open ExpandedFA.InfimalConvolution.DomainConjugateIdentities.Spec

def NormLowerSemicontinuity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    IsReflexiveValue ℝ E → ∀ φ ψ : ExtendedFunction E,
    Regular E φ → Regular E ψ →
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    DomainDifferenceConeValue E φ ψ = Set.univ →
    ∀ α : ℝ, IsClosed {f | InfimalConvolutionValue E φ ψ f ≤ (α : EReal)}

def ExactConjugateFormula : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    IsReflexiveValue ℝ E → ∀ φ ψ : ExtendedFunction E,
    Regular E φ → Regular E ψ →
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    DomainDifferenceConeValue E φ ψ = Set.univ →
    ∀ f, InfimalConvolutionValue E φ ψ f =
      ConvexConjugateValue E (fun x => φ x + ψ x) f

def FiniteAttainment : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    IsReflexiveValue ℝ E → ∀ φ ψ : ExtendedFunction E,
    Regular E φ → Regular E ψ →
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    DomainDifferenceConeValue E φ ψ = Set.univ →
    ∀ (f : E →L[ℝ] ℝ) (r : ℝ),
    ConvexConjugateValue E (fun x => φ x + ψ x) f = (r : EReal) →
    ∃ g, ConjugateSplitCostValue E φ ψ f g = (r : EReal)

def ExactDomainSum : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    IsReflexiveValue ℝ E → ∀ φ ψ : ExtendedFunction E,
    Regular E φ → Regular E ψ →
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    DomainDifferenceConeValue E φ ψ = Set.univ →
    {f | ∃ r : ℝ, ConvexConjugateValue E (fun x => φ x + ψ x) f = (r : EReal)} =
      {f | ∃ r : ℝ, ConvexConjugateValue E φ f = (r : EReal)} +
      {g | ∃ s : ℝ, ConvexConjugateValue E ψ g = (s : EReal)}

end ExpandedFA.InfimalConvolution.ReflexiveExactness.Spec
