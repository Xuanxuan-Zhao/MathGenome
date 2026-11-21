import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.ReflexiveExactness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.UniformSplitBounds

/-! Complete statement of paper.tex:7160–7237, `fa2:p1:infconv-full-cone`.
The primal values lie in `WithTop ℝ`; all infima, suprema and dual values
lie in `EReal`. Reflexivity is surjectivity of canonical evaluation.
No primal minimizer or common continuity point is assumed. -/
namespace ExpandedFA.InfimalConvolution.ReflexiveFullConeDuality.Spec

universe u

open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates.Spec
open ExpandedFA.P1.C04CanonicalMap.Spec
open ExpandedFA.InfimalConvolution.Definitions.Spec
open ExpandedFA.InfimalConvolution.DomainConjugateIdentities.Spec

/-- Uniformly for bounded B, including the empty set. The upstream statement
actually needs only Banach completeness and the full cone. -/
def UniformSplitBounds : Prop := UniformSplitBounds.Spec.BoundedSplitSublevels.{u}

def NormLowerSemicontinuity : Prop := ReflexiveExactness.Spec.NormLowerSemicontinuity.{u}

def ExactConjugateFormula : Prop := ReflexiveExactness.Spec.ExactConjugateFormula.{u}

def FiniteAttainment : Prop := ReflexiveExactness.Spec.FiniteAttainment.{u}

def ExactDomainSum : Prop := ReflexiveExactness.Spec.ExactDomainSum.{u}

/-- Equality in the full extended line, including unbounded-below primal problems. -/
def PrimalDualIdentity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    IsReflexiveValue ℝ E → ∀ φ ψ : ExtendedFunction E,
    Regular E φ → Regular E ψ →
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    DomainDifferenceConeValue E φ ψ = Set.univ →
    (⨅ x, ExtendedRealValueValue (φ x + ψ x)) =
      ⨆ g : E →L[ℝ] ℝ, -ConvexConjugateValue E φ (-g) - ConvexConjugateValue E ψ g

/-- A finite primal infimum yields an actual maximizing continuous functional. -/
def DualAttainment : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    IsReflexiveValue ℝ E → ∀ φ ψ : ExtendedFunction E,
    Regular E φ → Regular E ψ →
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    DomainDifferenceConeValue E φ ψ = Set.univ →
    ∀ r : ℝ, (⨅ x, ExtendedRealValueValue (φ x + ψ x)) = (r : EReal) →
    ∃ g : E →L[ℝ] ℝ,
      -ConvexConjugateValue E φ (-g) - ConvexConjugateValue E ψ g = (r : EReal) ∧
      ∀ u : E →L[ℝ] ℝ,
        -ConvexConjugateValue E φ (-u) - ConvexConjugateValue E ψ u ≤
        -ConvexConjugateValue E φ (-g) - ConvexConjugateValue E ψ g

/-- The common finite point excludes the other infinite primal value. -/
def PrimalNotTop : Prop :=
  ∀ (E : Type*) (φ ψ : ExtendedFunction E),
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    (⨅ x, ExtendedRealValueValue (φ x + ψ x)) ≠ ⊤

/-- Explicit interpretation of the unbounded-below case. -/
def UnboundedBelowDuality : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    IsReflexiveValue ℝ E → ∀ φ ψ : ExtendedFunction E,
    Regular E φ → Regular E ψ →
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
    DomainDifferenceConeValue E φ ψ = Set.univ →
    (⨅ x, ExtendedRealValueValue (φ x + ψ x)) = ⊥ →
    (⨆ g : E →L[ℝ] ℝ, -ConvexConjugateValue E φ (-g) - ConvexConjugateValue E ψ g) = ⊥

end ExpandedFA.InfimalConvolution.ReflexiveFullConeDuality.Spec
