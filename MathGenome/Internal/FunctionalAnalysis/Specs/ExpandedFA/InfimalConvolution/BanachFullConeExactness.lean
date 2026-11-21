import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.UniformSplitBounds
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar

/-! Independent specification of the full-space stage of
`fa2:p1:infconv-banach-closed-cone`, paper.tex:7251–7310.
The carrier of the dual retains its original operator norm. Its weak-star
closed sets use the canonical evaluation topology. No reflexivity, separability,
common continuity point, or primal minimizer is assumed. -/
namespace ExpandedFA.InfimalConvolution.BanachFullConeExactness.Spec

open ExpandedFA.P1
open ExtendedConvexFunctions
open Definitions.Spec

/-- Exactly the hypotheses of the full-cone Banach theorem. -/
def Hypotheses (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E) : Prop :=
  ExtendedConvexFunctions.Spec.ProperValue E φ ∧
  ExtendedConvexFunctions.Spec.ProperValue E ψ ∧
  ExtendedConvexFunctions.Spec.ExtendedConvexValue E φ ∧
  ExtendedConvexFunctions.Spec.ExtendedConvexValue E ψ ∧
  ExtendedConvexFunctions.Spec.LowerSemicontinuousValue E φ ∧
  ExtendedConvexFunctions.Spec.LowerSemicontinuousValue E ψ ∧
  (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty ∧
  DomainDifferenceConeValue E φ ψ = Set.univ

/-- The full extended-real infimal convolution is weak-star lsc. -/
def WeakStarLowerSemicontinuity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E), Hypotheses E φ ψ →
    ∀ r : ℝ, @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue ℝ E)
      {f : E →L[ℝ] ℝ | InfimalConvolutionValue E φ ψ f ≤ (r : EReal)}

/-- Attainment is asserted at every finite value of h. -/
def FiniteValueAttainment : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E), Hypotheses E φ ψ →
    ∀ (f : E →L[ℝ] ℝ) (r : ℝ), InfimalConvolutionValue E φ ψ f = (r : EReal) →
      ∃ g : E →L[ℝ] ℝ, ConjugateSplitCostValue E φ ψ f g = (r : EReal)

/-- Equality includes +∞, where no minimum is asserted. -/
def ExactConjugateFormula : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E), Hypotheses E φ ψ →
    ∀ f : E →L[ℝ] ℝ, InfimalConvolutionValue E φ ψ f =
      C06Conjugates.Spec.ConvexConjugateValue E (fun x => φ x + ψ x) f

/-- Literal Minkowski sum of finite conjugate domains, without closures. -/
def ExactDomainSum : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E), Hypotheses E φ ψ →
    ∀ f : E →L[ℝ] ℝ,
      C06Conjugates.Spec.ConvexConjugateValue E (fun x => φ x + ψ x) f < ⊤ ↔
      ∃ a b : E →L[ℝ] ℝ, f = a + b ∧
        C06Conjugates.Spec.ConvexConjugateValue E φ a < ⊤ ∧
        C06Conjugates.Spec.ConvexConjugateValue E ψ b < ⊤

/-- The primal infimum may be −∞. The common point excludes +∞;
finite dual attainment does not assert primal attainment. -/
def PrimalDualIdentity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E), Hypotheses E φ ψ →
    let p := ⨅ x : E, C06Conjugates.Spec.ExtendedRealValueValue (φ x + ψ x)
    p ≠ ⊤ ∧
    p = ⨆ g : E →L[ℝ] ℝ,
      -C06Conjugates.Spec.ConvexConjugateValue E φ (-g) -
        C06Conjugates.Spec.ConvexConjugateValue E ψ g ∧
    (∀ r : ℝ, p = (r : EReal) → ∃ g : E →L[ℝ] ℝ,
      -C06Conjugates.Spec.ConvexConjugateValue E φ (-g) -
        C06Conjugates.Spec.ConvexConjugateValue E ψ g = (r : EReal))

/-- h is proper: never −∞ and finite somewhere. -/
def ProperInfimalConvolution : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E), Hypotheses E φ ψ →
    (∀ f : E →L[ℝ] ℝ, InfimalConvolutionValue E φ ψ f ≠ ⊥) ∧
    ∃ (f : E →L[ℝ] ℝ) (r : ℝ), InfimalConvolutionValue E φ ψ f = (r : EReal)

/-- Convexity of the real epigraph, preserving the full EReal value function. -/
def ConvexInfimalEpigraph : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E), Hypotheses E φ ψ →
    Convex ℝ {p : (E →L[ℝ] ℝ) × ℝ |
      InfimalConvolutionValue E φ ψ p.1 ≤ (p.2 : EReal)}

end ExpandedFA.InfimalConvolution.BanachFullConeExactness.Spec
