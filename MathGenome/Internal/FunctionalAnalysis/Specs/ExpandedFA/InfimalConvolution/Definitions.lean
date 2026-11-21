import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates

/-!
Independent specification of the definitions in paper.tex:7092–7107,
7163–7166 and 7257–7265. The primal functions use the shared half-extended
real representation. Conjugates and their infimal convolution use `EReal`.

The formulas make sense for arbitrary primal functions, so the definitions
do not require properness, convexity, lower semicontinuity, completeness or
reflexivity. In particular they apply to all the proper convex functions
with a common finite domain point in the assigned statement. No assertion
that the conjugates have finite values is built into these definitions.
-/
namespace ExpandedFA.InfimalConvolution.Definitions.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

/-- D(φ) is the already established finite domain of a half-extended function. -/
def FiniteDomainType := ∀ (E : Type*), ExtendedFunction E → Set E

def FiniteDomainValue : FiniteDomainType :=
  ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue

def ConjugateSplitCostType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ExtendedFunction E → ExtendedFunction E → (E →L[ℝ] ℝ) → (E →L[ℝ] ℝ) → EReal

/-- The two continuous-dual conjugates, with split variables f−g and g. -/
noncomputable def ConjugateSplitCostValue : ConjugateSplitCostType :=
  fun E _ _ φ ψ f g =>
    ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue E φ (f - g) +
      ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue E ψ g

def InfimalConvolutionType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ExtendedFunction E → ExtendedFunction E → (E →L[ℝ] ℝ) → EReal

/-- The infimum is in the full extended real line, without a minimum assertion. -/
noncomputable def InfimalConvolutionValue : InfimalConvolutionType :=
  fun E _ _ φ ψ f => ⨅ g : E →L[ℝ] ℝ, ConjugateSplitCostValue E φ ψ f g

def DomainDifferenceConeType :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E],
    ExtendedFunction E → ExtendedFunction E → Set E

/-- The literal union ⋃ λ≥0, λ(Dφ−Dψ), retaining the scale λ=0.
There is no linear span, closure, or assumption that this union is all of E. -/
def DomainDifferenceConeValue : DomainDifferenceConeType :=
  fun E _ _ φ ψ => ⋃ (a : ℝ) (_ : 0 ≤ a),
    (fun p : E × E => a • (p.1 - p.2)) ''
      (FiniteDomainValue E φ ×ˢ FiniteDomainValue E ψ)

/-- Because −∞ is excluded from primal values, non-top means a real value. -/
def MemFiniteDomain : Prop :=
  ∀ (E : Type*) (φ : ExtendedFunction E) (x : E),
    x ∈ FiniteDomainValue E φ ↔ ∃ r : ℝ, φ x = (r : WithTop ℝ)

/-- The displayed infimum has its full order-theoretic meaning. -/
def InfimalConvolutionIsGLB : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E) (f : E →L[ℝ] ℝ),
    IsGLB (Set.range fun g : E →L[ℝ] ℝ => ConjugateSplitCostValue E φ ψ f g)
      (InfimalConvolutionValue E φ ψ f)

def MemDomainDifferenceCone : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E]
    (φ ψ : ExtendedFunction E) (z : E),
    z ∈ DomainDifferenceConeValue E φ ψ ↔
      ∃ (a : ℝ), 0 ≤ a ∧ ∃ (x y : E),
        x ∈ FiniteDomainValue E φ ∧ y ∈ FiniteDomainValue E ψ ∧ z = a • (x - y)

/-- A common finite-domain point supplies zero even at scale zero. -/
def ZeroMemDomainDifferenceCone : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] (φ ψ : ExtendedFunction E),
    (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty →
      (0 : E) ∈ DomainDifferenceConeValue E φ ψ

end ExpandedFA.InfimalConvolution.Definitions.Spec
