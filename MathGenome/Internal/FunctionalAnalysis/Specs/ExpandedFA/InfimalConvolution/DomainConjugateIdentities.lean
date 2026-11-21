import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-! The algebraic part of `fa2:p1:infconv-domain-closure`, paper.tex:7092–7136.
The full extended-real representation of h is retained. Properness means
no value −∞ and a finite value somewhere; convexity is the usual inequality
at finite endpoints (including weights zero). The domain is the set of
finite values. Conjugation always uses the continuous real-linear dual.
The norm-closure conclusion of the source is a separate obligation.
-/
namespace ExpandedFA.InfimalConvolution.DomainConjugateIdentities.Spec

open scoped Pointwise

open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.ExtendedConvexFunctions.Spec
open ExpandedFA.P1.C06Conjugates.Spec
open ExpandedFA.P1.C04CanonicalMap.Spec
open ExpandedFA.InfimalConvolution.Definitions.Spec

/-- Conjugation for a full extended-real function, against the native dual. -/
noncomputable def fullConjugate (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] (H : V → EReal) (L : V →L[ℝ] ℝ) : EReal :=
  ⨆ v, (L v : EReal) - H v

/-- All regularity assumptions on a primal function, without certificates
about the conjugate or the infimal convolution. -/
def Regular (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) : Prop :=
  ProperValue E φ ∧ ExtendedConvexValue E φ ∧ LowerSemicontinuousValue E φ

def AffineLowerBound : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E) (x₀ : E) (r s : ℝ),
    φ x₀ = (r : WithTop ℝ) → ψ x₀ = (s : WithTop ℝ) →
    ∀ f : E →L[ℝ] ℝ,
      ((CanonicalEvaluationValue ℝ E x₀ f - r - s : ℝ) : EReal) ≤
        InfimalConvolutionValue E φ ψ f

def ProperConvolution : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E), Regular E φ → Regular E ψ →
    (finiteDomainValue E φ ∩ finiteDomainValue E ψ).Nonempty →
    (∀ f, InfimalConvolutionValue E φ ψ f ≠ ⊥) ∧
      ∃ (f : E →L[ℝ] ℝ) (t : ℝ), InfimalConvolutionValue E φ ψ f = (t : EReal)

def ConvexConvolution : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E), Regular E φ → Regular E ψ →
    (finiteDomainValue E φ ∩ finiteDomainValue E ψ).Nonempty →
    ∀ (f g : E →L[ℝ] ℝ) (r s a b : ℝ),
    InfimalConvolutionValue E φ ψ f = (r : EReal) →
    InfimalConvolutionValue E φ ψ g = (s : EReal) →
    0 ≤ a → 0 ≤ b → a + b = 1 →
    InfimalConvolutionValue E φ ψ (a • f + b • g) ≤ ((a * r + b * s : ℝ) : EReal)

/-- D(h) = D(φ*) + D(ψ*), with each domain expressed by real values. -/
def DomainIdentity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E), Regular E φ → Regular E ψ →
    (finiteDomainValue E φ ∩ finiteDomainValue E ψ).Nonempty →
    {f | ∃ t : ℝ, InfimalConvolutionValue E φ ψ f = (t : EReal)} =
      {f | ∃ r : ℝ, ConvexConjugateValue E φ f = (r : EReal)} +
      {g | ∃ s : ℝ, ConvexConjugateValue E ψ g = (s : EReal)}

/-- h*(Jx)=φ(x)+ψ(x), including infinite values. This part in fact does not
need reflexivity; J is the actual continuous evaluation map. -/
def ConjugateIdentity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E), Regular E φ → Regular E ψ →
    (finiteDomainValue E φ ∩ finiteDomainValue E ψ).Nonempty →
    ∀ x : E, fullConjugate (E →L[ℝ] ℝ) (InfimalConvolutionValue E φ ψ)
      (CanonicalEvaluationValue ℝ E x) =
        ExtendedRealValueValue (φ x) + ExtendedRealValueValue (ψ x)

/-- The literal biconjugate over the continuous bidual equals (φ+ψ)*.
Surjectivity is the shared reflexivity predicate, so no noncanonical
identification of E and its bidual is used. Reflexivity implies Banach. -/
def BiconjugateIdentity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    IsReflexiveValue ℝ E → ∀ (φ ψ : ExtendedFunction E),
    Regular E φ → Regular E ψ →
    (finiteDomainValue E φ ∩ finiteDomainValue E ψ).Nonempty →
    ∀ f : E →L[ℝ] ℝ,
    (⨆ L : (E →L[ℝ] ℝ) →L[ℝ] ℝ,
      (L f : EReal) - fullConjugate (E →L[ℝ] ℝ) (InfimalConvolutionValue E φ ψ) L) =
        ConvexConjugateValue E (fun x => φ x + ψ x) f

end ExpandedFA.InfimalConvolution.DomainConjugateIdentities.Spec
