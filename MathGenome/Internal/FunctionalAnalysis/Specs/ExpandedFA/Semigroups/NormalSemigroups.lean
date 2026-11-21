import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem

/-! Semigroups of normal operators, paper.tex `fa2:p3:normal-semigroup`.
The generator is the canonical right norm derivative, on its full domain.
Normality includes equality of both partial product domains. No spectral
representation of the generator is assumed in either direction. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped NNReal

namespace ExpandedFA.Semigroups.NormalSemigroups
open Unbounded Unbounded.MeasurableSpectralCalculus
open Unbounded.UnboundedNormalSpectralTheorem
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsNormalSemigroup (T : C0Semigroup ℂ H) : Prop :=
  ∀ t, IsStarNormal (T.operators t)

def HasSpectralUpperBound (A : Operator ℂ H H) : Prop :=
  ∃ ω : ℝ, ∀ z ∈ operatorSpectrum A, z.re ≤ ω

/-- Equality of partial linear maps fixes the entire domain of exp(tA),
including at t=0. The exponential symbol is the actual function on ℂ;
no global boundedness of this symbol away from spectral support is assumed. -/
def ExponentialRepresentation (A : Operator ℂ H H) (T : C0Semigroup ℂ H) : Prop :=
  ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℂ H) (C : BoundedRealization E),
    measurableIntegral C id = A ∧
    ∀ t : ℝ≥0, measurableIntegral C (fun z => Complex.exp ((t : ℂ) * z)) =
      (T.operators t).toLinearMap.toPMap ⊤

namespace Spec

def Forward : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : C0Semigroup ℂ H), IsNormalSemigroup T →
    let A := C0SemigroupSpec.generatorValue T
    Dense (A.domain : Set H) ∧ A.IsClosed ∧
    OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue A) A =
      OperatorDomainsSpec.productValue A (HilbertAdjointSpec.adjointValue A) ∧
    HasSpectralUpperBound A ∧ ExponentialRepresentation A T

/-- Normality of the full canonical generator, including both product domains. -/
def GeneratorNormality : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : C0Semigroup ℂ H), IsNormalSemigroup T →
    let A := C0SemigroupSpec.generatorValue T
    OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue A) A =
      OperatorDomainsSpec.productValue A (HilbertAdjointSpec.adjointValue A)

def Converse : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator ℂ H H), Dense (A.domain : Set H) → A.IsClosed →
    OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue A) A =
      OperatorDomainsSpec.productValue A (HilbertAdjointSpec.adjointValue A) →
    HasSpectralUpperBound A →
    ∃ T : C0Semigroup ℂ H, IsNormalSemigroup T ∧
      C0SemigroupSpec.generatorValue T = A ∧ ExponentialRepresentation A T

def AdjointCommutation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : C0Semigroup ℂ H), IsNormalSemigroup T →
    ∀ s t, (T.operators s).adjoint.comp (T.operators t) =
      (T.operators t).comp (T.operators s).adjoint

def NormalDifferenceQuotients : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : C0Semigroup ℂ H), IsNormalSemigroup T →
    ∀ h : ℝ, IsStarNormal (C0SemigroupSpec.differenceQuotientValue T h)

/-- Adjoint strong continuity is proved from normality, not assumed. -/
def AdjointSemigroup : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : C0Semigroup ℂ H), IsNormalSemigroup T →
    ∃ S : C0Semigroup ℂ H, ∀ t, S.operators t = (T.operators t).adjoint

/-- A construction lemma for an arbitrary measurable spectral base and a
finite measurable symbol with a pointwise real upper bound. It does not
assume any derivative-domain identification. -/
def SpectralSemigroup : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : SpectralMeasure.ProjectionValuedMeasure S H) (C : BoundedRealization E)
    (f : S → ℂ), Measurable f → (∃ ω : ℝ, ∀ s, (f s).re ≤ ω) →
    ∃ T : C0Semigroup ℂ H, IsNormalSemigroup T ∧
      ∀ t : ℝ≥0, T.operators t = C.integral (fun s => Complex.exp ((t : ℂ) * f s))

def SpectralGenerator : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : SpectralMeasure.ProjectionValuedMeasure S H) (C : BoundedRealization E)
    (f : S → ℂ), Measurable f → (∃ ω : ℝ, ∀ s, (f s).re ≤ ω) →
    ∀ T : C0Semigroup ℂ H,
      (∀ t : ℝ≥0, T.operators t = C.integral (fun s => Complex.exp ((t : ℂ) * f s))) →
      C0SemigroupSpec.generatorValue T = measurableIntegral C f

end Spec
end ExpandedFA.Semigroups.NormalSemigroups
