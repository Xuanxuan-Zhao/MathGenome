import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealOperatorComplexification
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import Mathlib.MeasureTheory.Measure.Regular

/-! Independent statements for the real self-adjoint specialization of
`fa2:p3:normal-spectral`, with the scalar and exact-domain conventions at
paper.tex:67–73. The current source label occurs at 13978, rather than the
historical line window in the allocation. No positivity or resolvent-point
hypothesis is imposed. All PVMs act on the original real Hilbert space. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ENNReal
namespace ExpandedFA.Unbounded.RealSelfAdjointSpectralTheorem
open SpectralMeasure
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The intrinsic real bounded-inverse spectrum, including the zero-space case. -/
def operatorSpectrum (A : Operator ℝ H H) : Set ℝ :=
  (OperatorDomainsSpec.resolventSetValue A)ᶜ

/-- Representation is exact equality of partial operators. In particular no
field containing a desired graph or support law is assumed. -/
def Resolves (A : Operator ℝ H H) (E : RealProjectionValuedMeasure ℝ H) : Prop :=
  ∃ C : RealBoundedRealization E,
    RealMeasurableSpectralCalculus.measurableIntegralValue C (fun t : ℝ => t)
      measurable_id = A

/-- The complete maximal-domain and norm-limit conclusions for the witness. -/
def RepresentationLaws (A : Operator ℝ H H) {E : RealProjectionValuedMeasure ℝ H}
    (C : RealBoundedRealization E) : Prop :=
  RealMeasurableSpectralCalculus.measurableIntegralValue C (fun t : ℝ => t)
      measurable_id = A ∧
  (∀ x : H, x ∈ A.domain ↔
    (∫⁻ t : ℝ, ENNReal.ofReal (t ^ 2) ∂(C.scalar x)) < ∞) ∧
  (∀ x : A.domain,
    Tendsto (fun n : ℕ => C.integral
      (RealMeasurableSpectralCalculus.truncation (fun t : ℝ => t) measurable_id n) x)
      atTop (𝓝 (A x)))

def SameBorelValues (E F : RealProjectionValuedMeasure ℝ H) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → E B = F B

def SpectralSupport (A : Operator ℝ H H) (E : RealProjectionValuedMeasure ℝ H) : Prop :=
  _root_.IsClosed (operatorSpectrum A) ∧ E (operatorSpectrum A)ᶜ = 0 ∧
    ∀ U : Set ℝ, IsOpen U → (U ∩ operatorSpectrum A).Nonempty → E U ≠ 0

/-- Regularity of a signed measure is expressed by regularity of its actual
variation; scalar positive measures are regular separately. -/
def Regularity {E : RealProjectionValuedMeasure ℝ H} (C : RealBoundedRealization E) : Prop :=
  (∀ x : H, Measure.Regular (C.scalar x)) ∧
  (∀ x y : H, Measure.Regular (C.coefficient x y).variation)

namespace Spec

def Closedness : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Operator ℝ H H), Dense (A.domain : Set H) →
    HilbertAdjointSpec.adjointValue A = A → A.IsClosed

def SpectrumBridge : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Operator ℝ H H),
    letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
    operatorSpectrum A = Complex.ofReal ⁻¹'
      (UnboundedNormalSpectralTheorem.operatorSpectrum
        (RealOperatorComplexification.Spec.complexifyValue A))

def SpectrumClosed : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Operator ℝ H H), _root_.IsClosed (operatorSpectrum A)

/-- An actual intermediate complex representation, not the real conclusion. -/
def ComplexificationRepresentation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Operator ℝ H H), Dense (A.domain : Set H) →
    HilbertAdjointSpec.adjointValue A = A →
    letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
    ∃ E : ProjectionValuedMeasure ℝ (TraceIdeals.RealComplexification.Space H),
      UnboundedNormalSpectralTheorem.RealResolves
        (RealOperatorComplexification.Spec.complexifyValue A) E

def RegularityForEveryRealization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E), Regularity C

def RepresentationConsequences : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Operator ℝ H H) (E : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E),
    RealMeasurableSpectralCalculus.measurableIntegralValue C (fun t : ℝ => t)
      measurable_id = A → RepresentationLaws A C

def SpectralExistence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Operator ℝ H H), Dense (A.domain : Set H) →
    HilbertAdjointSpec.adjointValue A = A →
    ∃ (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E),
      RepresentationLaws A C

/-- All representations, with independently chosen bounded realizations,
are compared. There is no preferred-witness restriction. -/
def SpectralUniquenessAndSupport : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Operator ℝ H H), Dense (A.domain : Set H) →
    HilbertAdjointSpec.adjointValue A = A →
    ∀ E : RealProjectionValuedMeasure ℝ H, Resolves A E →
      SpectralSupport A E ∧
      ∀ F : RealProjectionValuedMeasure ℝ H, Resolves A F → SameBorelValues E F

def RealTheorem : Prop :=
  Closedness.{u} ∧ SpectralExistence.{u} ∧ SpectralUniquenessAndSupport.{u} ∧
    RegularityForEveryRealization.{u}

/-- The existing complex specialization is retained verbatim. -/
def FullScalarSelfAdjointTheorem : Prop :=
  UnboundedNormalSpectralTheorem.Spec.SelfAdjointSpectralTheorem.{u} ∧ RealTheorem.{u}

end Spec
end ExpandedFA.Unbounded.RealSelfAdjointSpectralTheorem
