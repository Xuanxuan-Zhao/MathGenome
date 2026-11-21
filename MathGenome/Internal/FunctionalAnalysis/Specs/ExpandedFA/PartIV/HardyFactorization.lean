import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyInnerOuter
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BlaschkeProducts
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Herglotz
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! Full statements of `fa2:p4:hardy-factorization`, paper.tex:18839–18892.
The geometric circle carries normalized Haar measure, consistently with the
angle circle in the Hardy coefficient model. No singularity certificate is
assumed in the zero-free-inner classification. -/
noncomputable section
open MeasureTheory
namespace ExpandedFA.PartIV.HardyFactorization
open HardyDiskSpec

/-- The actual exponential of the negative Herglotz integral. -/
def singularFactor (μ : Measure _root_.Circle) (c z : ℂ) : ℂ :=
  c * Complex.exp (-Herglotz.herglotzTransform μ 0 z)

/-- Positive finite measures, singular to probability circle Haar measure.
Includes the zero measure and hence constant unimodular inner functions. -/
def SingularMeasure (μ : Measure _root_.Circle) : Prop :=
  IsFiniteMeasure μ ∧ μ ⟂ₘ PositiveHarmonic.circleHaar

def ZeroFree (s : H2) : Prop := ∀ z ∈ disk, eval s z ≠ 0

namespace Spec

def Factorization : Prop := HardyInnerOuter.Spec.Factorization
def Uniqueness : Prop := HardyInnerOuter.Spec.Uniqueness
def OuterFormula : Prop := HardyInnerOuter.Spec.OuterFormula

/-- Existence AND joint uniqueness of the singular measure and phase. -/
def ZeroFreeRepresentation : Prop := ∀ s : H2, IsInner s → ZeroFree s →
  ∃! p : Measure _root_.Circle × ℂ,
    SingularMeasure p.1 ∧ ‖p.2‖ = 1 ∧
      Set.EqOn (eval s) (singularFactor p.1 p.2) disk

/-- Every positive singular measure gives a zero-free inner function. -/
def SingularConverse : Prop := ∀ μ : Measure _root_.Circle, SingularMeasure μ →
  ∀ c : ℂ, ‖c‖ = 1 → ∃ s : H2, IsInner s ∧ ZeroFree s ∧
    Set.EqOn (eval s) (singularFactor μ c) disk

/-- The canonical product uses ALL zeros with their analytic multiplicities. -/
def InnerRepresentation : Prop := ∀ i : H2, IsInner i →
  ∃ μ : Measure _root_.Circle, ∃ c : ℂ, SingularMeasure μ ∧ ‖c‖ = 1 ∧
    ∀ z ∈ disk, eval i z = BlaschkeProducts.canonicalProduct i z * singularFactor μ c z

/-- Uniqueness after the canonical normalization of the Blaschke factors. -/
def InnerMeasureUniqueness : Prop := ∀ i : H2, IsInner i →
  ∀ (μ ν : Measure _root_.Circle) (c d : ℂ),
  SingularMeasure μ → SingularMeasure ν → ‖c‖ = 1 → ‖d‖ = 1 →
  (∀ z ∈ disk, eval i z = BlaschkeProducts.canonicalProduct i z * singularFactor μ c z) →
  (∀ z ∈ disk, eval i z = BlaschkeProducts.canonicalProduct i z * singularFactor ν d z) →
  μ = ν ∧ c = d

/-- Exact multiplicities, including the order at zero. Together with the
preceding uniqueness this identifies all canonical factorization data. -/
def ZeroMultiplicity : Prop := BlaschkeProducts.Spec.CanonicalOrders

end Spec
end ExpandedFA.PartIV.HardyFactorization
