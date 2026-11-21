import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Exact product domains and closures in paper.tex, `fa2:p3:unbounded-calculus`.
All functions are everywhere finite (complex-valued); the measurable base and
complex Hilbert space are arbitrary. No control measure is assumed. -/
noncomputable section
open Set
namespace ExpandedFA.Unbounded.SpectralProductAndSumDomains.Spec
open MeasurableSpectralCalculus
universe u v

def ProductRule : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)
    (f g : S → ℂ), Measurable f → Measurable g →
    (OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C g)).domain =
      (measurableIntegral C g).domain ⊓ (measurableIntegral C (f * g)).domain ∧
    OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C g) ≤
      measurableIntegral C (f * g)

def ProductClosure : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)
    (f g : S → ℂ), Measurable f → Measurable g →
    (OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C g)).IsClosable ∧
    (OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C g)).closure =
      measurableIntegral C (f * g)

def SumClosure : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)
    (f g : S → ℂ), Measurable f → Measurable g →
    (measurableIntegral C f + measurableIntegral C g).IsClosable ∧
    (measurableIntegral C f + measurableIntegral C g).closure = measurableIntegral C (f + g)

/-- The zero first factor is bounded; a genuine diagonal PVM on ℓ² realizes
an unbounded second factor with a strictly smaller product domain. -/
def StrictDomainExample : Prop :=
  ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℕ (lp (fun _ : ℕ => ℂ) 2))
    (C : BoundedRealization E),
    let g : ℕ → ℂ := fun n => (2 : ℂ) ^ n
    Measurable g ∧ (∀ M : ℝ, ∃ n, M < ‖g n‖) ∧
    (measurableIntegral C g).domain ≠ ⊤ ∧
    (OperatorDomainsSpec.productValue (measurableIntegral C (0 : ℕ → ℂ))
      (measurableIntegral C g)).domain = (measurableIntegral C g).domain ∧
    (measurableIntegral C ((0 : ℕ → ℂ) * g)).domain = ⊤ ∧
    (OperatorDomainsSpec.productValue (measurableIntegral C (0 : ℕ → ℂ))
      (measurableIntegral C g)).domain < (measurableIntegral C ((0 : ℕ → ℂ) * g)).domain

end ExpandedFA.Unbounded.SpectralProductAndSumDomains.Spec
