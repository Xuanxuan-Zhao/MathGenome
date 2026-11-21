import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace ExpandedFA.Unbounded.RealSpectralProductAndSumDomains
open ExpandedFA.SpectralMeasure RealMeasurableSpectralCalculus
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {E : RealProjectionValuedMeasure S H}

namespace Spec
/-- The raw product has the intersection domain, and agrees there with the
maximal product-symbol operator. Equality of partial maps includes values. -/
def ProductLaw (C : RealBoundedRealization E) (f g : S → ℝ)
    (hf : Measurable f) (hg : Measurable g) : Prop :=
  let A := measurableIntegralValue C f hf
  let B := measurableIntegralValue C g hg
  let P := measurableIntegralValue C (fun s => f s * g s) (hf.mul hg)
  (OperatorDomainsSpec.productValue A B).domain = B.domain ⊓ P.domain ∧
  OperatorDomainsSpec.productValue A B ≤ P

/-- Both closures are equal as domain-carrying operators, with genuine
closability assertions rather than reliance on a fallback closure value. -/
def ClosureLaws (C : RealBoundedRealization E) (f g : S → ℝ)
    (hf : Measurable f) (hg : Measurable g) : Prop :=
  let A := measurableIntegralValue C f hf
  let B := measurableIntegralValue C g hg
  let P := OperatorDomainsSpec.productValue A B
  P.IsClosable ∧ P.closure = measurableIntegralValue C (fun s => f s * g s) (hf.mul hg) ∧
  (A + B).IsClosable ∧
  (A + B).closure = measurableIntegralValue C (fun s => f s + g s) (hf.add hg)

/-- A concrete infinite-dimensional real model witnesses strict inclusion even
with the bounded first symbol zero. The symbols may be chosen by the proof. -/
def Strictness : Prop :=
  ∃ (E : RealProjectionValuedMeasure ℕ (lp (fun _ : ℕ => ℝ) 2))
    (C : RealBoundedRealization E) (g : ℕ → ℝ) (hg : Measurable g),
    let Z := measurableIntegralValue C (fun _ => 0) measurable_const
    let B := measurableIntegralValue C g hg
    let P := measurableIntegralValue C (fun n => (0 : ℝ) * g n) (measurable_const.mul hg)
    Dense (B.domain : Set (lp (fun _ : ℕ => ℝ) 2)) ∧
    B.domain ≠ ⊤ ∧ Z.domain = ⊤ ∧
    (OperatorDomainsSpec.productValue Z B).domain = B.domain ∧
    P = (0 : (lp (fun _ : ℕ => ℝ) 2) →L[ℝ] (lp (fun _ : ℕ => ℝ) 2)).toLinearMap.toPMap ⊤ ∧
    (OperatorDomainsSpec.productValue Z B).domain < P.domain

def ProductTheorem : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g), ProductLaw C f g hf hg

def ClosureTheorem : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g), ClosureLaws C f g hf hg

/-- The complete real source theorem, including the already established maximal
construction, density, closedness and self-adjointness. -/
def CompleteTheorem : Prop :=
  RealMeasurableSpectralCalculus.Spec.EveryRealization.{u,v} ∧
  ProductTheorem.{u,v} ∧ ClosureTheorem.{u,v} ∧ Strictness
end Spec
end ExpandedFA.Unbounded.RealSpectralProductAndSumDomains
