import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.Jordan
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.VariationInequalities

/-! Independent Borel-domain statements for paper.tex:5585–5594.
`isSignedRadon_value` uses the canonical Jordan parts, and
`isComplexRadon_value` uses the canonical real and imaginary parts. The norm
is the already shared variation norm; no alternative scalar measure or norm
is introduced. No countability or nonempty-space hypothesis is imposed. -/
namespace Specs.D11.Ch19.ComplexRadonVariation

open Set MeasureTheory
open Specs.D11.Ch18.RadonPredicates
open Specs.D11.Ch14.Jordan
open Specs.D11.Ch14.TotalVariation
open Specs.D11.Ch14.VariationInequalities
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

abbrev signedPredicateType :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X],
    @SignedMeasure X (borel X) → Prop

def isSignedRadon_value : signedPredicateType.{u} := fun ν =>
  isRadonValue (positivePart_value ν) ∧ isRadonValue (negativePart_value ν)

abbrev complexPredicateType :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X],
    @ComplexMeasure X (borel X) → Prop

def isComplexRadon_value : complexPredicateType.{u} := fun ν =>
  isSignedRadon_value ν.re ∧ isSignedRadon_value ν.im

def signedRadon_iff_variation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (ν : @SignedMeasure X (borel X)),
    isSignedRadon_value ν ↔ isRadonValue (totalVariation_value ν)

def complexRadon_iff_variation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (ν : @ComplexMeasure X (borel X)),
    isComplexRadon_value ν ↔ isRadonValue (totalVariation_value ν)

/-- Finite mass makes the shared real-valued norm exactly the extended mass. -/
def signed_norm_mass : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (ν : @SignedMeasure X (borel X)),
    ENNReal.ofReal (variationNorm_value ν) = totalVariation_value ν univ

def complex_norm_mass : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (ν : @ComplexMeasure X (borel X)),
    ENNReal.ofReal (variationNorm_value ν) = totalVariation_value ν univ

def signed_norm_eq_zero_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (ν : @SignedMeasure X (borel X)),
    variationNorm_value ν = 0 ↔ ν = 0

def complex_norm_eq_zero_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (ν : @ComplexMeasure X (borel X)),
    variationNorm_value ν = 0 ↔ ν = 0

end Specs.D11.Ch19.ComplexRadonVariation
