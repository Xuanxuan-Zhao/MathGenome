import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! K03.13.termwise, integration portion, paper.tex:1387–1404.
The primitive coefficients include their zero constant coefficient. Radii are
coefficient-root radii in ℝ≥0∞, with no positive-radius restriction.
Integrals are the existing proper Darboux integrals on the ordered hull;
the sign in the conclusion is precisely the oriented integral from c to x.
Representatives of ordinary sums may be arbitrary outside the open interval.
The center series is asserted separately, even when the radius is zero.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch13.Integration
open PowerSeries
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open Specs.SingleVariableAnalysis.Ch08.Integral
open scoped ENNReal

def realPrimitiveCoefficientsType : Type := (ℕ → ℝ) → ℕ → ℝ
def realPrimitiveCoefficientsValue : realPrimitiveCoefficientsType :=
  fun a n => match n with
  | 0 => 0
  | n+1 => a n / (n+1 : ℝ)

def realPrimitiveRadius : Prop := ∀ a : ℕ → ℝ,
  realPowerSeriesRadiusValue (realPrimitiveCoefficientsValue a) = realPowerSeriesRadiusValue a

def realPrimitiveCenter : Prop := ∀ (a : ℕ → ℝ) (c : ℝ),
  realSeriesHasSumValue (fun n => a n / (n+1 : ℝ) * (c-c)^(n+1)) 0

def realPrimitiveDerivative : Prop := ∀ (a : ℕ → ℝ) (c : ℝ) (f g : ℝ → ℝ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    RealPowerSeriesHasSumValue a c x (f x)) →
  (∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    RealPowerSeriesHasSumValue (realPrimitiveCoefficientsValue a) c x (g x)) →
  ∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    HasDerivAt g (f x) x

def realTermwiseIntegration : Prop := ∀ (a : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    RealPowerSeriesHasSumValue a c x (f x)) →
  ∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
  ∃ hf : realIntegrableValue f (min c x) (max c x),
    realSeriesHasSumValue (fun n => a n / (n+1 : ℝ) * (x-c)^(n+1))
      (if c ≤ x then realIntegralValue f hf else -realIntegralValue f hf)

def complexPrimitiveCoefficientsType : Type := (ℕ → ℂ) → ℕ → ℂ
def complexPrimitiveCoefficientsValue : complexPrimitiveCoefficientsType :=
  fun a n => match n with
  | 0 => 0
  | n+1 => a n / (n+1 : ℂ)

def complexPrimitiveRadius : Prop := ∀ a : ℕ → ℂ,
  complexPowerSeriesRadiusValue (complexPrimitiveCoefficientsValue a) = complexPowerSeriesRadiusValue a

def complexPrimitiveCenter : Prop := ∀ (a : ℕ → ℂ) (c : ℝ),
  complexSeriesHasSumValue (fun n => a n / (n+1 : ℂ) * ((c : ℂ)-(c : ℂ))^(n+1)) 0

def complexPrimitiveDerivative : Prop := ∀ (a : ℕ → ℂ) (c : ℝ) (f g : ℝ → ℂ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    ComplexPowerSeriesHasSumValue a c (x : ℂ) (f x)) →
  (∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    ComplexPowerSeriesHasSumValue (complexPrimitiveCoefficientsValue a) c (x : ℂ) (g x)) →
  ∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    HasDerivAt g (f x) x

def complexTermwiseIntegration : Prop := ∀ (a : ℕ → ℂ) (c : ℝ) (f : ℝ → ℂ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    ComplexPowerSeriesHasSumValue a c (x : ℂ) (f x)) →
  ∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
  ∃ hf : complexIntegrableValue f (min c x) (max c x),
    complexSeriesHasSumValue (fun n => a n / (n+1 : ℂ) * ((x : ℂ)-(c : ℂ))^(n+1))
      (if c ≤ x then complexIntegralValue f hf else -complexIntegralValue f hf)

end Specs.SingleVariableAnalysis.Ch13.Integration
