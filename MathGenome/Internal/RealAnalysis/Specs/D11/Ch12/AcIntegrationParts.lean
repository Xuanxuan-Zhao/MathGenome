import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent statements for integration by parts, paper.tex:4142–4156.
The shared AC predicate tests finite disjoint open intervals, retaining the
original point values at both endpoints. Derivatives are real-parameter
derivatives, including when the values are complex. Both integrands are
explicitly absolutely integrable before their integral identity is asserted. -/

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate

namespace Specs.D11.Ch12.AcIntegrationParts

def bilinear_statement (K : Type*) [RCLike K] : Prop :=
  ∀ (F G : ℝ → K) {a b : ℝ}, a < b →
    absolutelyContinuousOnIntervalValue F a b →
    absolutelyContinuousOnIntervalValue G a b →
    IntegrableOn (fun x => deriv F x * G x) (Icc a b) ∧
    IntegrableOn (fun x => F x * deriv G x) (Icc a b) ∧
    (∫ x in a..b, deriv F x * G x) + (∫ x in a..b, F x * deriv G x) =
      F b * G b - F a * G a

def real_parts : Prop := bilinear_statement ℝ

def complex_parts : Prop := bilinear_statement ℂ

/-- The second factor is conjugated; the first factor remains linear. -/
def sesquilinear_parts : Prop :=
  ∀ (F G : ℝ → ℂ) {a b : ℝ}, a < b →
    absolutelyContinuousOnIntervalValue F a b →
    absolutelyContinuousOnIntervalValue G a b →
    IntegrableOn (fun x => deriv F x * conj (G x)) (Icc a b) ∧
    IntegrableOn (fun x => F x * conj (deriv G x)) (Icc a b) ∧
    (∫ x in a..b, deriv F x * conj (G x)) +
      (∫ x in a..b, F x * conj (deriv G x)) =
      F b * conj (G b) - F a * conj (G a)

end Specs.D11.Ch12.AcIntegrationParts
