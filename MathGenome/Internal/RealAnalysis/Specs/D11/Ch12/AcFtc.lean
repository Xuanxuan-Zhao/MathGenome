import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Independent statements for the AC fundamental theorem, paper.tex:4072–4089.
The function retains its point values, including both endpoints. Densities are
arbitrary L¹ representatives. The classical derivative is totalized by zero
where no finite derivative exists. -/
noncomputable section
open Set MeasureTheory
namespace Specs.D11.Ch12.AcFtc

/-- The three equivalent conditions, together with identification and uniqueness
of every representing density. No BV differentiability premise is imposed. -/
def ftc_statement (K : Type*) [RCLike K] : Prop :=
  ∀ (F : ℝ → K) {a b : ℝ}, a < b →
    (absolutelyContinuousOnIntervalValue F a b ↔
      ∃ f : ℝ → K, IntegrableOn f (Icc a b) ∧
        ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, f t) ∧
    (absolutelyContinuousOnIntervalValue F a b ↔
      (∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (deriv F x) x) ∧
      IntegrableOn (deriv F) (Icc a b) ∧
      ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, deriv F t) ∧
    (∀ f : ℝ → K, IntegrableOn f (Icc a b) →
      (∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, f t) →
      f =ᵐ[volume.restrict (Icc a b)] deriv F ∧
      ∀ g : ℝ → K, IntegrableOn g (Icc a b) →
        (∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, g t) →
        f =ᵐ[volume.restrict (Icc a b)] g)

def ftc_real : Prop := ftc_statement ℝ

def ftc_complex : Prop := ftc_statement ℂ

/-- Explicit convention for the derivative representative. This is independent
of any choice of L¹ density. -/
def derivative_representative : Prop :=
  ∀ {K : Type*} [RCLike K] [MeasurableSpace K] [BorelSpace K] (F : ℝ → K),
    Measurable (deriv F) ∧
      ∀ x, ¬ DifferentiableAt ℝ F x → deriv F x = 0

end Specs.D11.Ch12.AcFtc
