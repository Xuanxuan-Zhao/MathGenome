import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuity

/-! Independent statements for paper.tex:4047–4070. The real-line measure
structure is Borel; integrability allows all Lebesgue L¹ representatives.
Global AC is the shared uniform finite disjoint-interval condition.
`deriv` is the classical derivative, zero where it does not exist. -/
noncomputable section
open Set MeasureTheory
namespace Specs.D11.Ch12.AcStieltjesEquivalence
open ScalarStieltjesCorrespondence NormalizedStieltjes

/-- Uniform global AC, not merely AC on each bounded interval. -/
def density_ac : Prop :=
  ∀ {K : Type*} [RCLike K] (F f : ℝ → K), Integrable f volume →
    (∀ x, F x = ∫ t in Iic x, f t) → absolutelyContinuousValue F

/-- Every-point recovery and absolute integrability of the actual derivative. -/
def density_derivative : Prop :=
  ∀ {K : Type*} [RCLike K] (F f : ℝ → K), Integrable f volume →
    (∀ x, F x = ∫ t in Iic x, f t) →
    (∀ᵐ x ∂volume, HasDerivAt F (f x) x) ∧
    Integrable (deriv F) volume ∧
    (∀ x, F x = ∫ t in Iic x, deriv F t)

/-- For NBV, absolute continuity of the scalar total variation is equivalent
to an integrable scalar density on all Borel sets. -/
def measure_density_real : Prop :=
  ∀ F : ℝ → ℝ, NBV_value F →
    ((stieltjesMeasure_value F).variation ≪ volume ↔
      ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f volume ∧
        ∀ E, MeasurableSet E → stieltjesMeasure_value F E = ∫ t in E, f t)

def measure_density_complex : Prop :=
  ∀ F : ℝ → ℂ, NBV_value F →
    ((stieltjesMeasure_value F).variation ≪ volume ↔
      ∃ f : ℝ → ℂ, Measurable f ∧ Integrable f volume ∧
        ∀ E, MeasurableSet E → stieltjesMeasure_value F E = ∫ t in E, f t)

def measure_ac_real : Prop :=
  ∀ F : ℝ → ℝ, NBV_value F → (stieltjesMeasure_value F).variation ≪ volume →
    absolutelyContinuousValue F ∧
    Integrable (deriv F) volume ∧
    (∀ᵐ x ∂volume, HasDerivAt F (deriv F x) x) ∧
    ∀ x, F x = ∫ t in Iic x, deriv F t

def measure_ac_complex : Prop :=
  ∀ F : ℝ → ℂ, NBV_value F → (stieltjesMeasure_value F).variation ≪ volume →
    absolutelyContinuousValue F ∧
    Integrable (deriv F) volume ∧
    (∀ᵐ x ∂volume, HasDerivAt F (deriv F x) x) ∧
    ∀ x, F x = ∫ t in Iic x, deriv F t

/-- Full forward direction, uniform on ℝ and with no density assumed. -/
def ac_measure : Prop :=
  ∀ {K : Type*} [RCLike K] (F : ℝ → K), NBV_value F →
    absolutelyContinuousValue F → (stieltjesMeasure_value F).variation ≪ volume

/-- Complete global statements required by the manuscript. -/
def global_real : Prop :=
  ∀ F : ℝ → ℝ, NBV_value F →
    (absolutelyContinuousValue F ↔ (stieltjesMeasure_value F).variation ≪ volume) ∧
    (absolutelyContinuousValue F →
      Integrable (deriv F) volume ∧
      (∀ᵐ x ∂volume, HasDerivAt F (deriv F x) x) ∧
      ∀ x, F x = ∫ t in Iic x, deriv F t)

def global_complex : Prop :=
  ∀ F : ℝ → ℂ, NBV_value F →
    (absolutelyContinuousValue F ↔ (stieltjesMeasure_value F).variation ≪ volume) ∧
    (absolutelyContinuousValue F →
      Integrable (deriv F) volume ∧
      (∀ᵐ x ∂volume, HasDerivAt F (deriv F x) x) ∧
      ∀ x, F x = ∫ t in Iic x, deriv F t)

/-- The compact assertion is made for arbitrary F. Continuity is a conclusion
of AC and part of the right side of the equivalence, not an added hypothesis.
Normalization uses the original endpoint values and no right-limit replacement. -/
def compact_statement (K : Type*) [RCLike K] : Prop :=
  ∀ (F : ℝ → K) {a b : ℝ}, a < b →
    let G := compactNormalization_value F a b
    (absolutelyContinuousOnIntervalValue F a b ↔
      NBV_value G ∧ Continuous G ∧ (stieltjesMeasure_value G).variation ≪ volume) ∧
    (absolutelyContinuousOnIntervalValue F a b →
      (∀ x, stieltjesMeasure_value G {x} = 0) ∧
      IntegrableOn (deriv F) (Icc a b) ∧
      (∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (deriv F x) x) ∧
      ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, deriv F t)

def compact_real : Prop := compact_statement ℝ

def compact_complex : Prop := compact_statement ℂ

/-- Pointwise constant-extension bridge, without assuming BV or continuity. -/
def compactNormalization_ac_iff : Prop :=
  ∀ {K : Type*} [RCLike K] (F : ℝ → K) {a b : ℝ}, a ≤ b →
    (absolutelyContinuousOnIntervalValue F a b ↔
      absolutelyContinuousValue (compactNormalization_value F a b))

def compactNormalization_properties : Prop :=
  ∀ {K : Type*} [RCLike K] (F : ℝ → K) {a b : ℝ}, a < b →
    absolutelyContinuousOnIntervalValue F a b →
    NBV_value (compactNormalization_value F a b) ∧
      Continuous (compactNormalization_value F a b) ∧
      ∀ x, stieltjesMeasure_value (compactNormalization_value F a b) {x} = 0

/-- A density for the extension gives the compact classical derivative formula.
This is a conditional helper; the full compact statements above have no density
assumption and remain required. -/
def compact_density_reconstruction : Prop :=
  ∀ {K : Type*} [RCLike K] (F f : ℝ → K) {a b : ℝ}, a < b →
    Integrable f volume →
    (∀ x, compactNormalization_value F a b x = ∫ t in Iic x, f t) →
    IntegrableOn (deriv F) (Icc a b) ∧
      (∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (deriv F x) x) ∧
      ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, deriv F t

end Specs.D11.Ch12.AcStieltjesEquivalence
