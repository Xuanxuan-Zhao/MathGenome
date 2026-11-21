import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinEven

/-! Statements for `fa2:p4:krein-nonunique` in the adopted source.
`Nonunique` asks for actual different frequency measures with the constant
frequency assigned only to the cosine part, and includes normalization. -/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.PartIV.KreinNonunique.Spec

/-- A normalized counterexample, distinguished by its hyperbolic atom at 1.
The support, mass, integrability and moment conditions are all those of the
upstream two-measure representation, with no cosh atom at zero. -/
def Nonunique : Prop :=
  ∃ (p : ℝ → ℝ) (α₁ β₁ α₂ β₂ : Measure ℝ),
    Continuous p ∧ Function.Even p ∧ p 0 = 1 ∧
    KreinEven.Spec.EvenTestPositive p ∧
    KreinEven.Spec.Mixture p α₁ β₁ ∧ KreinEven.Spec.Mixture p α₂ β₂ ∧
    0 < β₁ {1} ∧ β₂ {1} = 0

/-- Regularity follows from the actual measure representation. -/
def MixtureRegularity : Prop :=
  ∀ (p : ℝ → ℝ) (α β : Measure ℝ), KreinEven.Spec.Mixture p α β →
    Continuous p ∧ Function.Even p

/-- Positive common rescaling preserves every condition in the representation. -/
def MixtureScaling : Prop :=
  ∀ (p : ℝ → ℝ) (α β : Measure ℝ) (c : ℝ), 0 ≤ c →
    KreinEven.Spec.Mixture p α β →
    KreinEven.Spec.Mixture (fun s => c * p s)
      (ENNReal.ofReal c • α) (ENNReal.ofReal c • β)

/-- The final normalization step does not assume test positivity or regularity:
these follow from the measure hypotheses. It does require the common mass to
be strictly positive, which the discrete construction must establish. -/
def NormalizeCounterexample : Prop :=
  ∀ (p : ℝ → ℝ) (α₁ β₁ α₂ β₂ : Measure ℝ),
    KreinEven.Spec.Mixture p α₁ β₁ → KreinEven.Spec.Mixture p α₂ β₂ →
    0 < p 0 → 0 < β₁ {1} → β₂ {1} = 0 → Nonunique

/-- The two positive parts of a finite signed cosine measure. -/
def CosineDecomposition (h : ℝ → ℝ) (αp αm : Measure ℝ) : Prop :=
  IsFiniteMeasure αp ∧ IsFiniteMeasure αm ∧ αp (Iio 0) = 0 ∧ αm (Iio 0) = 0 ∧
    ∀ s : ℝ, Integrable (fun a => Real.cos (a * s)) αp ∧
      Integrable (fun a => Real.cos (a * s)) αm ∧
      h s = (∫ a, Real.cos (a * s) ∂αp) - ∫ a, Real.cos (a * s) ∂αm

/-- The zero coefficient is in the cosine measure γ. The strict positive
frequency measures are the positive and negative nonconstant cosh parts. -/
def HyperbolicDecomposition (h : ℝ → ℝ) (γ βp βm : Measure ℝ) : Prop :=
  IsFiniteMeasure γ ∧ IsFiniteMeasure βp ∧ IsFiniteMeasure βm ∧
    γ (Iio 0) = 0 ∧ βp (Iic 0) = 0 ∧ βm (Iic 0) = 0 ∧
    (∀ s : ℝ, Integrable (fun a => Real.cos (a * s)) γ ∧
      Integrable (fun b => Real.cosh (b * s)) βp ∧
      Integrable (fun b => Real.cosh (b * s)) βm ∧
      h s = (∫ a, Real.cos (a * s) ∂γ) +
        (∫ b, Real.cosh (b * s) ∂βp) - ∫ b, Real.cosh (b * s) ∂βm) ∧
    (∀ R : ℝ, 0 < R → Integrable (fun b => Real.cosh (R * b)) βp ∧
      Integrable (fun b => Real.cosh (R * b)) βm) ∧
    0 < βm {1} ∧ βp {1} = 0

/-- Rearrange two signed transform identities and positively normalize. -/
def AssembleCounterexample : Prop :=
  ∀ (h : ℝ → ℝ) (αp αm γ βp βm : Measure ℝ),
    CosineDecomposition h αp αm → HyperbolicDecomposition h γ βp βm → Nonunique

end ExpandedFA.PartIV.KreinNonunique.Spec
