import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.LebesgueDecompositionFiniteTarget
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNPositiveSigmaFinite
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNSignedComplex

/-! Independent statements for paper.tex:4922–4945. All measures and measurable
functions use the original sigma-algebra. Positive densities can have infinite
total integral. Uniqueness of the parts is stated without subtraction, and the
parts are explicitly restrictions to a measurable reference-null support and
its complement. The scalar density is absolutely integrable. -/

open Set MeasureTheory
open scoped ENNReal
universe u

namespace Specs.D11.Ch15.LebesgueDecompositionSigmaFinite

/-- Uniqueness among all positive AC/singular decompositions. -/
def PositiveDecomposition {X : Type u} [MeasurableSpace X]
    (ν μ a s : Measure X) : Prop :=
  SigmaFinite a ∧ SigmaFinite s ∧ ν = a + s ∧ a ≪ μ ∧
  Ch14.ScalarInterfaces.positiveSingular_value s μ ∧
  ∀ a' s' : Measure X, ν = a' + s' → a' ≪ μ →
    Ch14.ScalarInterfaces.positiveSingular_value s' μ → a' = a ∧ s' = s

def positive_decomposition : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [SigmaFinite μ] [SigmaFinite ν],
    ∃ Z : Set X, MeasurableSet Z ∧ μ Z = 0 ∧
      PositiveDecomposition ν μ (ν.restrict Zᶜ) (ν.restrict Z) ∧
      ∃ h : X → ℝ≥0∞, Measurable h ∧ (∀ x, h x < ∞) ∧
        (∀ E, MeasurableSet E → ν.restrict Zᶜ E =
          Ch05.NonnegativeIntegral.nonnegativeIntegral_value (μ.restrict E) h) ∧
        ∀ k : X → ℝ≥0∞, Measurable k →
          (∀ E, MeasurableSet E → ν.restrict Zᶜ E =
            Ch05.NonnegativeIntegral.nonnegativeIntegral_value (μ.restrict E) k) → h =ᵐ[μ] k

/-- A measurable L¹ representative, the set-integral identity, variation
identity, and uniqueness of its L¹ class. -/
def ScalarDensity {X : Type u} [MeasurableSpace X]
    {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] [MeasurableSpace K]
    (μ : Measure X) (a : VectorMeasure X K) (h : X → K) : Prop :=
  Measurable h ∧ Integrable h μ ∧
    (∀ E, MeasurableSet E → a E = ∫ x in E, h x ∂μ) ∧
    (∀ E, MeasurableSet E → Ch14.TotalVariation.totalVariation_value a E =
      ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ) ∧
    ∀ k : X → K, Integrable k μ →
      (∀ E, MeasurableSet E → a E = ∫ x in E, k x ∂μ) → h =ᵐ[μ] k

def signed_decomposition : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : SignedMeasure X),
    ∃ Z : Set X, MeasurableSet Z ∧ μ Z = 0 ∧
      LebesgueDecompositionFiniteTarget.Decomposition ν μ (ν.restrict Zᶜ) (ν.restrict Z) ∧
      ∃ h : X → ℝ, ScalarDensity μ (ν.restrict Zᶜ) h

def complex_decomposition : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : ComplexMeasure X),
    ∃ Z : Set X, MeasurableSet Z ∧ μ Z = 0 ∧
      LebesgueDecompositionFiniteTarget.Decomposition ν μ (ν.restrict Zᶜ) (ν.restrict Z) ∧
      ∃ h : X → ℂ, ScalarDensity μ (ν.restrict Zᶜ) h

end Specs.D11.Ch15.LebesgueDecompositionSigmaFinite
