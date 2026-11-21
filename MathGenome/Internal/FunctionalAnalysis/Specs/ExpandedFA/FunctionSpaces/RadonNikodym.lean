import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Independent statements for `paper.tex:16758–16790`, `fa2:p4:radon-nikodym`.

An L¹ density is expressed by an integrable scalar representative, with
uniqueness for ordinary μ-a.e. equality. Thus uniqueness is in the usual scalar
L¹ quotient, not pointwise uniqueness and not a locally a.e. quotient. An
ordinary measurable representative is also supplied. For signed measures
`totalVariation` is the Hahn–Jordan variation; for complex measures `variation`
is the supremum over finite measurable partitions of sums of absolute values.
The extended integral identity records the mass without discarding infinity;
the real identity is exactly the stated integral of the absolute value.

Only μ is sigma-finite in the finite signed/complex cases. In the positive
case both measures are sigma-finite; the nonnegative real-valued density is
measurable and need not be globally integrable. No completeness of the measure
space, separability, or finiteness of μ is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.FunctionSpaces.RadonNikodymSpec

/-- Finite signed Radon–Nikodym, with exact variation and a.e. uniqueness. -/
def SignedRepresentation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : SignedMeasure X), ν ≪ᵥ μ.toENNRealVectorMeasure →
    ∃ g : X → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ A : Set X, MeasurableSet A → ν A = ∫ x in A, g x ∂μ) ∧
      (∫⁻ x, ‖g x‖ₑ ∂μ) = ν.totalVariation Set.univ ∧
      (∫ x, ‖g x‖ ∂μ) = ν.totalVariation.real Set.univ ∧
      ∀ h : X → ℝ, Integrable h μ →
        (∀ A : Set X, MeasurableSet A → ν A = ∫ x in A, h x ∂μ) → h =ᵐ[μ] g

/-- Finite complex Radon–Nikodym with its complex absolute value, rather than
separate bounds on the real and imaginary parts. -/
def ComplexRepresentation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : ComplexMeasure X), ν ≪ᵥ μ.toENNRealVectorMeasure →
    ∃ g : X → ℂ, Measurable g ∧ Integrable g μ ∧
      (∀ A : Set X, MeasurableSet A → ν A = ∫ x in A, g x ∂μ) ∧
      (∫⁻ x, ‖g x‖ₑ ∂μ) = ν.variation Set.univ ∧
      (∫ x, ‖g x‖ ∂μ) = ν.variation.real Set.univ ∧
      ∀ h : X → ℂ, Integrable h μ →
        (∀ A : Set X, MeasurableSet A → ν A = ∫ x in A, h x ∂μ) → h =ᵐ[μ] g

/-- Sigma-finite positive Radon–Nikodym with a finite-valued nonnegative
measurable density, allowing infinite total integral. -/
def PositiveRepresentation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : Measure X) [SigmaFinite ν], ν ≪ μ →
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      ∀ A : Set X, MeasurableSet A →
        ν A = ∫⁻ x in A, ENNReal.ofReal (g x) ∂μ

end ExpandedFA.FunctionSpaces.RadonNikodymSpec
