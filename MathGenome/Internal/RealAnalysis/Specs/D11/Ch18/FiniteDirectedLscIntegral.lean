import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Independent statements for the arbitrary-index LSC integral interchange
used in the finite-factor open-set argument at paper.tex:5465–5469. -/
namespace Specs.D11.Ch18.FiniteDirectedLscIntegral

open Set MeasureTheory
open scoped ENNReal
universe u v

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- The supremum is everywhere Borel measurable, even for an arbitrary index. -/
def supremum_regularity : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {I : Type v}
    (f : I → X → ℝ≥0∞), (∀ i, LowerSemicontinuous (f i)) →
    LowerSemicontinuous (fun x => ⨆ i, f i x) ∧
      Measurable (fun x => ⨆ i, f i x)

/-- The same integral interchange without a bound on the LSC family. -/
def lintegral_iSup_directed_of_lowerSemicontinuous : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonPredicates.isRadonValue μ → μ univ < ∞ →
    ∀ {I : Type v} [Nonempty I] (f : I → X → ℝ≥0∞),
      (∀ i, LowerSemicontinuous (f i)) → Directed (· ≤ ·) f →
      (∫⁻ x, ⨆ i, f i x ∂μ) = ⨆ i, ∫⁻ x, f i x ∂μ

/-- Bounded directed monotone convergence for finite Radon Borel measures.
The space and the index have independent, arbitrary universes. -/
def lintegral_iSup_directed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonPredicates.isRadonValue μ → μ univ < ∞ →
    ∀ {I : Type v} [Nonempty I] (f : I → X → ℝ≥0∞),
      (∀ i, LowerSemicontinuous (f i)) → Directed (· ≤ ·) f →
      ∀ (C : ℝ≥0∞), C < ∞ → (∀ i x, f i x ≤ C) →
      (∫⁻ x, ⨆ i, f i x ∂μ) = ⨆ i, ∫⁻ x, f i x ∂μ

end Specs.D11.Ch18.FiniteDirectedLscIntegral
