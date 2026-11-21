import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveContentOuterMeasure

/-!
Localization stage of paper.tex:5770–5775. The original measure has exactly
its Borel domain. The enlarged domain is the full splitting sigma-algebra,
with tests over all subsets; no sigma-finiteness or countability is imposed.
-/
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch20.RadonCaratheodoryLocalization
universe u

abbrev Radon {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)) : Prop :=
  Specs.D11.Ch18.RadonPredicates.isRadonValue μ

def outerMeasure_type :=
  {X : Type u} → [TopologicalSpace X] → @Measure X (borel X) → OuterMeasure X

def outerMeasure_value : outerMeasure_type.{u} :=
  fun μ => @Measure.toOuterMeasure _ (borel _) μ

def measurableSpace_type :=
  {X : Type u} → [TopologicalSpace X] → @Measure X (borel X) → MeasurableSpace X

def measurableSpace_value : measurableSpace_type.{u} :=
  fun μ => (outerMeasure_value μ).caratheodory

def measure_type :=
  {X : Type u} → [TopologicalSpace X] → (μ : @Measure X (borel X)) →
    @Measure X (measurableSpace_value μ)

noncomputable def measure_value : measure_type.{u} :=
  fun μ => Specs.D11.Ch02.Caratheodory.measure_value (outerMeasure_value μ)

def outerMeasure_formula : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), Radon μ → ∀ A : Set X,
    outerMeasure_value μ A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), μ U

/-- Existence of the actual integral functional and equality of the two outer
measures. The equality of functionals is to the scalar integral, not an
assumed representing certificate. Compact support ensures integrability. -/
def content_agreement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), Radon μ →
    ∃ I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ,
      ∃ hI : Specs.D11.Ch19.PositiveContentOuterMeasure.Positive I,
      (letI : MeasurableSpace X := borel X
       ∀ f : CompactlySupportedContinuousMap X ℝ,
         Integrable f μ ∧ I f = ∫ x, f x ∂μ) ∧
      outerMeasure_value μ = Specs.D11.Ch19.PositiveContentOuterMeasure.outerMeasure_value I hI

def borel_measurable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    borel X ≤ measurableSpace_value μ

/-- Equality of outer values does not assert Borel measurability of A. -/
def measure_apply : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)) (A : Set X),
    measure_value μ A = μ A

def complete : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    @Measure.IsComplete X (measurableSpace_value μ) (measure_value μ)

def finite_inner_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), Radon μ → ∀ A : Set X,
    MeasurableSet[measurableSpace_value μ] A → measure_value μ A < ∞ →
    measure_value μ A =
      ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), measure_value μ K

def local_measurable_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), Radon μ → ∀ B : Set X,
    MeasurableSet[measurableSpace_value μ] B ↔
      ∀ K : Set X, IsCompact K → MeasurableSet[measurableSpace_value μ] (B ∩ K)

end Specs.D11.Ch20.RadonCaratheodoryLocalization
