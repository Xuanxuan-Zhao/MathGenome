import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonSupport

/-!
Independent statements of paper.tex:5872–5878 (`d11:21:haar-positive-open`).
The shared predicates retain precisely the source's nonzero Radon Borel
measure and its translation invariance, on arbitrary LCH Hausdorff groups.
Both left and right Haar measures are covered. Integrability is included
explicitly so positivity does not use a totalized integral without its domain.
-/
namespace Specs.D11.Ch21.HaarPositiveOpen

open MeasureTheory
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

/-- Every nonempty open set has strictly positive extended-real mass. -/
def positive_open : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    (HaarDefinition.leftHaarValue μ ∨ HaarDefinition.rightHaarValue μ) →
    ∀ U : Set G, IsOpen U → U.Nonempty → 0 < μ U

/-- All nonzero nonnegative real Cc tests are integrable with positive integral. -/
def integral_pos : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    (HaarDefinition.leftHaarValue μ ∨ HaarDefinition.rightHaarValue μ) →
    ∀ f : CompactlySupportedContinuousMap G ℝ, (∀ x, 0 ≤ f x) → f ≠ 0 →
      Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ (fun x => f x) ∧
        0 < ∫ x, f x ∂μ

/-- Full support, using the canonical complement of the union of null opens. -/
def full_support : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    (HaarDefinition.leftHaarValue μ ∨ HaarDefinition.rightHaarValue μ) →
    Specs.D11.Ch18.RadonSupport.supportValue μ = Set.univ

end Specs.D11.Ch21.HaarPositiveOpen
