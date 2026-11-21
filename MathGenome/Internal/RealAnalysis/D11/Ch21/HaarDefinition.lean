import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.D11.Ch21.LchGroupInterface
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition

/-!
# Left and right Haar measures

This is the definition in paper.tex:5829–5831, `d11:21:haar-definition`.
The native positive measure is on exactly `borel G`. The regularity
requirement is the shared Chapter 18 Radon predicate: compact finiteness,
Borel outer regularity, and compact-inner regularity on opens.
The group has the original Hausdorff locally compact topological group
hypotheses, with no countability, metrizability, or sigma-finiteness assumption.
-/

namespace D11.Ch21

open MeasureTheory

universe u

/-- A left Haar measure is nonzero, Radon, and invariant on Borel sets
under left translation. -/
def isLeftHaarMeasure {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)) : Prop :=
  μ ≠ 0 ∧ D11.Ch18.isRadon μ ∧
    ∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
      μ ((fun x => a * x) '' E) = μ E

/-- A right Haar measure has the same nonzero and Radon requirements
and is invariant on Borel sets under right translation. -/
def isRightHaarMeasure {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)) : Prop :=
  μ ≠ 0 ∧ D11.Ch18.isRadon μ ∧
    ∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
      μ ((fun x => x * a) '' E) = μ E

theorem isLeftHaarMeasure_iff {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)) :
    isLeftHaarMeasure μ ↔
      μ ≠ 0 ∧ D11.Ch18.isRadon μ ∧
        ∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
          μ ((fun x => a * x) '' E) = μ E := Iff.rfl

theorem isRightHaarMeasure_iff {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)) :
    isRightHaarMeasure μ ↔
      μ ≠ 0 ∧ D11.Ch18.isRadon μ ∧
        ∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
          μ ((fun x => x * a) '' E) = μ E := Iff.rfl

end D11.Ch21
