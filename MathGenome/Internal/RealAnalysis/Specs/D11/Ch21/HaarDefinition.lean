import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.LchGroupInterface

/-!
Independent specifications for paper.tex:5829–5831,
`d11:21:haar-definition`.

The domain of each measure is exactly the Borel sigma-algebra. Positivity
and countable additivity are supplied by `Measure`; nonzero mass, the three
shared Radon predicates, and invariance on Borel sets are required below.
No countability or sigma-finiteness hypothesis is imposed.
-/

namespace Specs.D11.Ch21.HaarDefinition

open MeasureTheory

universe u

/-- Haar predicates on the source's Hausdorff locally compact topological groups. -/
def haarPredicateType : Type (u + 1) :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G], @Measure G (borel G) → Prop

/-- Nonzero Radon measure invariant under every left translation of a Borel set. -/
def leftHaarValue : haarPredicateType.{u} := fun μ =>
  μ ≠ 0 ∧ Specs.D11.Ch18.RadonPredicates.isRadonValue μ ∧
    ∀ (a : _) (E : Set _), MeasurableSet[borel _] E →
      μ ((fun x => a * x) '' E) = μ E

/-- The same nonzero and Radon requirements, with right translations instead. -/
def rightHaarValue : haarPredicateType.{u} := fun μ =>
  μ ≠ 0 ∧ Specs.D11.Ch18.RadonPredicates.isRadonValue μ ∧
    ∀ (a : _) (E : Set _), MeasurableSet[borel _] E →
      μ ((fun x => x * a) '' E) = μ E

/-- The complete defining conditions, including the exact quantifiers. -/
def leftHaarIffStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    leftHaarValue μ ↔
      μ ≠ 0 ∧ Specs.D11.Ch18.RadonPredicates.isRadonValue μ ∧
        ∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
          μ ((fun x => a * x) '' E) = μ E

def rightHaarIffStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    rightHaarValue μ ↔
      μ ≠ 0 ∧ Specs.D11.Ch18.RadonPredicates.isRadonValue μ ∧
        ∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
          μ ((fun x => x * a) '' E) = μ E

end Specs.D11.Ch21.HaarDefinition
