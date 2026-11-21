import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition

/-!
Independent statements of paper.tex:5936–5943,
`d11:21:haar-finite-iff-compact`. All measures have exactly the Borel
domain and the shared nonzero, left invariant Radon predicate. No
countability, metrizability, sigma-compactness or sigma-finiteness is assumed.
-/
namespace Specs.D11.Ch21.HaarFiniteIffCompact

open MeasureTheory
universe u

/-- Finite total left Haar mass is equivalent to compactness of the group. -/
def finite_iff_compact : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ →
      (μ Set.univ < ⊤ ↔ CompactSpace G)

/-- Division by total mass normalizes any compact-group left Haar measure. -/
def normalize_probability : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ →
      HaarDefinition.leftHaarValue ((μ Set.univ)⁻¹ • μ) ∧
        ((μ Set.univ)⁻¹ • μ) Set.univ = 1

/-- A compact Hausdorff topological group has exactly one left Haar probability. -/
def unique_probability : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G],
    ∃! μ : @Measure G (borel G),
      HaarDefinition.leftHaarValue μ ∧ μ Set.univ = 1

end Specs.D11.Ch21.HaarFiniteIffCompact
