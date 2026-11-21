import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition

/-!
Independent statements for paper.tex:5919–5925, `d11:21:haar-uniqueness`.
The measures are on exactly the Borel sigma-algebra of an arbitrary locally
compact Hausdorff topological group. The shared Haar predicates require only
compact finiteness, Borel outer regularity, and compact-inner regularity on
opens. A real scalar is finite by its type; strict positivity is explicit.
Equality of Borel measures in particular gives equality on every Borel set.
-/
namespace Specs.D11.Ch21.HaarUniqueness

open MeasureTheory
universe u

def left_uniqueness : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ ν : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.leftHaarValue μ →
    Specs.D11.Ch21.HaarDefinition.leftHaarValue ν →
    ∃! c : ℝ, 0 < c ∧ ν = ENNReal.ofReal c • μ

def right_uniqueness : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ ν : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.rightHaarValue μ →
    Specs.D11.Ch21.HaarDefinition.rightHaarValue ν →
    ∃! c : ℝ, 0 < c ∧ ν = ENNReal.ofReal c • μ

end Specs.D11.Ch21.HaarUniqueness
