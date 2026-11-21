import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.CompactCompleteTotalBounded
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness

/-!
Theorem `d10:12:compact-complete-tb` of paper.tex. The accepted Chapter 5
bridge identifies open-cover compactness with compactness of the whole set.
The accepted uniform conventions identify proper Cauchy-filter completeness
and finite entourage-section covers with Mathlib's conditions. The library's
compact-set criterion requires only UniformSpace, with no separation axiom.
-/

open Set Filter
universe u

namespace D10Topology.Ch12

/-- A uniform space is compact exactly when it is complete and totally bounded.
There is no separatedness or nonemptiness hypothesis. -/
theorem compact_iff_complete_totallyBounded (X : Type u) [UniformSpace X] :
    Ch05.CoverCompact X ↔ Complete X ∧ TotallyBoundedSpace X := by
  constructor
  · intro h
    obtain ⟨ht, hc⟩ := isCompact_iff_totallyBounded_isComplete.mp
      ((Ch05.coverCompact_iff_isCompact_univ X).mp h)
    exact ⟨complete_iff_mathlib.mpr (completeSpace_of_isComplete_univ hc),
      totallyBoundedSpace_iff_mathlib.mpr ht⟩
  · rintro ⟨hc, ht⟩
    apply (Ch05.coverCompact_iff_isCompact_univ X).mpr
    exact isCompact_iff_totallyBounded_isComplete.mpr
      ⟨totallyBoundedSpace_iff_mathlib.mp ht,
        completeSpace_iff_isComplete_univ.mp (complete_iff_mathlib.mp hc)⟩

/-- The empty uniform space satisfies all three conditions, and supports no
proper ultrafilter. In particular no point or ultrafilter is chosen here. -/
theorem empty_uniform_space_properties (X : Type u) [UniformSpace X] [IsEmpty X] :
    Ch05.CoverCompact X ∧ Complete X ∧ TotallyBoundedSpace X ∧
      ∀ F : Filter X, ¬ Specs.D10Topology.Ch05.Ultrafilters.IsUltrafilter F := by
  refine ⟨Ch05.empty_space_compact X, complete_empty, totallyBoundedSpace_empty, ?_⟩
  intro F hF
  obtain ⟨x, _⟩ := hF.1.nonempty_of_mem (univ_mem : (univ : Set X) ∈ F)
  exact isEmptyElim x

end D10Topology.Ch12
