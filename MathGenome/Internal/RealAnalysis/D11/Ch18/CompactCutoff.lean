import MathGenome.Internal.RealAnalysis.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CompactCutoff
import Mathlib.Topology.UrysohnsLemma

/-!
# Compact-support cutoffs in locally compact Hausdorff spaces

The topological Urysohn cutoff theorem supplies a continuous real map
with compact topological support contained in the prescribed open set.
Bundling this map in the canonical Cc interface retains all its properties.
Only topology and the definition-only Chapter 19 interface are used.
-/

namespace D11.Ch18

universe u

/-- The compact-open cutoff lemma, with support equal to the closure of
the nonzero set, as in paper.tex:5346. -/
theorem compact_cutoff (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (K U : Set X) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : D11.Ch19.Cc X ℝ,
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ K, φ x = 1) ∧
      IsCompact (closure {x | φ x ≠ 0}) ∧
      closure {x | φ x ≠ 0} ⊆ U := by
  obtain ⟨f, hfK, hfcompact, hfsupport, hfrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let φ : D11.Ch19.Cc X ℝ := ⟨f, hfcompact⟩
  exact ⟨φ, hfrange, hfK, hfcompact, hfsupport⟩

end D11.Ch18
