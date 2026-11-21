import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CountablePrecompactBase
import Mathlib.Topology.Compactness.SigmaCompact

/-!
The topological portion of the proof of
`d11:18:baire-borel-second-countable` in `paper.tex`.
Only point-set topology is used. All sequences are indexed by `ℕ`,
so no enumeration of an empty family is required.
-/

open Set TopologicalSpace

universe u

namespace D11.Ch18

/-- Second-countable locally compact Hausdorff spaces have countable
bases of precompact open sets. -/
theorem countablePrecompactBase : Specs.D11.Ch18.CountablePrecompactBase.{u} := by
  intro X _ _ _ _
  have hb : IsTopologicalBasis {V : Set X | IsOpen V ∧ IsCompact (closure V)} := by
    refine isTopologicalBasis_of_isOpen_of_nhds (fun _ hV => hV.1) ?_
    intro x U hx hU
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
    refine ⟨interior K, ⟨isOpen_interior, ?_⟩, hxK, interior_subset.trans hKU⟩
    exact hK.of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset hK.isClosed)
  obtain ⟨B, hBsub, hBcount, hBbasis⟩ := hb.exists_countable
  exact ⟨B, hBcount, hBbasis, fun _ hV => hBsub hV⟩

/-- Every ambient open set is a countable union of compact subsets contained in it. -/
theorem openCompactCover : Specs.D11.Ch18.OpenCompactCover.{u} := by
  intro X _ _ _ _ U hU
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hKU⟩ := hσ
  refine ⟨K, fun n => ⟨hK n, ?_⟩, hKU.symm⟩
  exact (subset_iUnion K n).trans hKU.subset

/-- Compact sets are countable intersections of ambient open sets.
Apply the compact-cover theorem to the open complement and take complements. -/
theorem compactOpenIntersection : Specs.D11.Ch18.CompactOpenIntersection.{u} := by
  intro X _ _ _ _ K hK
  obtain ⟨L, hL, hcover⟩ := openCompactCover X Kᶜ hK.isClosed.isOpen_compl
  refine ⟨fun n => (L n)ᶜ, fun n => (hL n).1.isClosed.isOpen_compl, ?_⟩
  simpa only [compl_compl, compl_iUnion] using congrArg (fun s : Set X => sᶜ) hcover

end D11.Ch18
