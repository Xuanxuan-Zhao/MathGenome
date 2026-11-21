import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.Characterizations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.BinarySpaces

open Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations

abbrev Edge : EdgeType := EdgeValue

abbrev EdgeVector : EdgeVectorType := EdgeVectorValue

abbrev edgeIndicator : edgeIndicatorType := edgeIndicatorValue

abbrev edgeSupport : edgeSupportType := edgeSupportValue

abbrev edgeSetEquiv : edgeSetEquivType := edgeSetEquivValue

abbrev cutEdges : cutEdgesType := cutEdgesValue

abbrev cutVector : cutVectorType := cutVectorValue

abbrev cutSpace : cutSpaceType := cutSpaceValue

abbrev walkVector : walkVectorType := walkVectorValue

abbrev cycleSpace : cycleSpaceType := cycleSpaceValue

abbrev dotProduct : dotProductType := dotProductValue

abbrev EvenDegree : EvenDegreeType := EvenDegreeValue

abbrev SpanningForest : SpanningForestType := SpanningForestValue

abbrev NonforestEdge : NonforestEdgeType := NonforestEdgeValue

abbrev ForestEdge : ForestEdgeType := ForestEdgeValue

abbrev forestPath : forestPathType := forestPathValue

abbrev fundamentalCycleWalk : fundamentalCycleWalkType := fundamentalCycleWalkValue

abbrev fundamentalCycle : fundamentalCycleType := fundamentalCycleValue

abbrev fundamentalCutSide : fundamentalCutSideType := fundamentalCutSideValue

abbrev fundamentalCut : fundamentalCutType := fundamentalCutValue

theorem indicator_symmDiff : indicator_symmDiffType := by
  intro V _ G S T
  classical
  funext e
  change (if e ∈ symmDiff S T then (1 : ZMod 2) else 0) =
    (if e ∈ S then 1 else 0) + (if e ∈ T then 1 else 0)
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases hs : e ∈ S <;> by_cases ht : e ∈ T <;>
    simp [Set.mem_symmDiff, hs, ht, htwo]

theorem cut_membership : cut_membershipType := by
  intro V _ G S a b h
  change (∃ x y, s(a, b) = s(x, y) ∧ x ∈ S ∧ y ∉ S) ↔ _
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact ⟨a, b, rfl, ha, hb⟩
    · exact ⟨b, a, Sym2.eq_swap, hb, ha⟩

theorem exists_spanningForest : exists_spanningForestType := by
  intro V _ G
  obtain ⟨F, hle, hacyc, hreach, _⟩ := Trees.spanning_forest G
  exact ⟨⟨F, hle, hacyc, hreach⟩⟩

theorem forestPath_unique : forestPath_uniqueType := by
  intro V _ G F e p
  exact (F.property.2.1.subsingleton_path _ _).elim _ _

theorem fundamentalCycle_isCycle : fundamentalCycle_isCycleType := by
  intro V _ G F e
  unfold fundamentalCycleWalkValue
  apply (SimpleGraph.Walk.cons_isCycle_iff _ _).mpr
  refine ⟨(forestPathValue G F e.val).property.mapLe F.property.1, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges, Sym2.mk_fst_out_snd_out]
  intro he
  exact e.property ((forestPathValue G F e.val).val.edges_subset_edgeSet he)

theorem fundamentalCut_separates : fundamentalCut_separatesType := by
  intro V _ G F e
  change (F.val.deleteEdges {e.val.val}).Reachable e.val.val.out.1 e.val.val.out.1 ∧
    ¬(F.val.deleteEdges {e.val.val}).Reachable e.val.val.out.1 e.val.val.out.2
  refine ⟨SimpleGraph.Reachable.refl _, ?_⟩
  have hb : F.val.IsBridge e.val.val :=
    SimpleGraph.isAcyclic_iff_forall_isBridge.mp F.property.2.1 e.property
  have hb' : F.val.IsBridge s(e.val.val.out.1, e.val.val.out.2) := by
    rwa [Sym2.mk_fst_out_snd_out]
  simpa only [Sym2.mk_fst_out_snd_out] using SimpleGraph.isBridge_iff.mp hb'

end FiniteCombinatorics.Graph.BinarySpaces
