import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Kruskal
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.GreedyBasis
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.GraphicBridge

/-! Kruskal's algorithm for finite labelled undirected multigraphs.
Foresthood tests actual labelled cycles, so loops are rejected and parallel
edges remain distinct. The proof identifies the scan with basis greedy and
applies maximum-weight optimality to the negatives of the given weights. -/
namespace P205.Matroids.Graphic
noncomputable section
universe u v

def kruskalStep : Specs.P205.Matroids.Graphic.kruskalStepType.{u, v} :=
  @Specs.P205.Matroids.Graphic.kruskalStepValue.{u, v}

def kruskalState : Specs.P205.Matroids.Graphic.kruskalStateType.{u, v} :=
  @Specs.P205.Matroids.Graphic.kruskalStateValue.{u, v}

def kruskalOutput : Specs.P205.Matroids.Graphic.kruskalOutputType.{u, v} :=
  @Specs.P205.Matroids.Graphic.kruskalOutputValue.{u, v}

def KruskalOrdering : Specs.P205.Matroids.Graphic.KruskalOrderingType.{u, v} :=
  @Specs.P205.Matroids.Graphic.KruskalOrderingValue.{u, v}

/-- Graphic independence and foresthood give the very same insertion decision. -/
theorem kruskal_step_eq_greedy {α : Type u} {β : Type v}
    (G : Graph α β) (hG : IsFinite G) :
    kruskalStep G = greedyStep (graphicMatroid G hG) := by
  classical
  funext I e
  have hi : (graphicMatroid G hG).Indep (insert e.val I) ↔
      Specs.P205.Matroids.Graphic.ForestValue G (insert e.val I) :=
    indep_iff_forest G hG (insert e.val I)
  simp only [kruskalStep, Specs.P205.Matroids.Graphic.kruskalStepValue,
    greedyStep, Specs.P205.Matroids.greedyStepValue, hi]

theorem kruskal_state_eq_greedy : Specs.P205.Matroids.Graphic.KruskalStateEqGreedy := by
  intro α β G hG l i
  change (l.take i).foldl (kruskalStep G) ∅ =
    (l.take i).foldl (greedyStep (graphicMatroid G hG)) ∅
  rw [kruskal_step_eq_greedy G hG]
  rfl

/-- Ascending original weights are descending negated weights, including ties. -/
theorem kruskal_ordering_neg {α : Type u} {β : Type v}
    (G : Graph α β) (hG : IsFinite G) (w : G.edgeSet → ℝ)
    (l : List G.edgeSet) (hl : KruskalOrdering G w l) :
    GreedyOrdering (graphicMatroid G hG) (fun e => -w e) l := by
  rcases hl with ⟨hn, he, hw⟩
  exact ⟨hn, he, hw.imp (fun h => neg_le_neg h)⟩

/-- Negating each real edge weight negates the total on every subset. -/
theorem subsetSum_neg {α : Type u} (M : Matroid α) [M.Finite]
    (w : Coordinates M) (B : Set α) :
    subsetSum M (fun e => -w e) B = -subsetSum M w B := by
  classical
  simp only [subsetSum, Specs.P205.Matroids.subsetSumValue]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

/-- Every exhaustive increasing-weight scan minimizes weight over spanning forests. -/
theorem kruskal_minimum_forest : Specs.P205.Matroids.Graphic.KruskalMinimumForest := by
  intro α β G hG w l hl
  have : (graphicMatroid G hG).Finite := ⟨hG.2⟩
  have ho := kruskal_ordering_neg G hG w l hl
  obtain ⟨hb, hopt⟩ := greedy_basis_optimal (graphicMatroid G hG) (fun e => -w e) l ho
  have hout : kruskalOutput G l = greedyOutput (graphicMatroid G hG) l :=
    kruskal_state_eq_greedy G hG l l.length
  apply (minimumSpanningForest_iff_base G hG w (kruskalOutput G l)).2
  refine ⟨hout.symm ▸ hb, ?_⟩
  intro D hD
  have h := hopt D hD
  change subsetSum (graphicMatroid G hG) (fun e => -w e) D ≤
    subsetSum (graphicMatroid G hG) (fun e => -w e)
      (greedyOutput (graphicMatroid G hG) l) at h
  have hn : -subsetSum (graphicMatroid G hG) w D ≤
      -subsetSum (graphicMatroid G hG) w (greedyOutput (graphicMatroid G hG) l) := by
    calc
      _ = subsetSum (graphicMatroid G hG) (fun e => -w e) D :=
        (subsetSum_neg (graphicMatroid G hG) w D).symm
      _ ≤ subsetSum (graphicMatroid G hG) (fun e => -w e)
          (greedyOutput (graphicMatroid G hG) l) := h
      _ = _ := subsetSum_neg (graphicMatroid G hG) w _
  have hh := neg_le_neg_iff.mp hn
  change subsetSum (graphicMatroid G hG) w (kruskalOutput G l) ≤
    subsetSum (graphicMatroid G hG) w D
  exact hout.symm ▸ hh

/-- For a connected graph (hence with a vertex), this is a minimum spanning tree. -/
theorem kruskal_minimum_tree : Specs.P205.Matroids.Graphic.KruskalMinimumTree := by
  intro α β G hG hC w l hl
  exact (connected_minimum_iff G hG hC w (kruskalOutput G l)).mp
    (kruskal_minimum_forest G hG w l hl)

theorem kruskal_empty_edges : Specs.P205.Matroids.Graphic.KruskalEmptyEdges := by
  intro α β G hE l
  cases l with
  | nil => rfl
  | cons e l => exact False.elim (by simpa [hE] using e.property)

theorem kruskal_empty_vertices : Specs.P205.Matroids.Graphic.KruskalEmptyVertices := by
  intro α β G hV l
  have hE : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
    simpa [hV] using h.left_mem
  exact kruskal_empty_edges G hE l

end
end P205.Matroids.Graphic
