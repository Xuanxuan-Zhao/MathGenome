import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.UniqueCycleCertificate
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.CycleCertificate

namespace P205.Matroids.UniqueCycleCertificate
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic Specs.P205.Matroids.TreeExchange
open Specs.P205.Matroids.CycleCertificate
open Specs.P205.Matroids.UniqueCycleCertificate
noncomputable section
universe u v
variable {α : Type u} {β : Type v}

/-- An equal-weight fundamental exchange supplies an explicit second minimizer. -/
lemma equality_alternative (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (w : G.edgeSet → ℝ) (T : Set β)
    (hm : MinimumSpanningTreeValue G hG w T)
    (e : G.edgeSet) (he : e.val ∉ T) (x y : G.vertexSet)
    (hl : G.IsLink e.val x.val y.val) (hxy : x ≠ y)
    (p : (spanningShadow G T).Walk x y) (hp : p.IsPath)
    (f : G.edgeSet) (hf : f.val ∈ pathLabels G T p) (hw : w e = w f) :
    ∃ D, D ≠ T ∧ MinimumSpanningTreeValue G hG w D ∧
      edgeWeightValue G hG w D = edgeWeightValue G hG w T := by
  let D := insert e.val (T \ {f.val})
  have hD : SpanningTreeValue G D :=
    (TreeExchange.path_exchange G hG hC T hm.1 hl he hxy p hp f.val hf.1).mpr hf
  have hne : D ≠ T := by
    intro h
    exact he (h ▸ Set.mem_insert e.val (T \ {f.val}))
  have hweight : edgeWeightValue G hG w D = edgeWeightValue G hG w T := by
    rw [CycleCertificate.weight_exchange G hG w hf.1 he, hw]
    ring
  exact ⟨D, hne, ⟨hD, fun A hA => hweight ▸ hm.2 A hA⟩, hweight⟩

lemma unique_implies_strict_cycle (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (w : G.edgeSet → ℝ) (T : Set β)
    (hm : UniqueMinimumSpanningTreeValue G hG w T) : StrictCycleBound G w T := by
  intro e he x y hl hxy p hp f hf
  have hle := CycleCertificate.minimum_implies_cycle G hG hC w T hm.1.1 hm.1
    e he x y hl hxy p hp f hf
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨D, hne, hD, _⟩ := equality_alternative G hG hC w T hm.1
    e he x y hl hxy p hp f hf heq.symm
  exact hne (hm.2 D hD)

/-- One exchange strictly improves any distinct competitor. Minimality of that
competitor is therefore impossible; no distinct-weight hypothesis is needed. -/
lemma strict_cycle_implies_unique (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (w : G.edgeSet → ℝ) (T : Set β)
    (hT : SpanningTreeValue G T) (hc : StrictCycleBound G w T) :
    UniqueMinimumSpanningTreeValue G hG w T := by
  classical
  have hc' : CycleBound G w T := fun e he x y hl hxy p hp f hf =>
    (hc e he x y hl hxy p hp f hf).le
  refine ⟨(CycleCertificate.minimum_iff_cycle G hG hC w T hT).mpr hc', ?_⟩
  intro D hmD
  have hD := hmD.1
  by_cases hsub : D ⊆ T
  · exact ((Graphic.connected_base_iff_tree G hG hC D).mpr hD).eq_of_subset_isBase
      ((Graphic.connected_base_iff_tree G hG hC T).mpr hT) hsub
  · obtain ⟨e, heD, heT⟩ := Set.not_subset.mp hsub
    obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet (hD.1 heD)
    let x : G.vertexSet := ⟨a, hl.left_mem⟩
    let y : G.vertexSet := ⟨b, hl.right_mem⟩
    have hxy : x ≠ y := by
      let := hD.2.1
      exact fun h => (show (G.restrict D).IsLink e a b from ⟨heD, hl⟩).ne
        (congrArg Subtype.val h)
    obtain ⟨p, hp, _⟩ := TreeExchange.unique_path G T hT x y
    have hcut := (TreeExchange.delete_tree_edge G hG D hD heD (a := x) (b := y) hl).2.1
    obtain ⟨f, hf, c, d, hfl, hcross⟩ := CycleCertificate.path_crosses G
      (spanningShadow G (D \ {e})) p hcut
    have hfe : f ≠ e := fun h => heT (h ▸ hf.1)
    have hfD : f ∉ D := by
      intro h
      exact hcross (edge_reachable G (A := D \ {e}) ⟨h, by simpa using hfe⟩ hfl)
    have hD' := TreeExchange.crossing_reconnects G hG hC D hD heD hfl hcross
    have hw := hc ⟨e, hD.1 heD⟩ heT x y hl hxy p hp ⟨f, hT.1 hf.1⟩ hf
    have hmin := hmD.2 _ hD'
    rw [CycleCertificate.weight_exchange G hG w (e := ⟨e, hD.1 heD⟩)
      (f := ⟨f, hT.1 hf.1⟩) heD hfD] at hmin
    exact (not_lt_of_ge hmin (by linarith)).elim

theorem unique_minimum_iff_strict_cycle : UniqueMinimumIffStrictCycleBound.{u,v} := by
  intro α β G hG hC w T hT
  exact ⟨unique_implies_strict_cycle G hG hC w T,
    strict_cycle_implies_unique G hG hC w T hT⟩

lemma strictCycleBound_iff_maximum (G : Graph α β) (hG : IsFiniteValue G)
    (w : G.edgeSet → ℝ) {T : Set β} (hT : SpanningTreeValue G T) :
    StrictCycleBound G w T ↔ StrictCycleMaximumBound G w T := by
  constructor
  · intro hc e he x y hl hxy p hp
    obtain ⟨f, hf, hfm⟩ := (CycleCertificate.pathWeights_maximum G hG w hT hxy p).1
    rw [← hfm]
    exact hc e he x y hl hxy p hp f hf
  · intro hc e he x y hl hxy p hp f hf
    exact lt_of_le_of_lt
      ((CycleCertificate.pathWeights_maximum G hG w hT hxy p).2 ⟨f, hf, rfl⟩)
      (hc e he x y hl hxy p hp)

theorem unique_minimum_iff_strict_cycle_maximum : UniqueMinimumIffStrictCycleMaximum.{u,v} := by
  intro α β G hG hC w T hT
  exact (unique_minimum_iff_strict_cycle G hG hC w T hT).trans
    (strictCycleBound_iff_maximum G hG w hT)

theorem equality_maximum_alternative : EqualityMaximumAlternative.{u,v} := by
  intro α β G hG hC w T hm e he x y hl hxy p hp hw
  obtain ⟨f, hf, hfm⟩ := (CycleCertificate.pathWeights_maximum G hG w hm.1 hxy p).1
  exact equality_alternative G hG hC w T hm e he x y hl hxy p hp f hf (hw.trans hfm.symm)

end
end P205.Matroids.UniqueCycleCertificate
