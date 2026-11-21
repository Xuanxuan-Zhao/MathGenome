import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.SafeCutEdge
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.TreeExchange
import Mathlib.Tactic.Linarith

namespace P205.Matroids.SafeCutEdge
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic
open Specs.P205.Matroids.TreeExchange
open Specs.P205.Matroids.SafeCutEdge
open scoped BigOperators
noncomputable section
universe u v
variable {α : Type u} {β : Type v}

/-- A walk whose endpoints are on opposite sides traverses a crossing label. -/
lemma walk_crosses (G : Graph α β) (T : Set β) (S : Set G.vertexSet)
    {x y : G.vertexSet} (p : (spanningShadow G T).Walk x y)
    (hx : x ∈ S) (hy : y ∉ S) :
    ∃ f, f ∈ pathLabels G T p ∧ Crosses G S f := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y h p ih =>
    by_cases hz : z ∈ S
    · obtain ⟨f, ⟨hf, a, b, hl, hp⟩, hc⟩ := ih hz hy
      exact ⟨f, ⟨hf, a, b, hl, by simp [hp]⟩, hc⟩
    · obtain ⟨f, hf, hl⟩ := h.2
      exact ⟨f, ⟨hf, x, z, hl, by simp⟩, x, z, hx, hz, hl⟩

theorem cut_nonempty : CutNonempty.{u,v} := by
  intro α β G hC S hS hproper
  obtain ⟨x, hx⟩ := hS
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem S).mp hproper
  have hr : (spanningShadow G G.edgeSet).Reachable x y := by
    simpa only [Graphic.spanningShadow_self G] using hC x y
  obtain ⟨p⟩ := hr
  obtain ⟨f, hf, hc⟩ := walk_crosses G G.edgeSet S p hx hy
  exact ⟨⟨f, hf.1⟩, hc⟩

/-- The weight change of a single labelled exchange, without restrictions on signs. -/
lemma exchange_weight (G : Graph α β) (hG : IsFiniteValue G)
    (w : G.edgeSet → ℝ) (D : Set β) (e f : G.edgeSet)
    (he : e.val ∉ D) (hf : f.val ∈ D) :
    edgeWeightValue G hG w (insert e.val (D \ {f.val})) =
      edgeWeightValue G hG w D + w e - w f := by
  classical
  let := hG.2.fintype
  have hne : e ≠ f := by
    intro h
    exact he (h ▸ hf)
  have hpoint : ∀ a : G.edgeSet,
      (@ite ℝ (a.val ∈ insert e.val (D \ {f.val})) (Classical.propDecidable _) (w a) 0) =
      (if a.val ∈ D then w a else 0) +
        (if a = e then w e else 0) - (if a = f then w f else 0) := by
    intro a
    by_cases hae : a = e
    · subst a
      simp [he, hne]
    · by_cases haf : a = f
      · subst a
        have hfe : f.val ≠ e.val := fun h => hae (Subtype.ext h)
        simp [hf, hae, hfe]
      · have hae' : a.val ≠ e.val := fun h => hae (Subtype.ext h)
        have haf' : a.val ≠ f.val := fun h => haf (Subtype.ext h)
        simp [hae, haf, hae', haf']
  unfold edgeWeightValue
  calc
    _ = ∑ a : G.edgeSet, ((if a.val ∈ D then w a else 0) +
        (if a = e then w e else 0) - (if a = f then w f else 0)) :=
      Finset.sum_congr rfl (fun a _ => hpoint a)
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp

theorem safe_cut_edge : SafeEdge.{u,v} := by
  intro α β G hG hC w F hforest hext S hS hproper hrespect e hecross hlight
  obtain ⟨D, hD, hFD⟩ := hext
  by_cases heD : e.val ∈ D
  · exact ⟨D, hD, Set.insert_subset heD hFD⟩
  obtain ⟨x, y, hx, hy, hel⟩ := hecross
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  obtain ⟨p, hp, _⟩ := TreeExchange.unique_path G D hD.1 x y
  obtain ⟨f, hfpath, hfcross⟩ := walk_crosses G D S p hx hy
  have hfD : f ∈ D := hfpath.1
  have hfF : f ∉ F := fun hf => hrespect f hf hfcross
  have hnew : SpanningTreeValue G (insert e.val (D \ {f})) :=
    (TreeExchange.path_exchange G hG hC D hD.1 hel heD hxy p hp f hfD).mpr hfpath
  let f' : G.edgeSet := ⟨f, hD.1.1 hfD⟩
  have hw : edgeWeightValue G hG w (insert e.val (D \ {f})) ≤
      edgeWeightValue G hG w D := by
    rw [exchange_weight G hG w D e f' heD hfD]
    have hle := hlight f' hfcross
    linarith
  refine ⟨insert e.val (D \ {f}), ⟨hnew, ?_⟩, ?_⟩
  · intro B hB
    exact hw.trans (hD.2 B hB)
  · intro a ha
    rcases ha with rfl | ha
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨hFD ha, fun h => hfF (h ▸ ha)⟩

end
end P205.Matroids.SafeCutEdge
