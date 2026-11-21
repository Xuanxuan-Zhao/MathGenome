import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Prim
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.SafeCutEdge
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.GraphicBridge
import Mathlib.Data.Set.Finite.Powerset

namespace P205.Matroids.Prim
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic
open Specs.P205.Matroids.SafeCutEdge
open Specs.P205.Matroids.Prim
noncomputable section
universe u v
variable {α : Type u} {β : Type v}

/-- A minimum exists since there are finitely many labelled edge subsets. -/
lemma minimum_tree_exists (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (w : G.edgeSet → ℝ) :
    ∃ D, MinimumSpanningTreeValue G hG w D := by
  have hf : {D | SpanningTreeValue G D}.Finite :=
    hG.2.finite_subsets.subset (fun _ h => h.1)
  obtain ⟨D, hD, hm⟩ := Set.exists_min_image {D | SpanningTreeValue G D}
    (edgeWeightValue G hG w) hf (Graphic.spanningTree_exists G hG hC)
  exact ⟨D, hD, hm⟩

lemma tree_forest (G : Graph α β) (hC : G.toSimpleGraph.Connected)
    {D : Set β} (hD : SpanningTreeValue G D) : ForestValue G D :=
  ((Graphic.connected_spanningForest_iff_tree G hC D).mpr hD).2.1

lemma shadow_mono (G : Graph α β) {F D : Set β} (h : F ⊆ D) :
    spanningShadow G F ≤ spanningShadow G D := by
  rintro x y ⟨hne, e, he, hl⟩
  exact ⟨hne, e, h he, hl⟩

lemma internal_respects (G : Graph α β) {S : Set G.vertexSet} {F : Set β}
    (hi : ∀ f ∈ F, ∀ x y : G.vertexSet, G.IsLink f x.val y.val → x ∈ S ∧ y ∈ S) :
    ∀ f ∈ F, ¬ Crosses G S f := by
  rintro f hf ⟨x, y, _, hy, hl⟩
  exact hy (hi f hf x y hl).2

/-- Simultaneous structural and safe-cut induction. -/
theorem run_invariants : RunInvariants.{u,v} := by
  intro α β G hG hC w r n S F hr
  let := hG.1.to_subtype
  induction hr with
  | start =>
    obtain ⟨D, hD⟩ := minimum_tree_exists G hG hC w
    have hf : ForestValue G (∅ : Set β) :=
      (tree_forest G hC hD.1).mono G (Set.empty_subset D)
    refine ⟨⟨by simp, by simp, by simp, hf, ?_, ?_⟩, D, hD, Set.empty_subset D⟩
    · simp
    · intro x hx
      have : x = r := by simpa using hx
      subst x
      exact .refl r
  | @next n S F S' F' hr hs ih =>
    obtain ⟨⟨hSc, hFc, hrS, hf, hi, hc⟩, hext⟩ := ih
    obtain ⟨e, x, y, hx, hy, hl, hw, rfl, rfl⟩ := hs
    have hcross : Crosses G S e.val := ⟨x, y, hx, hy, hl⟩
    have hproper : S ≠ Set.univ := fun h => hy (h ▸ Set.mem_univ y)
    have hres := internal_respects G hi
    have heF : e.val ∉ F := fun h => hres e.val h hcross
    have hext' := SafeCutEdge.safe_cut_edge G hG hC w F hf hext S
      ⟨r, hrS⟩ hproper hres e hcross hw
    obtain ⟨D, hD, hFD⟩ := hext'
    have hf' : ForestValue G (insert e.val F) := (tree_forest G hC hD.1).mono G hFD
    refine ⟨⟨?_, ?_, Set.mem_insert_of_mem y hrS, hf', ?_, ?_⟩, D, hD, hFD⟩
    · rw [Set.ncard_insert_of_notMem hy, hSc]
    · rw [Set.ncard_insert_of_notMem heF (hG.2.subset hf.1), hFc]
    · intro f hf a b hab
      rcases hf with rfl | hf
      · rcases hl.eq_and_eq_or_eq_and_eq hab with hh | hh
        · have ha : a = x := Subtype.ext hh.1.symm
          have hb : b = y := Subtype.ext hh.2.symm
          subst a; subst b
          exact ⟨Set.mem_insert_of_mem _ hx, Set.mem_insert _ _⟩
        · have ha : a = y := Subtype.ext hh.2.symm
          have hb : b = x := Subtype.ext hh.1.symm
          subst a; subst b
          exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ hx⟩
      · exact ⟨Set.mem_insert_of_mem _ (hi f hf a b hab).1,
          Set.mem_insert_of_mem _ (hi f hf a b hab).2⟩
    · intro z hz
      have hm := shadow_mono G (Set.subset_insert e.val F)
      rcases hz with hzy | hz
      · subst z
        have hxy : x ≠ y := fun h => hy (h ▸ hx)
        have ha : (spanningShadow G (insert e.val F)).Adj x y :=
          ⟨hxy, e.val, Set.mem_insert _ _, hl⟩
        exact (SimpleGraph.Reachable.mono hm (hc x hx)).trans ha.reachable
      · exact SimpleGraph.Reachable.mono hm (hc z hz)

/-- A proper visited set always has a light crossing edge. -/
theorem step_available : StepAvailable.{u,v} := by
  intro α β G hG hC w r n S F hr hproper
  let := hG.2.to_subtype
  have hi := (run_invariants G hG hC w r n S F hr).1
  obtain ⟨e₀, he₀⟩ := SafeCutEdge.cut_nonempty G hC S ⟨r, hi.2.2.1⟩ hproper
  obtain ⟨e, he, hw⟩ := Set.exists_min_image
    {e : G.edgeSet | Crosses G S e.val} w (Set.toFinite _) ⟨e₀, he₀⟩
  obtain ⟨x, y, hx, hy, hl⟩ := he
  have hs : Step G w S F (insert y S) (insert e.val F) :=
    ⟨e, x, y, hx, hy, hl, hw, rfl, rfl⟩
  exact ⟨_, _, hs, hr.next hs⟩

/-- There is one new vertex per addition, so completion occurs at exactly |V|-1. -/
theorem run_length : RunLength.{u,v} := by
  intro α β G hG hC w r n S F hr
  let := hG.1.to_subtype
  have hSc := (run_invariants G hG hC w r n S F hr).1.1
  have hN : 0 < G.vertexSet.ncard := (Set.ncard_pos hG.1).mpr ⟨r.val, r.property⟩
  have hle : n + 1 ≤ G.vertexSet.ncard := by
    simpa only [hSc, Set.ncard_univ, Nat.card_coe_set_eq] using
      (Set.ncard_le_ncard (Set.subset_univ S))
  refine ⟨by omega, ?_⟩
  constructor
  · intro hS
    have hh : n + 1 = G.vertexSet.ncard := by
      simpa only [hS, Set.ncard_univ, Nat.card_coe_set_eq] using hSc.symm
    omega
  · intro hn
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ S)
    simp only [Set.ncard_univ, Nat.card_coe_set_eq, hSc]
    omega

/-- Runs stop exactly when all actual vertices have been visited. -/
theorem run_termination : RunTermination.{u,v} := by
  intro α β G hG hC w r n S F hr
  constructor
  · intro hstop
    apply (run_length G hG hC w r n S F hr).2.mp
    by_contra hproper
    obtain ⟨S', F', hs, _⟩ := step_available G hG hC w r n S F hr hproper
    exact hstop ⟨S', F', hs⟩
  · intro hn
    have hS := (run_length G hG hC w r n S F hr).2.mpr hn
    rintro ⟨S', F', e, x, y, hx, hy, _⟩
    exact hy (hS ▸ Set.mem_univ y)

/-- At completion the partial tree spans. A spanning subtree of an MST is that MST. -/
theorem run_minimum : RunMinimum.{u,v} := by
  intro α β G hG hC w r n S F hr hS
  obtain ⟨⟨_, _, _, hf, _, hc⟩, D, hD, hFD⟩ :=
    run_invariants G hG hC w r n S F hr
  have hb : SpanningForestValue G F := by
    refine ⟨hf.1, hf, ?_⟩
    intro x y _
    exact (hc x (hS ▸ Set.mem_univ x)).symm.trans (hc y (hS ▸ Set.mem_univ y))
  have hbt := (Graphic.connected_spanningForest_iff_tree G hC F).mp hb
  have hbF := (Graphic.connected_base_iff_tree G hG hC F).mpr hbt
  have hbD := (Graphic.connected_base_iff_tree G hG hC D).mpr hD.1
  have heq : F = D := hbF.eq_of_subset_isBase hbD hFD
  exact ⟨heq ▸ hD, (run_length G hG hC w r n S F hr).2.mp hS⟩

/-- Extend any prefix until the visited set is full; no choices get stuck. -/
theorem run_completion : RunCompletion.{u,v} := by
  intro α β G hG hC w r n S F hr
  have aux : ∀ k n S F, Run G w r n S F →
      n + k = G.vertexSet.ncard - 1 →
      ∃ F', Run G w r (G.vertexSet.ncard - 1) Set.univ F' ∧ F ⊆ F' ∧
        MinimumSpanningTreeValue G hG w F' := by
    intro k
    induction k with
    | zero =>
      intro n S F hr hn
      have hn : n = G.vertexSet.ncard - 1 := by simpa using hn
      have hS := (run_length G hG hC w r n S F hr).2.mpr hn
      refine ⟨F, ?_, Set.Subset.rfl, (run_minimum G hG hC w r n S F hr hS).1⟩
      simpa only [hn, hS] using hr
    | succ k ih =>
      intro n S F hr hn
      have hproper : S ≠ Set.univ := by
        intro hS
        have := (run_length G hG hC w r n S F hr).2.mp hS
        omega
      obtain ⟨S', F', hs, hr'⟩ := step_available G hG hC w r n S F hr hproper
      obtain ⟨F'', hr'', hsub, hmin⟩ := ih (n+1) S' F' hr' (by omega)
      have hFF' : F ⊆ F' := by
        obtain ⟨e, x, y, hx, hy, hl, hw, hS', hF'⟩ := hs
        rw [hF']
        exact Set.subset_insert _ _
      exact ⟨F'', hr'', hFF'.trans hsub, hmin⟩
  exact aux (G.vertexSet.ncard - 1 - n) n S F hr
    (by have := (run_length G hG hC w r n S F hr).1; omega)

/-- Prim produces a minimum spanning tree from every initial vertex. -/
theorem prim_correct : PrimCorrect.{u,v} := by
  intro α β G hG hC w r
  obtain ⟨F, hr, _, hm⟩ := run_completion G hG hC w r 0 {r} ∅ (Run.start)
  exact ⟨F, hr, hm⟩

end
end P205.Matroids.Prim
