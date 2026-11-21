import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.CycleCertificate
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.TreeExchange
import Mathlib.Order.ConditionallyCompleteLattice.Finset

namespace P205.Matroids.CycleCertificate
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic Specs.P205.Matroids.TreeExchange
open Specs.P205.Matroids.CycleCertificate
noncomputable section
universe u v
variable {α : Type u} {β : Type v}

/-- A walk joining disconnected vertices must traverse a link joining
disconnected vertices. The labels are those of the original multigraph. -/
lemma path_crosses (G : Graph α β) {T : Set β}
    (H : SimpleGraph G.vertexSet) {x y : G.vertexSet}
    (p : (spanningShadow G T).Walk x y) (hn : ¬ H.Reachable x y) :
    ∃ f ∈ pathLabels G T p, ∃ a b : G.vertexSet,
      G.IsLink f a.val b.val ∧ ¬ H.Reachable a b := by
  induction p with
  | nil => exact (hn (SimpleGraph.Reachable.refl _)).elim
  | @cons x z y h p ih =>
    by_cases hxz : H.Reachable x z
    · obtain ⟨f, hf, a, b, hl, hab⟩ := ih (fun hzy => hn (hxz.trans hzy))
      exact ⟨f, ⟨hf.1, by
        obtain ⟨c, d, hcd, hm⟩ := hf.2
        exact ⟨c, d, hcd, by simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]; exact Or.inr hm⟩⟩,
        a, b, hl, hab⟩
    · obtain ⟨f, hf, hl⟩ := h.2
      exact ⟨f, ⟨hf, x, z, hl, by simp⟩, x, z, hl, hxz⟩

lemma weight_exchange (G : Graph α β) (hG : IsFiniteValue G)
    (w : G.edgeSet → ℝ) {D : Set β} {e f : G.edgeSet}
    (he : e.val ∈ D) (hf : f.val ∉ D) :
    edgeWeightValue G hG w (insert f.val (D \ {e.val})) =
      edgeWeightValue G hG w D + w f - w e := by
  classical
  let := hG.2.fintype
  have hef : e ≠ f := by intro h; exact hf (h ▸ he)
  have hh : ∀ a : G.edgeSet, ∀ dec : Decidable (a.val ∈ insert f.val (D \ {e.val})),
      (@ite ℝ (a.val ∈ insert f.val (D \ {e.val})) dec (w a) 0) =
      (if a.val ∈ D then w a else 0) + (if a = f then w a else 0) -
        (if a = e then w a else 0) := by
    intro a dec
    by_cases hae : a = e
    · subst a; simp [he, hef, show e.val ≠ f.val from fun h => hef (Subtype.ext h)]
    by_cases haf : a = f
    · subst a; simp [hf, Ne.symm hef]
    have hae' : a.val ≠ e.val := fun h => hae (Subtype.ext h)
    have haf' : a.val ≠ f.val := fun h => haf (Subtype.ext h)
    simp [hae, haf, hae', haf']
  simp only [edgeWeightValue]
  simp_rw [hh]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

/-- Necessity follows by exchanging any label on the fundamental path. -/
lemma minimum_implies_cycle (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (w : G.edgeSet → ℝ) (T : Set β)
    (hT : SpanningTreeValue G T) (hm : MinimumSpanningTreeValue G hG w T) :
    CycleBound G w T := by
  intro e he x y hl hxy p hp f hf
  have ht := (TreeExchange.path_exchange G hG hC T hT hl he hxy p hp f.val hf.1).mpr hf
  have hw := hm.2 _ ht
  rw [weight_exchange G hG w hf.1 he] at hw
  linarith

/-- Each competitor can be changed toward T without increasing weight. -/
lemma cycle_weight_le (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (w : G.edgeSet → ℝ) (T : Set β)
    (hT : SpanningTreeValue G T) (hc : CycleBound G w T) :
    ∀ D, SpanningTreeValue G D →
      edgeWeightValue G hG w T ≤ edgeWeightValue G hG w D := by
  classical
  intro D
  generalize hn : (D \ T).ncard = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    intro hD
    by_cases hsub : D ⊆ T
    · have hDb := (Graphic.connected_base_iff_tree G hG hC D).mpr hD
      have hTb := (Graphic.connected_base_iff_tree G hG hC T).mpr hT
      have heq := hDb.eq_of_subset_isBase hTb hsub
      exact le_of_eq (congrArg (edgeWeightValue G hG w) heq.symm)
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
      obtain ⟨f, hf, c, d, hfl, hcross⟩ := path_crosses G
        (spanningShadow G (D \ {e})) p hcut
      have hfe : f ≠ e := fun h => heT (h ▸ hf.1)
      have hfD : f ∉ D := by
        intro h
        exact hcross (edge_reachable G (A := D \ {e}) ⟨h, by simpa using hfe⟩ hfl)
      have hD' := TreeExchange.crossing_reconnects G hG hC D hD heD hfl hcross
      have hw : w ⟨f, hT.1 hf.1⟩ ≤ w ⟨e, hD.1 heD⟩ :=
        hc ⟨e, hD.1 heD⟩ heT x y hl hxy p hp ⟨f, hT.1 hf.1⟩ hf
      have hdiff : (insert f (D \ {e})) \ T = (D \ T) \ {e} := by
        ext z
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | hz, hzT⟩
          · exact (hzT hf.1).elim
          · exact ⟨⟨hz.1, hzT⟩, hz.2⟩
        · rintro ⟨⟨hzD, hzT⟩, hze⟩
          exact ⟨Or.inr ⟨hzD, hze⟩, hzT⟩
      have hlt : ((insert f (D \ {e})) \ T).ncard < n := by
        rw [hdiff, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem ⟨heD, heT⟩ ((hG.2.subset hD.1).sdiff)
      have hle := ih _ hlt (insert f (D \ {e})) rfl hD'
      have hex := weight_exchange G hG w (e := ⟨e, hD.1 heD⟩)
        (f := ⟨f, hT.1 hf.1⟩) heD hfD
      rw [hex] at hle
      linarith

theorem minimum_iff_cycle : MinimumIffCycleBound.{u,v} := by
  intro α β G hG hC w T hT
  exact ⟨minimum_implies_cycle G hG hC w T hT,
    fun hc => ⟨hT, cycle_weight_le G hG hC w T hT hc⟩⟩

/-- The supremum used in the displayed certificate is an attained path maximum. -/
lemma pathWeights_maximum (G : Graph α β) (hG : IsFiniteValue G)
    (w : G.edgeSet → ℝ) {T : Set β} (hT : SpanningTreeValue G T)
    {x y : G.vertexSet} (hxy : x ≠ y) (p : (spanningShadow G T).Walk x y) :
    IsGreatest (w '' {f : G.edgeSet | f.val ∈ pathLabels G T p})
      (sSup (w '' {f : G.edgeSet | f.val ∈ pathLabels G T p})) := by
  let := hG.2.fintype
  have hfin := (Set.toFinite {f : G.edgeSet | f.val ∈ pathLabels G T p}).image w
  obtain ⟨f, hf⟩ := TreeExchange.pathLabels_nonempty G T p hxy
  have hne : (w '' {f : G.edgeSet | f.val ∈ pathLabels G T p}).Nonempty :=
    ⟨w ⟨f, hT.1 hf.1⟩, ⟨⟨f, hT.1 hf.1⟩, hf, rfl⟩⟩
  exact hne.isGreatest_csSup hfin

lemma cycleBound_iff_maximum (G : Graph α β) (hG : IsFiniteValue G)
    (w : G.edgeSet → ℝ) {T : Set β} (hT : SpanningTreeValue G T) :
    CycleBound G w T ↔ CycleMaximumBound G w T := by
  constructor
  · intro hc e he x y hl hxy p hp
    obtain ⟨f, hf, hfm⟩ := (pathWeights_maximum G hG w hT hxy p).1
    rw [← hfm]
    exact hc e he x y hl hxy p hp f hf
  · intro hc e he x y hl hxy p hp f hf
    have hle := (pathWeights_maximum G hG w hT hxy p).2 ⟨f, hf, rfl⟩
    exact hle.trans (hc e he x y hl hxy p hp)

theorem minimum_iff_cycle_maximum : MinimumIffCycleMaximum.{u,v} := by
  intro α β G hG hC w T hT
  exact (minimum_iff_cycle G hG hC w T hT).trans (cycleBound_iff_maximum G hG w hT)

end
end P205.Matroids.CycleCertificate
