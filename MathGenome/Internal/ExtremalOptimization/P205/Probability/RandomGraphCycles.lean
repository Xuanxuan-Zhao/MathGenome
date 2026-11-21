import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.RandomGraphCycles
import MathGenome.Internal.ExtremalOptimization.P205.Probability.FiniteModels
import MathGenome.Internal.ExtremalOptimization.P205.Probability.MarkovZeroDefect
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace P205.Probability.RandomGraphCycles

theorem parameter_mem_unit : Specs.P205.Probability.RandomGraphCycles.ParameterInUnitInterval :=
  fun _ _ hg hn => parameter_valid hg hn

theorem independent_edges : Specs.P205.Probability.RandomGraphCycles.IndependentEdges := by
  intro g n hg hn
  exact FiniteModel.independent_coordinates _

/-- The decoded graph has exactly the edges selected by the experiment. -/
lemma graph_edge_iff {n : ℕ} (ω : Outcome n) (e : Edge n) :
    e.val ∈ (graph ω).edgeSet ↔ ω e = true := by
  rw [graph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨⟨he, hω⟩, _⟩
    exact hω
  · intro hω
    exact ⟨⟨e.property, hω⟩, by
      simpa only [SimpleGraph.edgeSet_top, Set.mem_compl_iff] using e.property⟩

lemma mem_graphEdges {n : ℕ} (H : SimpleGraph (Fin n)) (e : Edge n) :
    e ∈ graphEdges H ↔ e.val ∈ H.edgeSet := by
  simp only [graphEdges, Finset.mem_map, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨a, ha⟩
    have hv := congrArg (fun e : Edge n => e.val) ha
    rw [← hv]
    exact SimpleGraph.mem_edgeFinset.mp a.property
  · intro he
    exact ⟨⟨e.val, SimpleGraph.mem_edgeFinset.mpr he⟩, Subtype.ext rfl⟩

lemma graphEdges_subset_iff {n : ℕ} (H K : SimpleGraph (Fin n)) :
    graphEdges H ⊆ graphEdges K ↔ H ≤ K := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  constructor
  · intro h e he
    have ht : e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := SimpleGraph.edgeSet_mono le_top he
    exact (mem_graphEdges K ⟨e, ht⟩).mp (h ((mem_graphEdges H ⟨e, ht⟩).mpr he))
  · intro h e he
    exact (mem_graphEdges K e).mpr (h ((mem_graphEdges H e).mp he))

lemma occurs_graphEdges_iff {n : ℕ} (ω : Outcome n) (H : SimpleGraph (Fin n)) :
    ω ∈ occurs (graphEdges H) ↔ H ≤ graph ω := by
  rw [← graphEdges_subset_iff]
  simp only [occurs, Set.mem_ofPred_eq, Finset.subset_iff, mem_graphEdges, graph_edge_iff]

lemma occurs_iff_graph {n : ℕ} (ω : Outcome n) (S : Finset (Edge n)) :
    ω ∈ occurs S ↔ ∀ e ∈ S, e.val ∈ (graph ω).edgeSet := by
  simp only [occurs, Set.mem_ofPred_eq, graph_edge_iff]

theorem cycle_meaning : Specs.P205.Probability.RandomGraphCycles.CycleMeaning := by
  intro n l hl ω
  rw [← SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < l),
    SimpleGraph.isContained_iff_exists_le_comap]
  constructor
  · rintro ⟨S, hS, hω⟩
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨f, SimpleGraph.map_le_iff_le_comap.mp ((occurs_graphEdges_iff ω _).mp hω)⟩
  · rintro ⟨f, hf⟩
    refine ⟨graphEdges ((SimpleGraph.cycleGraph l).map f),
      Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (occurs_graphEdges_iff ω _).mpr (SimpleGraph.map_le_iff_le_comap.mpr hf)

lemma card_graphEdges {n : ℕ} (H : SimpleGraph (Fin n)) :
    (graphEdges H).card = H.edgeFinset.card := by
  simp [graphEdges]

lemma card_cycleGraph {l : ℕ} (hl : 3 ≤ l) :
    (SimpleGraph.cycleGraph l).edgeFinset.card = l := by
  have hl' : l = (l - 3) + 3 := by omega
  rw [hl']
  have h := (SimpleGraph.cycleGraph ((l - 3) + 3)).sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.cycleGraph_degree_three_le, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] at h ⊢
  omega

lemma card_cycle {n l : ℕ} (hl : 3 ≤ l) {S : Finset (Edge n)} (hS : S ∈ cycles n l) :
    S.card = l := by
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hS
  rw [card_graphEdges]
  have h := SimpleGraph.card_edgeFinset_map f (SimpleGraph.cycleGraph l)
  have hc := card_cycleGraph hl
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] at h hc ⊢
  exact h.trans hc

lemma number_cycles_le (n l : ℕ) : (cycles n l).card ≤ n ^ l := by
  calc
    (cycles n l).card ≤ Fintype.card (Fin l ↪ Fin n) := Finset.card_image_le.trans_eq (by simp)
    _ ≤ Fintype.card (Fin l → Fin n) :=
      Fintype.card_le_of_injective (fun f => (f : Fin l → Fin n)) (fun _ _ h => DFunLike.coe_injective h)
    _ = n ^ l := by simp

/-- A cylinder requiring a prescribed finite set of edges has its product probability. -/
lemma cylinder_mass (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n) (S : Finset (Edge n)) :
    (model g n hg hn).eventMass (occurs S) = parameter g n ^ S.card := by
  let p := parameter g n
  let B := bernoulli p (parameter_valid hg hn)
  let f : Edge n → Bool → ℝ := fun e b =>
    if e ∈ S then (if b = true then B.weight b else 0) else B.weight b
  have hf (ω : Outcome n) :
      (occurs S).indicator (model g n hg hn).weight ω = ∏ e, f e (ω e) := by
    by_cases h : ω ∈ occurs S
    · rw [Set.indicator_of_mem h]
      change (∏ e, B.weight (ω e)) = ∏ e, f e (ω e)
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S
      · simp [f, he, h e he]
      · simp [f, he]
    · rw [Set.indicator_of_notMem h]
      obtain ⟨e, he⟩ := not_forall.mp h
      have hm : e ∈ S := by
        by_contra hm
        exact he (fun he' => (hm he').elim)
      have hb : ω e ≠ true := fun hb => he (fun _ => hb)
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [f, hm, hb])
  unfold FiniteModel.eventMass
  simp_rw [hf]
  change (∑ ω : Edge n → Bool, ∏ e, f e (ω e)) = _
  rw [← Fintype.prod_sum]
  have hsum (e : Edge n) : (∑ b : Bool, f e b) = if e ∈ S then p else 1 := by
    by_cases he : e ∈ S <;> simp [f, he, B, bernoulli]
  simp_rw [hsum]
  rw [Finset.prod_ite_mem_eq]
  simp [p]

theorem edge_marginal : Specs.P205.Probability.RandomGraphCycles.EdgeMarginal := by
  intro g n hg hn e
  have h := cylinder_mass g n hg hn {e}
  simpa [occurs] using h

lemma count_nonneg (g n : ℕ) (ω : Outcome n) : 0 ≤ count g n ω := by
  unfold count
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω))

lemma count_eq_card (g n : ℕ) (ω : Outcome n) :
    count g n ω = ∑ l ∈ Finset.Icc 3 g,
      (((cycles n l).filter (fun S => ω ∈ occurs S)).card : ℝ) := by
  unfold count
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply]

theorem count_meaning : Specs.P205.Probability.RandomGraphCycles.CountMeaning := by
  intro g n ω
  rw [count_eq_card]
  simp_rw [occurs_iff_graph]

lemma expected_count_formula (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n) :
    (model g n hg hn).expectation (count g n) =
      ∑ l ∈ Finset.Icc 3 g, ((cycles n l).card : ℝ) * parameter g n ^ l := by
  unfold count
  rw [FiniteModel.expectation_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [FiniteModel.expectation_sum]
  calc
    _ = ∑ S ∈ cycles n l, parameter g n ^ l := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [FiniteModel.expectation_indicator, cylinder_mass, card_cycle (Finset.mem_Icc.mp hl).1 hS]
    _ = _ := by simp [mul_comm]

/-- The exponent choice makes every length at most g contribute at most √n. -/
lemma length_expectation_bound {g n l : ℕ} (hg : 3 ≤ g) (hn : 1 ≤ n) (hl : l ≤ g) :
    (n : ℝ) ^ l * parameter g n ^ l ≤ Real.sqrt n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hl' : (l : ℝ) ≤ g := by exact_mod_cast hl
  rw [parameter, ← mul_pow]
  have hbase : (n : ℝ) * (n : ℝ) ^ (-1 + 1 / (2 * (g : ℝ))) =
      (n : ℝ) ^ (1 + (-1 + 1 / (2 * (g : ℝ)))) := by
    simpa only [Real.rpow_one] using (Real.rpow_add hnpos 1 (-1 + 1 / (2 * (g : ℝ)))).symm
  rw [hbase]
  rw [show (1 : ℝ) + (-1 + 1 / (2 * (g : ℝ))) = 1 / (2 * (g : ℝ)) by ring]
  rw [← Real.rpow_mul_natCast (le_of_lt hnpos), Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hn'
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    1 / (2 * (g : ℝ)) * (l : ℝ) * 2 = (l : ℝ) / g := by field_simp
    _ ≤ 1 := (div_le_one hgpos).2 hl'

theorem expected_short_cycles : Specs.P205.Probability.RandomGraphCycles.ExpectedShortCycles := by
  intro g n hg hn
  rw [expected_count_formula]
  calc
    _ ≤ ∑ l ∈ Finset.Icc 3 g, Real.sqrt (n : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hc : ((cycles n l).card : ℝ) ≤ (n : ℝ) ^ l := by
        exact_mod_cast number_cycles_le n l
      calc
        _ ≤ (n : ℝ) ^ l * parameter g n ^ l :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg (parameter_valid hg hn).1 _)
        _ ≤ _ := length_expectation_bound hg hn (Finset.mem_Icc.mp hl).2
    _ ≤ (g : ℝ) * Real.sqrt n := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (Finset.Icc 3 g).card ≤ g := by
        rw [Nat.card_Icc]
        omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.sqrt_nonneg _)

theorem short_cycle_tail : Specs.P205.Probability.RandomGraphCycles.ShortCycleTail := by
  intro g n hg hn
  let M := model g n hg hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hMarkov := markov_bound M.measure (count g n)
    (measurable_of_finite _) (FiniteModel.integrable_all M _) (Filter.Eventually.of_forall (count_nonneg g n))
    ((n : ℝ) / 2) (by positivity)
  rw [FiniteModel.integral_expectation, Measure.real, FiniteModel.measureReal_eventMass] at hMarkov
  calc
    _ ≤ M.expectation (count g n) / ((n : ℝ) / 2) := hMarkov
    _ ≤ ((g : ℝ) * Real.sqrt n) / ((n : ℝ) / 2) :=
      div_le_div_of_nonneg_right (expected_short_cycles g n hg hn) (by positivity)
    _ = 2 * (g : ℝ) / Real.sqrt n := by
      apply (div_eq_div_iff (by positivity) (ne_of_gt hspos)).2
      have hs := Real.sq_sqrt (le_of_lt hnpos)
      nlinarith

end P205.Probability.RandomGraphCycles
