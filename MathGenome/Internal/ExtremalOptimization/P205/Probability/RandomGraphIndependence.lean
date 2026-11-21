import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.RandomGraphIndependence
import MathGenome.Internal.ExtremalOptimization.P205.Probability.RandomGraphCycles
import MathGenome.Internal.ExtremalOptimization.P205.Probability.UnionBound
import MathGenome.Internal.ExtremalOptimization.P205.Probability.PositiveProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Push

open MeasureTheory
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace P205.Probability.RandomGraphIndependence
open RandomGraphCycles

/-- Internal possible edges of a prescribed vertex subset. -/
noncomputable def internalGraph {n : ℕ} (S : Finset (Fin n)) : SimpleGraph (Fin n) :=
  (⊤ : SimpleGraph S).map (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ Fin n)

lemma internalGraph_adj {n : ℕ} (S : Finset (Fin n)) (u v : Fin n) :
    (internalGraph S).Adj u v ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  simp only [internalGraph, SimpleGraph.map_adj, SimpleGraph.top_adj]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    exact ⟨x.property, y.property, fun h => hxy (Subtype.ext h)⟩
  · rintro ⟨hu, hv, hne⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => hne (congrArg Subtype.val h), rfl, rfl⟩

lemma internalEdges_card {n : ℕ} (S : Finset (Fin n)) :
    (graphEdges (internalGraph S)).card = S.card.choose 2 := by
  rw [card_graphEdges, internalGraph]
  have h := SimpleGraph.card_edgeFinset_map
    (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ Fin n) (⊤ : SimpleGraph S)
  have hc := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := S)
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] at h hc ⊢
  exact h.trans (hc.trans (by simp))

lemma independent_iff_absent {n : ℕ} (S : Finset (Fin n)) (ω : Outcome n) :
    (graph ω).IsIndepSet (S : Set (Fin n)) ↔
      ∀ e ∈ graphEdges (internalGraph S), ω e = false := by
  constructor
  · intro h e he
    have he' := (mem_graphEdges _ e).mp he
    have hnot : e.val ∉ (graph ω).edgeSet := by
      have hh : ∀ d : Sym2 (Fin n), d ∈ (internalGraph S).edgeSet →
          d ∉ (graph ω).edgeSet := by
        intro d
        induction d using Sym2.ind with
        | _ u v =>
          intro hd
          have huv := (internalGraph_adj S u v).mp hd
          exact h huv.1 huv.2.1 huv.2.2
      exact hh e.val he'
    have := (graph_edge_iff ω e).not.mp hnot
    cases hb : ω e <;> simp_all
  · intro h u hu v hv hne hadj
    have ht : s(u, v) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := hne
    let e : Edge n := ⟨s(u, v), ht⟩
    have he : e ∈ graphEdges (internalGraph S) :=
      (mem_graphEdges _ e).mpr ((internalGraph_adj S u v).mpr ⟨hu, hv, hne⟩)
    have hh := h e he
    have hh' : ω e = true := (graph_edge_iff ω e).mp hadj
    simp_all

/-- The product weights give the probability that prescribed edges are absent. -/
lemma absent_cylinder_mass (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n) (S : Finset (Edge n)) :
    (model g n hg hn).eventMass {ω | ∀ e ∈ S, ω e = false} =
      (1 - parameter g n) ^ S.card := by
  let p := parameter g n
  let B := bernoulli p (parameter_valid hg hn)
  let f : Edge n → Bool → ℝ := fun e b =>
    if e ∈ S then (if b = false then B.weight b else 0) else B.weight b
  have hf (ω : Outcome n) :
      ({ω | ∀ e ∈ S, ω e = false} : Set (Outcome n)).indicator
        (model g n hg hn).weight ω = ∏ e, f e (ω e) := by
    by_cases h : ω ∈ ({ω | ∀ e ∈ S, ω e = false} : Set (Outcome n))
    · rw [Set.indicator_of_mem h]
      change (∏ e, B.weight (ω e)) = ∏ e, f e (ω e)
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S
      · simp [f, he, h e he]
      · simp [f, he]
    · rw [Set.indicator_of_notMem h]
      change ¬ ∀ e ∈ S, ω e = false at h
      push Not at h
      obtain ⟨e, he, hb⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [f, he, hb])
  unfold FiniteModel.eventMass
  simp_rw [hf]
  change (∑ ω : Edge n → Bool, ∏ e, f e (ω e)) = _
  rw [← Fintype.prod_sum]
  have hsum (e : Edge n) : (∑ b : Bool, f e b) = if e ∈ S then 1 - p else 1 := by
    by_cases he : e ∈ S <;> simp [f, he, B, bernoulli]
  simp_rw [hsum]
  rw [Finset.prod_ite_mem_eq]
  simp [p]

theorem independent_set_probability :
    Specs.P205.Probability.RandomGraphIndependence.IndependentSetProbability := by
  intro g n hg hn S
  have heq : {ω : Outcome n | (graph ω).IsIndepSet (S : Set (Fin n))} =
      {ω | ∀ e ∈ graphEdges (internalGraph S), ω e = false} := by
    ext ω
    exact independent_iff_absent S ω
  rw [heq, absent_cylinder_mass, internalEdges_card]

lemma le_indepNum_iff {n a : ℕ} (G : SimpleGraph (Fin n)) :
    a ≤ G.indepNum ↔ ∃ S : Finset (Fin n), S.card = a ∧ G.IsIndepSet (S : Set (Fin n)) := by
  constructor
  · intro ha
    obtain ⟨T, hT⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq (hT.card_eq.symm ▸ ha)
    exact ⟨S, hS, hT.isIndepSet.mono (by exact_mod_cast hST)⟩
  · rintro ⟨S, rfl, hS⟩
    exact hS.card_le_indepNum

theorem independence_bound : Specs.P205.Probability.RandomGraphIndependence.IndependenceBound := by
  intro g n hg hn a
  let M := model g n hg hn
  let I := {S : Finset (Fin n) // S ∈ Finset.univ.powersetCard a}
  let A : I → Set (Outcome n) := fun S => {ω | (graph ω).IsIndepSet (S.val : Set (Fin n))}
  have heq : {ω : Outcome n | a ≤ (graph ω).indepNum} = ⋃ S : I, A S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A]
    constructor
    · intro ha
      obtain ⟨S, hcard, hS⟩ := (le_indepNum_iff _).mp ha
      exact ⟨⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩, hS⟩
    · rintro ⟨S, hS⟩
      exact (le_indepNum_iff _).mpr ⟨S.val, (Finset.mem_powersetCard.mp S.property).2, hS⟩
  have hmass (S : I) : M.measure.real (A S) = (1 - parameter g n) ^ a.choose 2 := by
    rw [Measure.real, FiniteModel.measureReal_eventMass]
    change (model g n hg hn).eventMass {ω | (graph ω).IsIndepSet (S.val : Set (Fin n))} = _
    rw [independent_set_probability, (Finset.mem_powersetCard.mp S.property).2]
  calc
    _ = M.measure.real (⋃ S : I, A S) := by
      rw [Measure.real, FiniteModel.measureReal_eventMass, ← heq]
    _ ≤ ∑ S : I, M.measure.real (A S) := union_bound _ A (fun _ => (A _).toFinite.measurableSet)
    _ = _ := by simp [hmass, I]

theorem exponential_bound : Specs.P205.Probability.RandomGraphIndependence.ExponentialBound := by
  intro g n hg hn a
  have hp := parameter_valid hg hn
  have hchoose : (n.choose a : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.choose_le_two_pow n a
  have hp_exp : (1 - parameter g n) ^ a.choose 2 ≤
      Real.exp (-parameter g n * (a.choose 2 : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by linarith [hp.2])
    have h := Real.add_one_le_exp (-parameter g n)
    linarith
  exact mul_le_mul hchoose hp_exp (pow_nonneg (by linarith [hp.2]) _) (by positivity)

lemma choose_threshold_lower {k n : ℕ} (hk : 1 ≤ k) (hn : 8 * k ≤ n) :
    (n : ℝ) ^ 2 / (64 * (k : ℝ) ^ 2) ≤ ((threshold k n).choose 2 : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hn' : 8 * (k : ℝ) ≤ n := by exact_mod_cast hn
  have ha : (n : ℝ) / (4 * (k : ℝ)) ≤ (threshold k n : ℝ) := Nat.le_ceil _
  have ha' : (n : ℝ) ≤ (threshold k n : ℝ) * (4 * (k : ℝ)) :=
    (div_le_iff₀ (by positivity)).mp ha
  have ha1 : (n : ℝ) / (8 * (k : ℝ)) ≤ (threshold k n : ℝ) - 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  calc
    _ = ((n : ℝ) / (4 * (k : ℝ))) * ((n : ℝ) / (8 * (k : ℝ))) / 2 := by
      field_simp
      ring
    _ ≤ (threshold k n : ℝ) * ((threshold k n : ℝ) - 1) / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul ha ha1 (by positivity) (by positivity)) (by norm_num)
    _ = _ := (Nat.cast_choose_two (K := ℝ) _).symm

theorem quantitative_exponent : Specs.P205.Probability.RandomGraphIndependence.QuantitativeExponent := by
  intro g k n hg hk hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 ≤ parameter g n := Real.rpow_nonneg hnpos.le _
  calc
    _ = parameter g n * ((n : ℝ) ^ 2 / (64 * (k : ℝ) ^ 2)) := by
      rw [← mul_div_assoc, parameter, ← Real.rpow_two (n : ℝ), ← Real.rpow_add hnpos]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (choose_threshold_lower hk hn) hp

open Filter in
lemma exponential_envelope_tendsto {d D : ℝ} (hd : 0 < d) (hD : 0 < D) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * Real.exp (-(n : ℝ) ^ (1 + d) / D))
      atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ d / D) atTop atTop :=
    ((tendsto_rpow_atTop hd).comp hn).atTop_div_const hD
  have hneg : Tendsto (fun n : ℕ => Real.log 2 - (n : ℝ) ^ d / D) atTop atBot := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      tendsto_atBot_add_const_left atTop (Real.log 2) (tendsto_neg_atTop_atBot.comp hpow)
  have hexp := Real.tendsto_exp_atBot.comp (hn.atTop_mul_atBot₀ hneg)
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  change Real.exp ((n : ℝ) * (Real.log 2 - (n : ℝ) ^ d / D)) = _
  have heq : (n : ℝ) * (Real.log 2 - (n : ℝ) ^ d / D) =
      (n : ℝ) * Real.log 2 + (-(n : ℝ) ^ (1 + d) / D) := by
    rw [Real.rpow_add hnpos, Real.rpow_one]
    ring
  rw [heq, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

open Filter in
theorem upper_bound_tends_to_zero : Specs.P205.Probability.RandomGraphIndependence.UpperBoundTendsToZero := by
  intro g k hg hk
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  apply squeeze_zero' (Eventually.of_forall (fun n => by unfold upperBound; positivity))
    (g := fun n : ℕ => (2 : ℝ) ^ n *
      Real.exp (-(n : ℝ) ^ (1 + 1 / (2 * (g : ℝ))) / (64 * (k : ℝ) ^ 2)))
  · filter_upwards [eventually_ge_atTop (8 * k)] with n hn
    unfold upperBound
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have h := quantitative_exponent g k n hg hk hn
    simpa only [neg_mul, neg_div] using neg_le_neg h
  · exact exponential_envelope_tendsto (by positivity) (by positivity)

open Filter in
theorem simultaneous_existence : Specs.P205.Probability.RandomGraphIndependence.SimultaneousExistence := by
  intro g k hg hk
  have hC : Tendsto (fun n : ℕ => 2 * (g : ℝ) / Real.sqrt (n : ℝ)) atTop (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop _
  have hU := upper_bound_tends_to_zero g k hg hk
  have hlim : Tendsto (fun n : ℕ => 2 * (g : ℝ) / Real.sqrt (n : ℝ) + upperBound g k n)
      atTop (nhds 0) := by simpa only [zero_add] using hC.add hU
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hsmall⟩ := ((eventually_ge_atTop 1).and hsmall).exists
  let M := model g n hg hn
  let bad : Bool → Set (Outcome n) := fun b => if b then
    {ω | threshold k n ≤ (graph ω).indepNum} else {ω | (n : ℝ) / 2 ≤ count g n ω}
  have hInd : M.eventMass {ω | threshold k n ≤ (graph ω).indepNum} ≤ upperBound g k n :=
    (independence_bound g n hg hn _).trans (exponential_bound g n hg hn _)
  have hsum : (∑ b : Bool, M.measure.real (bad b)) < 1 := by
    calc
      _ = M.eventMass {ω | threshold k n ≤ (graph ω).indepNum} +
          M.eventMass {ω | (n : ℝ) / 2 ≤ count g n ω} := by
            simp [bad, Measure.real, FiniteModel.measureReal_eventMass]
      _ ≤ upperBound g k n + 2 * (g : ℝ) / Real.sqrt n :=
        add_le_add hInd (short_cycle_tail g n hg hn)
      _ < 1 := by linarith
  obtain ⟨ω, hω⟩ := exists_avoiding M.measure bad (fun _ => (bad _).toFinite.measurableSet) hsum
  refine ⟨n, hn, ω, ?_, ?_⟩
  · have := hω false
    simpa [bad] using this
  · have := hω true
    simpa [bad] using this

theorem good_graph_exists : Specs.P205.Probability.RandomGraphIndependence.GoodGraphExists := by
  intro g k hg hk
  obtain ⟨n, hn, ω, hC, hI⟩ := simultaneous_existence g k hg hk
  refine ⟨n, graph ω, hn, ?_, hI⟩
  rw [← count_meaning g n ω]
  exact hC

end P205.Probability.RandomGraphIndependence
