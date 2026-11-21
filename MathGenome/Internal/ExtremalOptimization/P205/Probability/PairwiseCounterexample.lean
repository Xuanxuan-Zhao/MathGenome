import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.PairwiseCounterexample
import MathGenome.Internal.ExtremalOptimization.P205.Probability.FiniteModels
import MathGenome.Internal.ExtremalOptimization.P205.Probability.DependencyGraph
import Mathlib.Tactic.FinCases

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

noncomputable section

namespace P205.Probability.PairwiseCounterexample

-- Match the classical finite-function enumeration in `FiniteModel.pi`.
local instance : DecidableEq (Fin 2) := Classical.decEq _

private theorem sum_outcomes (f : Outcome → ℝ) :
    ∑ ω, f ω = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  classical
  calc
    ∑ ω, f ω = ∑ p : Bit × Bit, f ![p.1, p.2] :=
      Fintype.sum_equiv (finTwoArrowEquiv Bit) _ _ (by
        intro ω
        congr 1
        ext i
        fin_cases i <;> rfl)
    _ = _ := by simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc]

private theorem measure_formula (S : Set Outcome) :
    μ S = ENNReal.ofReal (experiment.eventMass S) :=
  FiniteModel.measure_eventMass experiment S

private theorem mass_A : experiment.eventMass A = 1 / 2 := by
  norm_num [FiniteModel.eventMass, sum_outcomes, experiment, FiniteModel.pi,
    Fin.prod_univ_two, fairBit, A, U, Set.indicator]

private theorem mass_B : experiment.eventMass B = 1 / 2 := by
  norm_num [FiniteModel.eventMass, sum_outcomes, experiment, FiniteModel.pi,
    Fin.prod_univ_two, fairBit, B, V, Set.indicator]

private theorem mass_C : experiment.eventMass C = 1 / 2 := by
  norm_num [FiniteModel.eventMass, sum_outcomes, experiment, FiniteModel.pi,
    Fin.prod_univ_two, fairBit, C, U, V, Set.indicator]

private theorem mass_pairs (i j : Fin 3) (h : i ≠ j) :
    experiment.eventMass (events i ∩ events j) = 1 / 4 := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (h rfl).elim
    | norm_num [events, FiniteModel.eventMass, sum_outcomes, experiment, FiniteModel.pi,
        Fin.prod_univ_two, fairBit, A, B, C, U, V, Set.indicator]

private theorem mass_triple : experiment.eventMass (C ∩ (A ∩ B)) = 1 / 4 := by
  norm_num [FiniteModel.eventMass, sum_outcomes, experiment, FiniteModel.pi,
    Fin.prod_univ_two, fairBit, A, B, C, U, V, Set.indicator]

/-- The coordinates of the product are independent, and both are fair. -/
theorem fair_independent_bits : PairwiseCounterexampleSpec.fairIndependentBits := by
  constructor
  · intro b
    constructor
    · rw [measure_formula]
      fin_cases b <;> norm_num [FiniteModel.eventMass, sum_outcomes, experiment,
        FiniteModel.pi, Fin.prod_univ_two, fairBit, U, Set.indicator]
    · rw [measure_formula]
      fin_cases b <;> norm_num [FiniteModel.eventMass, sum_outcomes, experiment,
        FiniteModel.pi, Fin.prod_univ_two, fairBit, V, Set.indicator]
  · exact (FiniteModel.independent_coordinates (fun _ : Fin 2 => fairBit)).indepFun
      (show (0 : Fin 2) ≠ 1 by intro h; have := congrArg Fin.val h; norm_num at this)

/-- Each event has mass one half, and distinct pairs have mass one quarter. -/
theorem probabilities : PairwiseCounterexampleSpec.probabilities := by
  constructor
  · intro i
    fin_cases i <;>
      simp [events, measure_formula, mass_A, mass_B, mass_C]
  · intro i j h
    rw [measure_formula, mass_pairs i j h]

/-- These probability identities give actual independence of each distinct pair. -/
theorem pairwise_independent : PairwiseCounterexampleSpec.pairwiseIndependent := by
  intro i j h
  apply (indepSet_iff_measure_inter_eq_mul
    (FiniteModel.all_measurable _) (FiniteModel.all_measurable _) μ).2
  rw [probabilities.2 i j h, probabilities.1 i, probabilities.1 j,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  norm_num

/-- Intersections of the two generators are in their generated sigma-algebra. -/
theorem intersection_generated : PairwiseCounterexampleSpec.intersectionGenerated := by
  exact (MeasurableSpace.measurableSet_generateFrom (by simp : A ∈ ({A, B} : Set _))).inter
    (MeasurableSpace.measurableSet_generateFrom (by simp : B ∈ ({A, B} : Set _)))

/-- The joint nonneighbor event contradicts the independence equation for C. -/
theorem obstruction : PairwiseCounterexampleSpec.obstruction := by
  have hC : μ C = ENNReal.ofReal (1 / 2 : ℝ) := by simpa [events] using probabilities.1 2
  have hAB : μ (A ∩ B) = ENNReal.ofReal (1 / 4 : ℝ) := by
    simpa [events] using probabilities.2 0 1 (by decide)
  have hABC : μ (C ∩ (A ∩ B)) = ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [measure_formula, mass_triple]
  refine ⟨hABC, ?_, ?_⟩
  · rw [hC, hAB, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    norm_num
  · rw [hABC, hC, hAB, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    intro h
    have ht := congrArg ENNReal.toReal h
    norm_num at ht

/-- Pairwise independence does not make the graph with no edges a dependency graph. -/
theorem not_dependency_graph :
    ¬ IsDependencyGraph μ events (⊥ : SimpleGraph (Fin 3)) := by
  intro h
  have hgen : MeasurableSet[MeasurableSpace.generateFrom
      (events '' {j : Fin 3 | j ≠ 2 ∧ ¬ (⊥ : SimpleGraph (Fin 3)).Adj 2 j})]
      (A ∩ B) := by
    apply MeasurableSet.inter
    · apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨0, ⟨by decide, by simp⟩, rfl⟩
    · apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨1, ⟨by decide, by simp⟩, rfl⟩
  have heq := h.2 2 (A ∩ B) hgen
  exact obstruction.2.2 (by simpa [events] using heq)

end P205.Probability.PairwiseCounterexample

end
