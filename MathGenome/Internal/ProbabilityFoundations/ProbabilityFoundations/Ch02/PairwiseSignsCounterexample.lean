import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceJointLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.PairwiseSignsCounterexample
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityFoundations.Ch02.Signs

-- The domain is a finite discrete measurable space.
theorem measurable_X (i : Fin 3) : Measurable (X i) := by
  exact measurable_of_countable _

private theorem map_P {T : Type*} [MeasurableSpace T] (f : Ω → T) :
    Measure.map f P = ((1 / 4 : ℝ≥0) : ℝ≥0∞) •
      (Measure.dirac (f (false, false)) + Measure.dirac (f (false, true)) +
       Measure.dirac (f (true, false)) + Measure.dirac (f (true, true))) := by
  have hf : Measurable f := measurable_of_countable f
  simp [P, Measure.map_smul _ hf.aemeasurable, Measure.map_add _ _ hf,
    Measure.map_dirac' hf]

theorem range_X (i : Fin 3) (ω : Ω) : X i ω ∈ ({-1, 1} : Set ℝ) := by
  rcases ω with ⟨a, b⟩
  fin_cases i <;> cases a <;> cases b <;> norm_num [X, U, V, W, sign]

theorem product_eq_one (ω : Ω) : U ω * V ω * W ω = 1 := by
  rcases ω with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [U, V, W, sign]

private theorem uniformPair_expansion : uniformPair =
    ((1 / 4 : ℝ≥0) : ℝ≥0∞) •
      (Measure.dirac (-1, -1) + Measure.dirac (-1, 1) +
       Measure.dirac (1, -1) + Measure.dirac (1, 1)) := by
  simp only [uniformPair, uniformSign, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.add_prod, Measure.prod_add, Measure.dirac_prod_dirac, smul_add, smul_smul]
  have hquarter : (((1 / 2 : ℝ≥0) : ℝ≥0∞) * ((1 / 2 : ℝ≥0) : ℝ≥0∞)) =
      ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (by norm_num : (1 / 2 : ℝ≥0) * (1 / 2) = 1 / 4)
  rw [hquarter]
  ac_rfl

theorem pair_law (i j : Fin 3) (hij : i ≠ j) :
    Measure.map (fun ω => (X i ω, X j ω)) P = uniformPair := by
  rw [map_P, uniformPair_expansion]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [X, U, V, W, sign] <;> abel

private theorem quarter_add_quarter :
    ((1 / 4 : ℝ≥0) : ℝ≥0∞) + ((1 / 4 : ℝ≥0) : ℝ≥0∞) =
      ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  exact_mod_cast (by norm_num : (1 / 4 : ℝ≥0) + 1 / 4 = 1 / 2)

theorem marginal_law (i : Fin 3) : Measure.map (X i) P = uniformSign := by
  rw [map_P]
  have hgroup (a b : Measure ℝ) :
      ((1 / 4 : ℝ≥0) : ℝ≥0∞) • (a + b + a + b) =
      ((1 / 2 : ℝ≥0) : ℝ≥0∞) • (a + b) := by
    rw [show a + b + a + b = (a + b) + (a + b) by ac_rfl,
      smul_add, ← add_smul, quarter_add_quarter]
  fin_cases i
  all_goals
    dsimp [X, U, V, W, sign]
    norm_num only [neg_one_mul, one_mul, neg_neg]
    unfold uniformSign
    convert hgroup (Measure.dirac (-1)) (Measure.dirac 1) using 1 <;> congr 1 <;> abel

private theorem integrable_P (f : Ω → ℝ) : Integrable f P := by
  unfold P
  apply Integrable.smul_measure _ (by simp)
  simp only [integrable_add_measure]
  exact ⟨⟨⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩,
    integrable_dirac (by simp)⟩, integrable_dirac (by simp)⟩

private theorem integral_P (f : Ω → ℝ) :
    (∫ ω, f ω ∂P) = (1 / 4 : ℝ) *
      (f (false, false) + f (false, true) + f (true, false) + f (true, true)) := by
  have hd (ω : Ω) : Integrable f (Measure.dirac ω) := integrable_dirac (by simp)
  unfold P
  rw [integral_smul_measure]
  rw [integral_add_measure (((hd _).add_measure (hd _)).add_measure (hd _)) (hd _),
    integral_add_measure ((hd _).add_measure (hd _)) (hd _),
    integral_add_measure (hd _) (hd _)]
  simp

theorem expectation_X (i : Fin 3) : (∫ ω, X i ω ∂P) = 0 := by
  rw [integral_P]
  fin_cases i <;> norm_num [X, U, V, W, sign]

/-- All three real signs are pairwise independent in the common interface. -/
theorem pairwise_independent : PairwiseIndependentRandomElements P X := by
  apply (pairwiseIndependentRandomElements_iff P X).mpr
  intro i j hij
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_X i).aemeasurable (measurable_X j).aemeasurable).mpr
  rw [pair_law i j hij, marginal_law i, marginal_law j]
  rfl

theorem expectation_product : (∫ ω, U ω * V ω * W ω ∂P) = 1 := by
  simp only [product_eq_one]
  simp

/-- Mutual independence would force the three-factor identity, contradicting
one for the product expectation and zero for every individual expectation. -/
theorem not_mutually_independent : ¬ IndependentRandomElements P X := by
  intro h
  have hi := (independentRandomElements_iff_iIndepFun P X).mp h
  have he := hi.integral_fun_prod_eq_prod_integral
    (fun i => (measurable_X i).aestronglyMeasurable)
  simp only [Fin.prod_univ_three, expectation_X, zero_mul] at he
  change (∫ ω, U ω * V ω * W ω ∂P) = 0 at he
  rw [expectation_product] at he
  norm_num at he

/-- Example 2.3: the complete finite probability counterexample. -/
theorem counterexample :
    Specs.ProbabilityFoundations.Ch02.PairwiseSignsCounterexample.counterexampleType := by
  refine ⟨measurable_X, range_X, marginal_law, pair_law, pairwise_independent,
    (fun _ => rfl), product_eq_one, Filter.Eventually.of_forall product_eq_one,
    (fun i => integrable_P (X i)), expectation_X, integrable_P _, expectation_product,
    not_mutually_independent, ?_⟩
  have hU := expectation_X 0
  have hV := expectation_X 1
  have hW := expectation_X 2
  change (∫ ω, U ω ∂P) = 0 at hU
  change (∫ ω, V ω ∂P) = 0 at hV
  change (∫ ω, W ω ∂P) = 0 at hW
  rw [expectation_product, hU, hV, hW]
  norm_num

end ProbabilityFoundations.Ch02.Signs
