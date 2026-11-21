import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.NumberTheory.Real.Irrational

/-! Independent specification for K03.08.dirichlet (paper.tex:2250–2260).
The function is the rational indicator on [0,1], extended by zero outside.
The discontinuity assertion uses the relative domain, including its endpoints.
The sums and integrability predicate are the shared Darboux definitions.
-/
namespace Specs.SingleVariableAnalysis.Ch08.Dirichlet
open _root_.SingleVariableAnalysis.Riemann
open DarbouxSums Integral

abbrev dirichletType := ℝ → ℝ

noncomputable def dirichletValue : dirichletType := by
  classical
  exact fun x => if x ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x then 1 else 0

def rationalDensity : Prop := ∀ a b : ℝ, a < b →
  ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b

def irrationalDensity : Prop := ∀ a b : ℝ, a < b →
  ∃ x : ℝ, Irrational x ∧ a < x ∧ x < b

def bounded : Prop := boundedOnIntervalValue dirichletValue 0 1

def intervalBounds : Prop := ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
  sSup (dirichletValue '' Set.Icc a b) = 1 ∧
  sInf (dirichletValue '' Set.Icc a b) = 0

def cellBounds : Prop := ∀ (P : PartitionData 0 1)
  (hf : boundedOnIntervalValue dirichletValue 0 1) (i : Fin P.n),
  cellSupremumValue dirichletValue P hf i = 1 ∧
  cellInfimumValue dirichletValue P hf i = 0

def partitionSums : Prop := ∀ (P : PartitionData 0 1)
  (hf : boundedOnIntervalValue dirichletValue 0 1),
  upperSumValue dirichletValue P hf = 1 ∧ lowerSumValue dirichletValue P hf = 0

def integralBounds : Prop := ∀ (hf : boundedOnIntervalValue dirichletValue 0 1),
  lowerIntegralValue dirichletValue (by norm_num : (0 : ℝ) ≤ 1) hf = 0 ∧
  upperIntegralValue dirichletValue (by norm_num : (0 : ℝ) ≤ 1) hf = 1

def notIntegrable : Prop := ¬ realIntegrableValue dirichletValue 0 1

def discontinuousEverywhere : Prop := ∀ x ∈ Set.Icc (0 : ℝ) 1,
  ¬ ContinuousWithinAt dirichletValue (Set.Icc (0 : ℝ) 1) x

end Specs.SingleVariableAnalysis.Ch08.Dirichlet
