import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.NormNum

/-! Canonical four-outcome model for paper.tex:544–553. The two coordinates
are encoded by booleans and decoded as the real signs -1 and 1. All laws below
are on the real line with its Borel sigma algebra. -/
open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityFoundations.Ch02.Signs

abbrev Ω := Bool × Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

def U (ω : Ω) : ℝ := sign ω.1
def V (ω : Ω) : ℝ := sign ω.2
def W (ω : Ω) : ℝ := U ω * V ω

def X (i : Fin 3) (ω : Ω) : ℝ := ![U ω, V ω, W ω] i

/-- Each of the four sign pairs has mass 1/4. -/
noncomputable def P : Measure Ω :=
  ((1 / 4 : ℝ≥0) : ℝ≥0∞) • (Measure.dirac (false, false) + Measure.dirac (false, true) +
    Measure.dirac (true, false) + Measure.dirac (true, true))

/-- The uniform law on the actual real signs {-1,1}. -/
noncomputable def uniformSign : Measure ℝ :=
  ((1 / 2 : ℝ≥0) : ℝ≥0∞) • (Measure.dirac (-1) + Measure.dirac 1)

/-- The uniform law on the four ordered pairs of real signs. -/
noncomputable def uniformPair : Measure (ℝ × ℝ) := uniformSign.prod uniformSign

instance : IsProbabilityMeasure P := by
  constructor
  simp only [P, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul, mul_one]
  exact_mod_cast (by norm_num : (1 / 4 : ℝ≥0) * (1 + 1 + 1 + 1) = 1)

end ProbabilityFoundations.Ch02.Signs

namespace Specs.ProbabilityFoundations.Ch02.PairwiseSignsCounterexample
open ProbabilityFoundations.Ch02.Signs

/-- Full counterexample: measurable signs, specified marginal and pair laws,
pairwise independence, the deterministic and a.s. product identity, integrable
zero-mean coordinates, product expectation one, and failure both of mutual
independence and of the three-factor expectation identity. -/
def counterexampleType : Prop :=
  (∀ i, Measurable (X i)) ∧
  (∀ i ω, X i ω ∈ ({-1, 1} : Set ℝ)) ∧
  (∀ i, Measure.map (X i) P = uniformSign) ∧
  (∀ i j, i ≠ j → Measure.map (fun ω => (X i ω, X j ω)) P = uniformPair) ∧
  IndependenceInterfaces.PairwiseIndependentRandomElementsValue P X ∧
  (∀ ω, W ω = U ω * V ω) ∧
  (∀ ω, U ω * V ω * W ω = 1) ∧
  (∀ᵐ ω ∂P, U ω * V ω * W ω = 1) ∧
  (∀ i, Integrable (X i) P) ∧
  (∀ i, (∫ ω, X i ω ∂P) = 0) ∧
  Integrable (fun ω => U ω * V ω * W ω) P ∧
  (∫ ω, U ω * V ω * W ω ∂P) = 1 ∧
  ¬ IndependenceInterfaces.IndependentRandomElementsValue P X ∧
  (∫ ω, U ω * V ω * W ω ∂P) ≠
    (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P) * (∫ ω, W ω ∂P)

end Specs.ProbabilityFoundations.Ch02.PairwiseSignsCounterexample
