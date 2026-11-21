import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.FiniteModels
import Mathlib.Data.Finset.Card

/-! Independent statements for the finite alteration principle, paper.tex
828–850 (Theorem 4.4). Repairs are specified functions on positive support;
their correctness must be supplied by the application. -/

namespace P205.Probability.AlterationSpec

/-- Zero-weight outcomes need not satisfy the weighted-mean bound. -/
def weightedMeanWitness : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (Z : Ω → ℝ),
    ∃ ω, ω ∈ M.positiveSupport ∧ M.expectation Z ≤ Z ω

/-- Abstract finite objects are represented by their type and natural-valued
size. The stated size guarantee is precisely the one in Theorem 4.4.
This stronger form needs only that guarantee and defect clearance; the
finite-set version below derives the guarantee from actual deletion data. -/
def finiteAlteration : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (S D : Ω → ℕ)
    {Object : Type*} (size : Object → ℕ) (defectFree : Object → Prop)
    (repair : M.positiveSupport → Object),
    (∀ ω, defectFree (repair ω)) →
    (∀ ω, (S ω.val : ℝ) - (D ω.val : ℝ) ≤ (size (repair ω) : ℝ)) →
    ∃ ω : M.positiveSupport, defectFree (repair ω) ∧
      M.expectation (fun v => (S v : ℝ) - (D v : ℝ)) ≤ (size (repair ω) : ℝ)

/-- Concrete deletion interface: the repaired set is a subset of the sample,
at most D original items are removed, and the application proves clearance. -/
def finiteSetAlteration : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω)
    {α : Type*} [DecidableEq α] (sample : Ω → Finset α) (D : Ω → ℕ)
    (defectFree : Finset α → Prop) (repair : M.positiveSupport → Finset α),
    (∀ ω, repair ω ⊆ sample ω.val) →
    (∀ ω, ((sample ω.val) \ repair ω).card ≤ D ω.val) →
    (∀ ω, defectFree (repair ω)) →
    ∃ ω : M.positiveSupport, defectFree (repair ω) ∧
      M.expectation (fun v => ((sample v).card : ℝ) - (D v : ℝ)) ≤
        ((repair ω).card : ℝ)

end P205.Probability.AlterationSpec
