import Mathlib.MeasureTheory.Measure.Prod
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueCompletion

/-! Euclidean products and their completions, paper.tex:2790–2831.
`coordinates` is the canonical split into the first m and last n coordinates.
All space equalities below are literal equalities after pullback by its inverse.
The ordinary product of completed factors is kept separate from its completion.
The subsequent counterexample is allocated to the separate sections-failure goal. -/

noncomputable section
open Set MeasureTheory
open D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch02.Completion

namespace D11.Ch08.EuclideanProductCompletion

abbrev coordinates (m n : ℕ) : Point (m + n) ≃L[ℝ] Point m × Point n :=
  EuclideanSpace.finAddEquivProd

end D11.Ch08.EuclideanProductCompletion

namespace Specs.D11.Ch08.EuclideanProductCompletion
open _root_.D11.Ch08.EuclideanProductCompletion

abbrev borelProduct (m n : ℕ) [NeZero m] [NeZero n] :=
  (borelMeasure_value m).prod (borelMeasure_value n)

abbrev factorSpace (m n : ℕ) [NeZero m] [NeZero n] :=
  (lebesgueSpace_value m).prod (lebesgueSpace_value n)

abbrev factorProduct (m n : ℕ) [NeZero m] [NeZero n] :
    @Measure (Point m × Point n) (factorSpace m n) :=
  @Measure.prod (Point m) (Point n) (lebesgueSpace_value m) (lebesgueSpace_value n)
    (lebesgue_value m) (lebesgue_value n)

/-- The Borel product is the joint Borel sigma-algebra under concatenation. -/
def borel_sigma : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n],
  (borel (Point m)).prod (borel (Point n)) =
    (borel (Point (m + n))).comap (coordinates m n).symm

/-- Equality of measures on the whole joint Borel space. -/
def borel_measure : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n],
  (borelProduct m n).map (coordinates m n).symm = borelMeasure_value (m + n)

def borel_completion_space : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n],
  completedSpace_value (borelProduct m n) =
    (lebesgueSpace_value (m + n)).comap (coordinates m n).symm

def borel_completion_value : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n]
  (E : Set (Point m × Point n)),
  MeasurableSet[completedSpace_value (borelProduct m n)] E →
    completedMeasure_value (borelProduct m n) E =
      lebesgue_value (m + n) ((coordinates m n).symm '' E)

def factor_product_inclusions : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n],
  (borel (Point m)).prod (borel (Point n)) ≤ factorSpace m n ∧
    factorSpace m n ≤ (lebesgueSpace_value (m + n)).comap (coordinates m n).symm

/-- The joint completed measure restricts to the ordinary product of the
completed factor measures, on every set of that product sigma-algebra. -/
def factor_product_restriction : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n]
  (E : Set (Point m × Point n)), MeasurableSet[factorSpace m n] E →
    factorProduct m n E = lebesgue_value (m + n) ((coordinates m n).symm '' E)

def factor_completion_space : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n],
  completedSpace_value (m := factorSpace m n) (factorProduct m n) =
    (lebesgueSpace_value (m + n)).comap (coordinates m n).symm

def factor_completion_value : Prop := ∀ (m n : ℕ) [NeZero m] [NeZero n]
  (E : Set (Point m × Point n)),
  MeasurableSet[completedSpace_value (m := factorSpace m n) (factorProduct m n)] E →
    completedMeasure_value (m := factorSpace m n) (factorProduct m n) E =
      lebesgue_value (m + n) ((coordinates m n).symm '' E)

end Specs.D11.Ch08.EuclideanProductCompletion
