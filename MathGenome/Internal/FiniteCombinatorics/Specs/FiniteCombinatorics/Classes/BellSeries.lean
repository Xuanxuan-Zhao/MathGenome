import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingSecond
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Basic

/-! Independent specification of the block-marking and Bell assertions of
`paper.tex`, p204:W22. The coefficient variable of `Polynomial ℚ` is the block
marker u; the outer `PowerSeries` variable is the label marker z. Exponentials
are the canonical formal exponential, composed only at zero-constant series.
Partitions below are literal unordered nonempty blocks covering the label set.
-/
noncomputable section
open scoped BigOperators
namespace Specs.FiniteCombinatorics.Classes.BellSeries

def bellValue (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k
def bellType := ℕ → ℕ
def blockPolynomialValue (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (Nat.stirlingSecond n k : ℚ) * Polynomial.X ^ k
def blockPolynomialType := ℕ → Polynomial ℚ

def FixedCounting : Prop := ∀ (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ),
  Nat.card {P : Finpartition (Finset.univ : Finset α) // P.parts.card = k} =
    Nat.stirlingSecond (Fintype.card α) k
def MarkedCounting : Prop := ∀ (α : Type*) [Fintype α] [DecidableEq α],
  (∑ P : Finpartition (Finset.univ : Finset α), (Polynomial.X : Polynomial ℚ) ^ P.parts.card) =
    blockPolynomialValue (Fintype.card α)
def BellCounting : Prop := ∀ (α : Type*) [Fintype α],
  Nat.card (Setoid.Partitions α) = bellValue (Fintype.card α)
def BivariateEGF : Prop :=
  (PowerSeries.exp (Polynomial ℚ)).subst
    (PowerSeries.C Polynomial.X * (PowerSeries.exp (Polynomial ℚ) - 1)) =
      Series.egfValue blockPolynomialValue
def BellEGF : Prop :=
  Series.egfValue (fun n => (bellValue n : ℚ)) =
    (PowerSeries.exp ℚ).subst (PowerSeries.exp ℚ - 1)
def EmptyCounts : Prop := bellValue 0 = 1 ∧ blockPolynomialValue 0 = 1
def FormalConditions : Prop :=
  PowerSeries.constantCoeff (PowerSeries.exp ℚ - 1) = 0 ∧
  PowerSeries.HasSubst (PowerSeries.exp ℚ - 1) ∧
  PowerSeries.constantCoeff
    (PowerSeries.C Polynomial.X * (PowerSeries.exp (Polynomial ℚ) - 1)) = 0 ∧
  PowerSeries.HasSubst
    (PowerSeries.C Polynomial.X * (PowerSeries.exp (Polynomial ℚ) - 1))

end Specs.FiniteCombinatorics.Classes.BellSeries
