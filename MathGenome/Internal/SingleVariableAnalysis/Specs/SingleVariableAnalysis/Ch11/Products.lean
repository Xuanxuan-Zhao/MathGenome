import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction

/-!
Independent specification of K03.11.products, paper.tex:1139–1148.
All products are ordered, with indices 0,…,N. A convergent product has
nonzero factors and a nonzero finite limit. The logarithmic series uses the
ordinary partial-sum predicate, allowing conditional convergence.
A prefix of length m has indices 0,…,m-1; m=0 is permitted.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch11.Products
open scoped BigOperators
open Ch01.SequenceLimit Ch11.PartialSums Ch07.LogConstruction Ch07.ExpConstruction

def realPartialProductType : Type := (ℕ → ℝ) → ℕ → ℝ
def realPartialProductValue : realPartialProductType :=
  fun v N => ∏ n ∈ Finset.range (N + 1), v n

def realProductHasLimitType : Type := (ℕ → ℝ) → ℝ → Prop
def realProductHasLimitValue : realProductHasLimitType :=
  fun v P => (∀ n, v n ≠ 0) ∧ P ≠ 0 ∧ realSequenceConvergesValue (realPartialProductValue v) P

def realProductConvergesType : Type := (ℕ → ℝ) → Prop
def realProductConvergesValue : realProductConvergesType :=
  fun v => ∃ P : ℝ, realProductHasLimitValue v P

def realProductNecessary : Prop :=
  ∀ (v : ℕ → ℝ) (P : ℝ), realProductHasLimitValue v P →
    realSequenceConvergesValue v 1

def realProductPrefixIff : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, v n ≠ 0) → ∀ (m : ℕ) (Q : ℝ),
    realProductHasLimitValue (fun n => v (n + m)) Q ↔
      realProductHasLimitValue v ((∏ n ∈ Finset.range m, v n) * Q)

def realProductTailConvergesIff : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, v n ≠ 0) → ∀ m : ℕ,
    realProductConvergesValue (fun n => v (n + m)) ↔ realProductConvergesValue v

def realProductFiniteChangesIff : Prop :=
  ∀ (v w : ℕ → ℝ), (∀ n, v n ≠ 0) → (∀ n, w n ≠ 0) →
    ∀ m : ℕ, (∀ n, m ≤ n → v n = w n) →
      (realProductConvergesValue v ↔ realProductConvergesValue w)

def realProductZeroFactorExcluded : Prop :=
  ∀ (v : ℕ → ℝ) (n : ℕ), v n = 0 → ¬ realProductConvergesValue v

def realProductZeroLimitExcluded : Prop :=
  ∀ v : ℕ → ℝ, realSequenceConvergesValue (realPartialProductValue v) 0 →
    ¬ realProductConvergesValue v

def realHalfProductFormula : Prop :=
  ∀ N : ℕ, realPartialProductValue (fun _ => (1 / 2 : ℝ)) N = (1 / 2 : ℝ) ^ (N + 1)

def realHalfProductCounterexample : Prop :=
  (∀ n : ℕ, (fun _ : ℕ => (1 / 2 : ℝ)) n ≠ 0) ∧
    realSequenceConvergesValue (realPartialProductValue (fun _ => (1 / 2 : ℝ))) 0 ∧
    ¬ realProductConvergesValue (fun _ => (1 / 2 : ℝ))

def complexPartialProductType : Type := (ℕ → ℂ) → ℕ → ℂ
def complexPartialProductValue : complexPartialProductType :=
  fun v N => ∏ n ∈ Finset.range (N + 1), v n

def complexProductHasLimitType : Type := (ℕ → ℂ) → ℂ → Prop
def complexProductHasLimitValue : complexProductHasLimitType :=
  fun v P => (∀ n, v n ≠ 0) ∧ P ≠ 0 ∧ complexSequenceConvergesValue (complexPartialProductValue v) P

def complexProductConvergesType : Type := (ℕ → ℂ) → Prop
def complexProductConvergesValue : complexProductConvergesType :=
  fun v => ∃ P : ℂ, complexProductHasLimitValue v P

def complexProductNecessary : Prop :=
  ∀ (v : ℕ → ℂ) (P : ℂ), complexProductHasLimitValue v P →
    complexSequenceConvergesValue v 1

def complexProductPrefixIff : Prop :=
  ∀ (v : ℕ → ℂ), (∀ n, v n ≠ 0) → ∀ (m : ℕ) (Q : ℂ),
    complexProductHasLimitValue (fun n => v (n + m)) Q ↔
      complexProductHasLimitValue v ((∏ n ∈ Finset.range m, v n) * Q)

def complexProductTailConvergesIff : Prop :=
  ∀ (v : ℕ → ℂ), (∀ n, v n ≠ 0) → ∀ m : ℕ,
    complexProductConvergesValue (fun n => v (n + m)) ↔ complexProductConvergesValue v

def complexProductFiniteChangesIff : Prop :=
  ∀ (v w : ℕ → ℂ), (∀ n, v n ≠ 0) → (∀ n, w n ≠ 0) →
    ∀ m : ℕ, (∀ n, m ≤ n → v n = w n) →
      (complexProductConvergesValue v ↔ complexProductConvergesValue w)

def complexProductZeroFactorExcluded : Prop :=
  ∀ (v : ℕ → ℂ) (n : ℕ), v n = 0 → ¬ complexProductConvergesValue v

def complexProductZeroLimitExcluded : Prop :=
  ∀ v : ℕ → ℂ, complexSequenceConvergesValue (complexPartialProductValue v) 0 →
    ¬ complexProductConvergesValue v

def complexHalfProductFormula : Prop :=
  ∀ N : ℕ, complexPartialProductValue (fun _ => (1 / 2 : ℂ)) N = (1 / 2 : ℂ) ^ (N + 1)

def complexHalfProductCounterexample : Prop :=
  (∀ n : ℕ, (fun _ : ℕ => (1 / 2 : ℂ)) n ≠ 0) ∧
    complexSequenceConvergesValue (complexPartialProductValue (fun _ => (1 / 2 : ℂ))) 0 ∧
    ¬ complexProductConvergesValue (fun _ => (1 / 2 : ℂ))

def positiveProductLimitPositive : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) → ∀ P : ℝ,
    realProductHasLimitValue v P → 0 < P

def logPartialProduct : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) → ∀ N : ℕ,
    seriesLogValue (realPartialProductValue v N) =
      realPartialSumValue (fun n => seriesLogValue (v n)) N

def expLogPartialSum : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) → ∀ N : ℕ,
    realPartialProductValue v N =
      realSeriesExpValue (realPartialSumValue (fun n => seriesLogValue (v n)) N)

def productLogLimitIff : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) → ∀ P : ℝ, 0 < P →
    (realProductHasLimitValue v P ↔
      realSeriesHasSumValue (fun n => seriesLogValue (v n)) (seriesLogValue P))

def productOfLogSum : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) → ∀ S : ℝ,
    realSeriesHasSumValue (fun n => seriesLogValue (v n)) S →
      realProductHasLimitValue v (realSeriesExpValue S)

def positiveProductIffLogSeries : Prop :=
  ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) →
    (realProductConvergesValue v ↔ realSeriesConvergesValue (fun n => seriesLogValue (v n)))

end Specs.SingleVariableAnalysis.Ch11.Products
