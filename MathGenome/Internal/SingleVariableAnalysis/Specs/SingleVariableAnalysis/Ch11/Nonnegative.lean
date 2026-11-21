import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Independent specification of K03.11.nonnegative, paper.tex:995–1001.
The ordered real sums use the upstream inclusive indexing 0,...,N.
The extended sum takes values in the nonnegative half of the extended real
line, `ℝ≥0∞`; `∞` means +∞. Nonnegativity makes `ofReal` an exact embedding
on every term and finite sum. No claim is made for signed series here.

The family definition also applies to a block, whose index set is a subtype
of ℕ. The finite-subset formula applies to these families as well. The
partition theorem permits finite and countable blocks, infinite block sums,
and any finite or countable collection of blocks (indeed any index type).
Disjointness and coverage are explicit; no summability is assumed.
-/

namespace Specs.SingleVariableAnalysis.Ch11.Nonnegative

open scoped BigOperators Topology ENNReal
open PartialSums
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

universe u v

def nonnegativeExtendedSumType : Type (u + 1) := {ι : Type u} → (ι → ℝ) → ℝ≥0∞
noncomputable def nonnegativeExtendedSumValue : nonnegativeExtendedSumType :=
  fun a => ∑' i, ENNReal.ofReal (a i)

def nonnegativePartialSumsMonotone : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) → Monotone (realPartialSumValue a)

def nonnegativeSeriesConvergesIff : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
    (realSeriesConvergesValue a ↔ BddAbove (Set.range (realPartialSumValue a)))

def nonnegativeSeriesHasSumSupremum : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
    ∀ hb : BddAbove (Set.range (realPartialSumValue a)),
      realSeriesHasSumValue a
        (Ch01.SupInf.realSupremumValue (Set.range (realPartialSumValue a))
          (Set.range_nonempty _) hb)

def nonnegativeSeriesDivergesToPosInfinity : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) → ¬ realSeriesConvergesValue a →
    divergesToPosInfinityValue (realPartialSumValue a)

def nonnegativeExtendedSumFiniteSubsets : Prop :=
  ∀ {ι : Type u} (a : ι → ℝ), (∀ i, 0 ≤ a i) →
    nonnegativeExtendedSumValue a =
      ⨆ F : Finset ι, ENNReal.ofReal (∑ i ∈ F, a i)

def nonnegativeExtendedSumPartialSums : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
    nonnegativeExtendedSumValue a = ⨆ N, ENNReal.ofReal (realPartialSumValue a N)

def nonnegativeExtendedSumTendsto : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
    Filter.Tendsto (fun N => ENNReal.ofReal (realPartialSumValue a N))
      Filter.atTop (𝓝 (nonnegativeExtendedSumValue a))

def nonnegativeExtendedSumOfHasSum : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) → ∀ S : ℝ,
    realSeriesHasSumValue a S → nonnegativeExtendedSumValue a = ENNReal.ofReal S

def nonnegativeExtendedSumEqTopIff : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
    (nonnegativeExtendedSumValue a = ∞ ↔ ¬ realSeriesConvergesValue a)

def nonnegativeExtendedSumReindex : Prop :=
  ∀ {ι : Type u} {κ : Type v} (a : κ → ℝ), (∀ i, 0 ≤ a i) →
    ∀ e : ι ≃ κ, nonnegativeExtendedSumValue (fun i => a (e i)) =
      nonnegativeExtendedSumValue a

def nonnegativeExtendedSumFiberwise : Prop :=
  ∀ {ι : Type u} (a : ℕ → ℝ), (∀ n, 0 ≤ a n) → ∀ q : ℕ → ι,
    (∑' i, nonnegativeExtendedSumValue (fun n : {n // q n = i} => a n)) =
      nonnegativeExtendedSumValue a

def nonnegativeExtendedSumPartition : Prop :=
  ∀ {ι : Type u} (a : ℕ → ℝ), (∀ n, 0 ≤ a n) → ∀ B : ι → Set ℕ,
    Pairwise (fun i j => Disjoint (B i) (B j)) → (⋃ i, B i) = Set.univ →
    (∑' i, nonnegativeExtendedSumValue (fun n : B i => a n)) =
      nonnegativeExtendedSumValue a

end Specs.SingleVariableAnalysis.Ch11.Nonnegative
