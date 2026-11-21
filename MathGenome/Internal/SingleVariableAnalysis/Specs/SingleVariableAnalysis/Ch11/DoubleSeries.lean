import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
Independent specification of K03.11.double_series, paper.tex:1130–1137.
Both indices start at zero. Nonnegative sums are extended nonnegative real
sums, including infinity, with an explicit finite-subset supremum formula.
In the absolute case the sole hypothesis is finiteness of the extended sum
of magnitudes. All scalar series in the conclusion use the upstream ordinary
inclusive partial-sum limits. The row and column sums and every bijective
enumeration are absolutely convergent and have the same finite value.
The example retains the source's exact diagonal and superdiagonal entries.
-/

namespace Specs.SingleVariableAnalysis.Ch11.DoubleSeries

open scoped BigOperators ENNReal
open Nonnegative PartialSums Absolute

def nonnegativeDoubleSeries : Prop :=
  ∀ a : ℕ → ℕ → ℝ, (∀ i j, 0 ≤ a i j) →
    nonnegativeExtendedSumValue (fun p : ℕ × ℕ => a p.1 p.2) =
      (⨆ F : Finset (ℕ × ℕ), ENNReal.ofReal (∑ p ∈ F, a p.1 p.2)) ∧
    (∑' i, nonnegativeExtendedSumValue (a i)) =
      nonnegativeExtendedSumValue (fun p : ℕ × ℕ => a p.1 p.2) ∧
    (∑' j, nonnegativeExtendedSumValue (fun i => a i j)) =
      nonnegativeExtendedSumValue (fun p : ℕ × ℕ => a p.1 p.2) ∧
    ∀ e : ℕ ≃ (ℕ × ℕ),
      nonnegativeExtendedSumValue (fun n => a (e n).1 (e n).2) =
        nonnegativeExtendedSumValue (fun p : ℕ × ℕ => a p.1 p.2)

def realAbsoluteDoubleSeries : Prop :=
  ∀ a : ℕ → ℕ → ℝ,
    nonnegativeExtendedSumValue (fun p : ℕ × ℕ => |a p.1 p.2|) < ∞ →
    let S := ∑' p : ℕ × ℕ, a p.1 p.2
    HasSum (fun p : ℕ × ℕ => a p.1 p.2) S ∧
    (∀ i, realAbsolutelyConvergesValue (a i) ∧
      realSeriesHasSumValue (a i) (∑' j, a i j)) ∧
    (∀ j, realAbsolutelyConvergesValue (fun i => a i j) ∧
      realSeriesHasSumValue (fun i => a i j) (∑' i, a i j)) ∧
    realAbsolutelyConvergesValue (fun i => ∑' j, a i j) ∧
    realSeriesHasSumValue (fun i => ∑' j, a i j) S ∧
    realAbsolutelyConvergesValue (fun j => ∑' i, a i j) ∧
    realSeriesHasSumValue (fun j => ∑' i, a i j) S ∧
    ∀ e : ℕ ≃ (ℕ × ℕ),
      realAbsolutelyConvergesValue (fun n => a (e n).1 (e n).2) ∧
      realSeriesHasSumValue (fun n => a (e n).1 (e n).2) S

def complexAbsoluteDoubleSeries : Prop :=
  ∀ a : ℕ → ℕ → ℂ,
    nonnegativeExtendedSumValue (fun p : ℕ × ℕ => ‖a p.1 p.2‖) < ∞ →
    let S := ∑' p : ℕ × ℕ, a p.1 p.2
    HasSum (fun p : ℕ × ℕ => a p.1 p.2) S ∧
    (∀ i, complexAbsolutelyConvergesValue (a i) ∧
      complexSeriesHasSumValue (a i) (∑' j, a i j)) ∧
    (∀ j, complexAbsolutelyConvergesValue (fun i => a i j) ∧
      complexSeriesHasSumValue (fun i => a i j) (∑' i, a i j)) ∧
    complexAbsolutelyConvergesValue (fun i => ∑' j, a i j) ∧
    complexSeriesHasSumValue (fun i => ∑' j, a i j) S ∧
    complexAbsolutelyConvergesValue (fun j => ∑' i, a i j) ∧
    complexSeriesHasSumValue (fun j => ∑' i, a i j) S ∧
    ∀ e : ℕ ≃ (ℕ × ℕ),
      complexAbsolutelyConvergesValue (fun n => a (e n).1 (e n).2) ∧
      complexSeriesHasSumValue (fun n => a (e n).1 (e n).2) S

def orderExampleType : Type := ℕ → ℕ → ℝ

def orderExampleValue : orderExampleType :=
  fun i j => if j = i then 1 else if j = i + 1 then -1 else 0

def orderExampleRows : Prop :=
  ∀ i, realSeriesHasSumValue (orderExampleValue i) 0

def orderExampleColumns : Prop :=
  ∀ j, realSeriesHasSumValue (fun i => orderExampleValue i j)
    (if j = 0 then 1 else 0)

def orderExampleIterated : Prop :=
  (∀ i, realSeriesHasSumValue (orderExampleValue i) 0) ∧
  (∀ j, realSeriesHasSumValue (fun i => orderExampleValue i j)
    (if j = 0 then 1 else 0)) ∧
  realSeriesHasSumValue (fun _ : ℕ => (0 : ℝ)) 0 ∧
  realSeriesHasSumValue (fun j : ℕ => if j = 0 then (1 : ℝ) else 0) 1 ∧
  (0 : ℝ) ≠ 1

def orderExampleNotAbsolute : Prop :=
  nonnegativeExtendedSumValue (fun p : ℕ × ℕ => |orderExampleValue p.1 p.2|) = ∞

end Specs.SingleVariableAnalysis.Ch11.DoubleSeries
