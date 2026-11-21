import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Nonnegative

/-!
Independent specification of the first paragraph of K03.11.rearrange_conditional
(paper.tex:1097–1104). All finite sums are ordinary inclusive partial sums.
The zero-padded positive/negative parts retain the original indices. The lists
below enumerate exactly the strictly positive/negative indices in original order;
zero terms belong to neither list. Conditional convergence has its upstream
ordinary meaning, with no unconditional summability hypothesis.
-/

namespace Specs.SingleVariableAnalysis.Ch11.PositiveNegative

open PartialSums Absolute Nonnegative
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open scoped ENNReal

def positivePartType : Type := (ℕ → ℝ) → ℕ → ℝ
noncomputable def positivePartValue : positivePartType := fun a n => max (a n) 0

def negativePartType : Type := (ℕ → ℝ) → ℕ → ℝ
noncomputable def negativePartValue : negativePartType := fun a n => max (-a n) 0

def partIdentities : Prop := ∀ (a : ℕ → ℝ) (n : ℕ),
  0 ≤ positivePartValue a n ∧ 0 ≤ negativePartValue a n ∧
  a n = positivePartValue a n - negativePartValue a n ∧
  |a n| = positivePartValue a n + negativePartValue a n

def partsDiverge : Prop := ∀ (a : ℕ → ℝ), realConditionallyConvergesValue a →
  divergesToPosInfinityValue (realPartialSumValue (positivePartValue a)) ∧
  divergesToPosInfinityValue (realPartialSumValue (negativePartValue a))

def partsExtendedSum : Prop := ∀ (a : ℕ → ℝ), realConditionallyConvergesValue a →
  nonnegativeExtendedSumValue (positivePartValue a) = ∞ ∧
  nonnegativeExtendedSumValue (negativePartValue a) = ∞

def negativeTermsDiverge : Prop := ∀ (a : ℕ → ℝ), realConditionallyConvergesValue a →
  divergesToNegInfinityValue (realPartialSumValue (fun n => -negativePartValue a n))

def signSetsInfinite : Prop := ∀ (a : ℕ → ℝ), realConditionallyConvergesValue a →
  Set.Infinite {n | 0 < a n} ∧ Set.Infinite {n | a n < 0}

/-- Applies to every increasing enumeration, not just a chosen witness. -/
def listMagnitudesTendToZero : Prop :=
  ∀ (a : ℕ → ℝ), realConditionallyConvergesValue a →
  ∀ r : ℕ → ℕ, StrictMono r →
    realSequenceConvergesValue (fun j => |a (r j)|) 0

/-- Exhaustive lists in the original order exist, with vanishing magnitudes. -/
def signLists : Prop := ∀ (a : ℕ → ℝ), realConditionallyConvergesValue a →
  ∃ r s : ℕ → ℕ, StrictMono r ∧ StrictMono s ∧
    Set.range r = {n | 0 < a n} ∧ Set.range s = {n | a n < 0} ∧
    realSequenceConvergesValue (fun j => |a (r j)|) 0 ∧
    realSequenceConvergesValue (fun j => |a (s j)|) 0

end Specs.SingleVariableAnalysis.Ch11.PositiveNegative
