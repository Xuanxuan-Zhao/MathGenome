import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.PositiveRoots
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Limsup
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute

/-!
Independent specification of K03.11.root (paper.tex:1027–1033).
The ordinary series uses indices n ≥ 0. The limsup omits only index zero:
its nth entry is the positive (n+1)st root of the magnitude of a (n+1).
It uses the upstream supremum construction of roots and the extended-real
infimum of tail suprema, without boundedness or nonvanishing assumptions.
Nonnegativity places this EReal value in [0,+∞], and the strict comparisons
include L = 0 and L = +∞. The boundary examples use 1/n and 1/n² for n ≥ 1;
the library's harmless value 0 at index zero is retained explicitly.
-/
namespace Specs.SingleVariableAnalysis.Ch11.Root

open Specs.SingleVariableAnalysis.Ch01.PositiveRoots
open Specs.SingleVariableAnalysis.Ch01.Limsup
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open Specs.SingleVariableAnalysis.Ch11.Absolute

def realRootLimsupType : Type := (ℕ → ℝ) → EReal
noncomputable def realRootLimsupValue : realRootLimsupType :=
  fun a => sequenceLimsupValue (fun n => nonnegativeRootValue (n+1) |a (n+1)|)
def complexRootLimsupType : Type := (ℕ → ℂ) → EReal
noncomputable def complexRootLimsupValue : complexRootLimsupType :=
  fun a => sequenceLimsupValue (fun n => nonnegativeRootValue (n+1) ‖a (n+1)‖)

def realRootLimsupNonneg : Prop := ∀ a, 0 ≤ realRootLimsupValue a
def complexRootLimsupNonneg : Prop := ∀ a, 0 ≤ complexRootLimsupValue a

def realRootTestAbsolute : Prop := ∀ a, realRootLimsupValue a < 1 →
  realAbsolutelyConvergesValue a
def complexRootTestAbsolute : Prop := ∀ a, complexRootLimsupValue a < 1 →
  complexAbsolutelyConvergesValue a

def realRootTestDiverges : Prop := ∀ a, 1 < realRootLimsupValue a →
  realSeriesDivergesValue a
def complexRootTestDiverges : Prop := ∀ a, 1 < complexRootLimsupValue a →
  complexSeriesDivergesValue a

def realRootTestZero : Prop := ∀ a, realRootLimsupValue a = 0 →
  realAbsolutelyConvergesValue a
def complexRootTestZero : Prop := ∀ a, complexRootLimsupValue a = 0 →
  complexAbsolutelyConvergesValue a

def realRootTestTop : Prop := ∀ a, realRootLimsupValue a = ⊤ →
  realSeriesDivergesValue a
def complexRootTestTop : Prop := ∀ a, complexRootLimsupValue a = ⊤ →
  complexSeriesDivergesValue a

def harmonicRootLimit : Prop :=
  realSequenceConvergesValue
    (fun n => nonnegativeRootValue (n+1) |1 / ((n+1 : ℕ) : ℝ)|) 1

def reciprocalSquareRootLimit : Prop :=
  realSequenceConvergesValue
    (fun n => nonnegativeRootValue (n+1) |1 / (((n+1 : ℕ) : ℝ)^2)|) 1

/-- Equal root limsups and different ordinary convergence verdicts. -/
def rootTestBoundaryExamples : Prop :=
  realRootLimsupValue (fun n => 1 / (n : ℝ)) = 1 ∧
  realRootLimsupValue (fun n => 1 / (n : ℝ)^2) = 1 ∧
  realSeriesDivergesValue (fun n => 1 / (n : ℝ)) ∧
  realAbsolutelyConvergesValue (fun n => 1 / (n : ℝ)^2)

end Specs.SingleVariableAnalysis.Ch11.Root
