import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of K03.11.absolute, paper.tex:1081–1090.
Absolute convergence means ordinary convergence of the real series of
magnitudes. Conditional convergence uses the ordinary scalar series, with
no absolute-convergence assumption. A tail beginning at p is reindexed as
n ↦ a (n + p); in particular p = 0 retains the entire original series.
All sum values below are finite and are witnessed by partial-sum limits.
-/

namespace Specs.SingleVariableAnalysis.Ch11.Absolute

open PartialSums
open scoped BigOperators

def realAbsolutelyConvergesType : Type := (ℕ → ℝ) → Prop
noncomputable def realAbsolutelyConvergesValue : realAbsolutelyConvergesType :=
  fun a => realSeriesConvergesValue (fun n => |a n|)

def complexAbsolutelyConvergesType : Type := (ℕ → ℂ) → Prop
noncomputable def complexAbsolutelyConvergesValue : complexAbsolutelyConvergesType :=
  fun a => realSeriesConvergesValue (fun n => ‖a n‖)

def realConditionallyConvergesType : Type := (ℕ → ℝ) → Prop
noncomputable def realConditionallyConvergesValue : realConditionallyConvergesType :=
  fun a => realSeriesConvergesValue a ∧ ¬ realAbsolutelyConvergesValue a

def complexConditionallyConvergesType : Type := (ℕ → ℂ) → Prop
noncomputable def complexConditionallyConvergesValue : complexConditionallyConvergesType :=
  fun a => complexSeriesConvergesValue a ∧ ¬ complexAbsolutelyConvergesValue a

def realAbsoluteConverges : Prop :=
  ∀ a : ℕ → ℝ, realAbsolutelyConvergesValue a → realSeriesConvergesValue a

def complexAbsoluteConverges : Prop :=
  ∀ a : ℕ → ℂ, complexAbsolutelyConvergesValue a → complexSeriesConvergesValue a

def realTailHasSum : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S → ∀ p : ℕ,
    realSeriesHasSumValue (fun n => a (n + p))
      (S - ∑ n ∈ Finset.range p, a n)

def complexTailHasSum : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S → ∀ p : ℕ,
    complexSeriesHasSumValue (fun n => a (n + p))
      (S - ∑ n ∈ Finset.range p, a n)

def realTailBound : Prop :=
  ∀ (a : ℕ → ℝ) (p : ℕ) (S A : ℝ),
    realSeriesHasSumValue (fun n => a (n + p)) S →
    realSeriesHasSumValue (fun n => |a (n + p)|) A → |S| ≤ A

def complexTailBound : Prop :=
  ∀ (a : ℕ → ℂ) (p : ℕ) (S : ℂ) (A : ℝ),
    complexSeriesHasSumValue (fun n => a (n + p)) S →
    realSeriesHasSumValue (fun n => ‖a (n + p)‖) A → ‖S‖ ≤ A

def realAbsoluteTails : Prop :=
  ∀ a : ℕ → ℝ, realAbsolutelyConvergesValue a → ∀ p : ℕ,
    ∃ S A : ℝ, realSeriesHasSumValue (fun n => a (n + p)) S ∧
      realSeriesHasSumValue (fun n => |a (n + p)|) A ∧ |S| ≤ A

def complexAbsoluteTails : Prop :=
  ∀ a : ℕ → ℂ, complexAbsolutelyConvergesValue a → ∀ p : ℕ,
    ∃ (S : ℂ) (A : ℝ), complexSeriesHasSumValue (fun n => a (n + p)) S ∧
      realSeriesHasSumValue (fun n => ‖a (n + p)‖) A ∧ ‖S‖ ≤ A

end Specs.SingleVariableAnalysis.Ch11.Absolute
