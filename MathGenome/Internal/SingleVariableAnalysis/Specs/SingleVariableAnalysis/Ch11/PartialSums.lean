import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification of K03.11.partial_sums (paper.tex:979–988).
Terms have indices n ≥ 0 and partial sums include both endpoints 0 and N.
A sum is a finite scalar limit of these ordered partial sums; no unconditional
summability is imposed. Finite alterations may occur anywhere up to m.
Linearity includes every finite family, including the empty family.
-/

namespace Specs.SingleVariableAnalysis.Ch11.PartialSums

open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open scoped BigOperators

def realPartialSumType : Type := (ℕ → ℝ) → ℕ → ℝ
noncomputable def realPartialSumValue : realPartialSumType :=
  fun a N => ∑ n ∈ Finset.range (N + 1), a n

def realSeriesHasSumType : Type := (ℕ → ℝ) → ℝ → Prop
noncomputable def realSeriesHasSumValue : realSeriesHasSumType :=
  fun a S => realSequenceConvergesValue (realPartialSumValue a) S

def realSeriesConvergesType : Type := (ℕ → ℝ) → Prop
noncomputable def realSeriesConvergesValue : realSeriesConvergesType :=
  fun a => ∃ S : ℝ, realSeriesHasSumValue a S

def realSeriesDivergesType : Type := (ℕ → ℝ) → Prop
noncomputable def realSeriesDivergesValue : realSeriesDivergesType :=
  fun a => ¬ realSeriesConvergesValue a

def realSeriesHasSumIff : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S ↔
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M, |((∑ n ∈ Finset.range (N + 1), a n) - S)| < ε

def realSeriesSumUnique : Prop :=
  ∀ (a : ℕ → ℝ) (S T : ℝ),
    realSeriesHasSumValue a S → realSeriesHasSumValue a T → S = T

def realPartialSumCorrection : Prop :=
  ∀ (a b : ℕ → ℝ) (m : ℕ), (∀ n, m < n → b n = a n) →
    ∀ N ≥ m, realPartialSumValue b N =
      realPartialSumValue a N + ∑ n ∈ Finset.range (m + 1), (b n - a n)

def realSeriesFiniteCorrectionIff : Prop :=
  ∀ (a b : ℕ → ℝ) (m : ℕ), (∀ n, m < n → b n = a n) →
    ∀ S : ℝ, realSeriesHasSumValue a S ↔
      realSeriesHasSumValue b (S + ∑ n ∈ Finset.range (m + 1), (b n - a n))

def realSeriesFiniteChangesIff : Prop :=
  ∀ (a b : ℕ → ℝ) (m : ℕ), (∀ n, m < n → b n = a n) →
    (realSeriesConvergesValue a ↔ realSeriesConvergesValue b)

def realSeriesAdd : Prop :=
  ∀ (a b : ℕ → ℝ) (S T : ℝ),
    realSeriesHasSumValue a S → realSeriesHasSumValue b T →
      realSeriesHasSumValue (fun n => a n + b n) (S + T)

def realSeriesConstMul : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S → ∀ c : ℝ,
    realSeriesHasSumValue (fun n => c * a n) (c * S)

def realSeriesFiniteLinearity : Prop :=
  ∀ {ι : Type} (s : Finset ι) (c : ι → ℝ) (a : ι → ℕ → ℝ) (S : ι → ℝ),
    (∀ i ∈ s, realSeriesHasSumValue (a i) (S i)) →
      realSeriesHasSumValue (fun n => ∑ i ∈ s, c i * a i n) (∑ i ∈ s, c i * S i)

def complexPartialSumType : Type := (ℕ → ℂ) → ℕ → ℂ
noncomputable def complexPartialSumValue : complexPartialSumType :=
  fun a N => ∑ n ∈ Finset.range (N + 1), a n

def complexSeriesHasSumType : Type := (ℕ → ℂ) → ℂ → Prop
noncomputable def complexSeriesHasSumValue : complexSeriesHasSumType :=
  fun a S => complexSequenceConvergesValue (complexPartialSumValue a) S

def complexSeriesConvergesType : Type := (ℕ → ℂ) → Prop
noncomputable def complexSeriesConvergesValue : complexSeriesConvergesType :=
  fun a => ∃ S : ℂ, complexSeriesHasSumValue a S

def complexSeriesDivergesType : Type := (ℕ → ℂ) → Prop
noncomputable def complexSeriesDivergesValue : complexSeriesDivergesType :=
  fun a => ¬ complexSeriesConvergesValue a

def complexSeriesHasSumIff : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S ↔
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M, ‖((∑ n ∈ Finset.range (N + 1), a n) - S)‖ < ε

def complexSeriesSumUnique : Prop :=
  ∀ (a : ℕ → ℂ) (S T : ℂ),
    complexSeriesHasSumValue a S → complexSeriesHasSumValue a T → S = T

def complexPartialSumCorrection : Prop :=
  ∀ (a b : ℕ → ℂ) (m : ℕ), (∀ n, m < n → b n = a n) →
    ∀ N ≥ m, complexPartialSumValue b N =
      complexPartialSumValue a N + ∑ n ∈ Finset.range (m + 1), (b n - a n)

def complexSeriesFiniteCorrectionIff : Prop :=
  ∀ (a b : ℕ → ℂ) (m : ℕ), (∀ n, m < n → b n = a n) →
    ∀ S : ℂ, complexSeriesHasSumValue a S ↔
      complexSeriesHasSumValue b (S + ∑ n ∈ Finset.range (m + 1), (b n - a n))

def complexSeriesFiniteChangesIff : Prop :=
  ∀ (a b : ℕ → ℂ) (m : ℕ), (∀ n, m < n → b n = a n) →
    (complexSeriesConvergesValue a ↔ complexSeriesConvergesValue b)

def complexSeriesAdd : Prop :=
  ∀ (a b : ℕ → ℂ) (S T : ℂ),
    complexSeriesHasSumValue a S → complexSeriesHasSumValue b T →
      complexSeriesHasSumValue (fun n => a n + b n) (S + T)

def complexSeriesConstMul : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S → ∀ c : ℂ,
    complexSeriesHasSumValue (fun n => c * a n) (c * S)

def complexSeriesFiniteLinearity : Prop :=
  ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (a : ι → ℕ → ℂ) (S : ι → ℂ),
    (∀ i ∈ s, complexSeriesHasSumValue (a i) (S i)) →
      complexSeriesHasSumValue (fun n => ∑ i ∈ s, c i * a i n) (∑ i ∈ s, c i * S i)

end Specs.SingleVariableAnalysis.Ch11.PartialSums
