import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of K03.11.cesaro, paper.tex:1160–1169.
Terms start at zero, and each partial sum and mean includes its final index.
Cesàro sums are finite limits of averages of ordinary ordered partial sums.
The real and complex predicates are separate from ordinary series convergence.
-/
namespace Specs.SingleVariableAnalysis.Ch11.Cesaro

open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open scoped BigOperators

def realSeriesCesaroMeanType : Type := (ℕ → ℝ) → ℕ → ℝ
noncomputable def realSeriesCesaroMeanValue : realSeriesCesaroMeanType :=
  fun a N => ((N : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (N + 1), realPartialSumValue a j

def realSeriesCesaroHasSumType : Type := (ℕ → ℝ) → ℝ → Prop
noncomputable def realSeriesCesaroHasSumValue : realSeriesCesaroHasSumType :=
  fun a S => realSequenceConvergesValue (realSeriesCesaroMeanValue a) S

def realSeriesCesaroConvergesType : Type := (ℕ → ℝ) → Prop
noncomputable def realSeriesCesaroConvergesValue : realSeriesCesaroConvergesType :=
  fun a => ∃ S, realSeriesCesaroHasSumValue a S

def complexSeriesCesaroMeanType : Type := (ℕ → ℂ) → ℕ → ℂ
noncomputable def complexSeriesCesaroMeanValue : complexSeriesCesaroMeanType :=
  fun a N => ((N : ℂ) + 1)⁻¹ * ∑ j ∈ Finset.range (N + 1), complexPartialSumValue a j

def complexSeriesCesaroHasSumType : Type := (ℕ → ℂ) → ℂ → Prop
noncomputable def complexSeriesCesaroHasSumValue : complexSeriesCesaroHasSumType :=
  fun a S => complexSequenceConvergesValue (complexSeriesCesaroMeanValue a) S

def complexSeriesCesaroConvergesType : Type := (ℕ → ℂ) → Prop
noncomputable def complexSeriesCesaroConvergesValue : complexSeriesCesaroConvergesType :=
  fun a => ∃ S, complexSeriesCesaroHasSumValue a S

def realOrdinaryImpliesCesaro : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S → realSeriesCesaroHasSumValue a S

def complexOrdinaryImpliesCesaro : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S → complexSeriesCesaroHasSumValue a S

def realCesaroSumUnique : Prop :=
  ∀ (a : ℕ → ℝ) (S T : ℝ),
    realSeriesCesaroHasSumValue a S → realSeriesCesaroHasSumValue a T → S = T

def complexCesaroSumUnique : Prop :=
  ∀ (a : ℕ → ℂ) (S T : ℂ),
    complexSeriesCesaroHasSumValue a S → complexSeriesCesaroHasSumValue a T → S = T

def realAlternatingCesaro : Prop :=
  realSeriesCesaroHasSumValue (fun n => (-1 : ℝ)^n) (1/2)

def complexAlternatingCesaro : Prop :=
  complexSeriesCesaroHasSumValue (fun n => (-1 : ℂ)^n) (1/2)

def realAlternatingDiverges : Prop :=
  realSeriesDivergesValue (fun n => (-1 : ℝ)^n)

def complexAlternatingDiverges : Prop :=
  complexSeriesDivergesValue (fun n => (-1 : ℂ)^n)

def realCesaroNotOrdinary : Prop :=
  ∃ a : ℕ → ℝ, realSeriesCesaroConvergesValue a ∧ ¬ realSeriesConvergesValue a

def complexCesaroNotOrdinary : Prop :=
  ∃ a : ℕ → ℂ, complexSeriesCesaroConvergesValue a ∧ ¬ complexSeriesConvergesValue a

end Specs.SingleVariableAnalysis.Ch11.Cesaro
