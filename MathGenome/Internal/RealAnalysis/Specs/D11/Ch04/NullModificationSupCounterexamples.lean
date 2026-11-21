import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.NonborelLebesgue
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-! Independent statements for the two examples at paper.tex:1438–1453.
The domain and scalar target carry their Borel sigma-algebras. Native real
`volume` is a measure on that Borel domain; no completion is installed.
Indicators are real valued, and the supremum is the bounded real supremum
indexed by the points of the same non-Borel Cantor subset.
-/

noncomputable section
open Set MeasureTheory

namespace Specs.D11.Ch04.NullModificationSupCounterexamples

open Specs.D11.Ch03

def indicator_preimage_half : Prop :=
  ∀ N : Set ℝ, (N.indicator (fun _ => (1 : ℝ))) ⁻¹' Ioi (1 / 2 : ℝ) = N

def indicator_not_borel : Prop :=
  ∀ N : Set ℝ, ¬ MeasurableSet[borel ℝ] N →
    ¬ MeasurableMapTests.realMeasurable_value (borel ℝ) (N.indicator (fun _ => (1 : ℝ)))

/-- For every non-Borel subset of the fixed middle-thirds set, the modification
agrees with the measurable zero function off the Borel null envelope C. -/
def incomplete_modification_failure : Prop :=
  ∀ N : Set ℝ, N ⊆ CantorSet.C_value → ¬ MeasurableSet[borel ℝ] N →
    MeasurableSet[borel ℝ] CantorSet.C_value ∧
    (volume : Measure ℝ) CantorSet.C_value = 0 ∧
    MeasurableMapTests.realMeasurable_value (borel ℝ) (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ x, x ∉ CantorSet.C_value → N.indicator (fun _ => (1 : ℝ)) x = 0) ∧
    AeCommonException.aeEq_value (volume : Measure ℝ)
      (N.indicator (fun _ => (1 : ℝ))) (fun _ => 0) ∧
    ¬ MeasurableMapTests.realMeasurable_value (borel ℝ) (N.indicator (fun _ => (1 : ℝ))) ∧
    (N.indicator (fun _ => (1 : ℝ))) ⁻¹' Ioi (1 / 2 : ℝ) = N

/-- Each member of this genuinely uncountable family lies in [0,1], and its
pointwise real supremum is exactly the nonmeasurable indicator of N. -/
def uncountable_sup_failure : Prop :=
  ∀ N : Set ℝ, N ⊆ CantorSet.C_value → ¬ MeasurableSet[borel ℝ] N →
    ¬ N.Countable ∧
    (∀ a : N,
      MeasurableMapTests.realMeasurable_value (borel ℝ)
        (({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ))) ∧
      ∀ x : ℝ, 0 ≤ ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ∧
        ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ≤ 1) ∧
    (fun x : ℝ => ⨆ a : N, ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x) =
      N.indicator (fun _ => (1 : ℝ)) ∧
    ¬ MeasurableMapTests.realMeasurable_value (borel ℝ)
      (fun x : ℝ => ⨆ a : N, ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x)

/-- The non-Borel Cantor subset exists, so the modification failure is realized. -/
def exists_incomplete_modification : Prop :=
  ∃ N : Set ℝ, N ⊆ CantorSet.C_value ∧
    MeasurableSet[borel ℝ] CantorSet.C_value ∧
    (volume : Measure ℝ) CantorSet.C_value = 0 ∧
    MeasurableMapTests.realMeasurable_value (borel ℝ) (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ x, x ∉ CantorSet.C_value → N.indicator (fun _ => (1 : ℝ)) x = 0) ∧
    AeCommonException.aeEq_value (volume : Measure ℝ)
      (N.indicator (fun _ => (1 : ℝ))) (fun _ => 0) ∧
    ¬ MeasurableMapTests.realMeasurable_value (borel ℝ) (N.indicator (fun _ => (1 : ℝ))) ∧
    (N.indicator (fun _ => (1 : ℝ))) ⁻¹' Ioi (1 / 2 : ℝ) = N

def exists_uncountable_sup : Prop :=
  ∃ N : Set ℝ, N ⊆ CantorSet.C_value ∧ ¬ N.Countable ∧
    (∀ a : N,
      MeasurableMapTests.realMeasurable_value (borel ℝ)
        (({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ))) ∧
      ∀ x : ℝ, 0 ≤ ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ∧
        ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ≤ 1) ∧
    (fun x : ℝ => ⨆ a : N, ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x) =
      N.indicator (fun _ => (1 : ℝ)) ∧
    ¬ MeasurableMapTests.realMeasurable_value (borel ℝ)
      (fun x : ℝ => ⨆ a : N, ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x)

end Specs.D11.Ch04.NullModificationSupCounterexamples
