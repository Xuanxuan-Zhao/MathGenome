import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.BernoulliMeasure
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ChaosDefinitions

/-! Full conclusions of paper.tex, Theorem d13:19:bernoulli-mixing.
The frequency is the proportion of ones at coordinates 0,...,n-1, also
for the two-sided shift. Mixing quantifies over all Borel measurable pairs
through the canonical product measurable structure. -/
namespace Specs.D13Unified.Ch19.BernoulliMixing
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Specs.D13Unified.Ch17.ShiftSpaces
open Specs.D13Unified.Ch19.BernoulliMeasure

def preservesPlusStatement : Prop := MeasureDefinitions.PreservesMeasure shiftPlus bernoulliPlus
def preservesTwoSidedStatement : Prop := MeasureDefinitions.PreservesMeasure shift bernoulliTwoSided
def mixingPlusStatement : Prop := MeasureDefinitions.IsMixing shiftPlus bernoulliPlus
def mixingTwoSidedStatement : Prop := MeasureDefinitions.IsMixing shift bernoulliTwoSided
def ergodicPlusStatement : Prop := MeasureDefinitions.IsErgodic shiftPlus bernoulliPlus
def ergodicTwoSidedStatement : Prop := MeasureDefinitions.IsErgodic shift bernoulliTwoSided

def frequencyPlusStatement : Prop :=
  ∀ᵐ s ∂bernoulliPlus, Tendsto
    (fun n : ℕ => (∑ j ∈ Finset.range n, ((s j).val : ℝ)) / (n : ℝ))
    atTop (𝓝 (1 / 2))
def frequencyTwoSidedStatement : Prop :=
  ∀ᵐ s ∂bernoulliTwoSided, Tendsto
    (fun n : ℕ => (∑ j ∈ Finset.range n, ((s (j : ℤ)).val : ℝ)) / (n : ℝ))
    atTop (𝓝 (1 / 2))

def fixedNullPlusStatement : Prop :=
  ∀ n : ℕ, 0 < n → bernoulliPlus {s | shiftPlus^[n] s = s} = 0
def fixedNullTwoSidedStatement : Prop :=
  ∀ n : ℕ, 0 < n → bernoulliTwoSided {s | shift^[n] s = s} = 0

def periodicNullPlusStatement : Prop :=
  bernoulliPlus (Specs.D13Unified.Ch17.ChaosDefinitions.periodicPoints shiftPlus) = 0
def periodicNullTwoSidedStatement : Prop :=
  bernoulliTwoSided (Specs.D13Unified.Ch17.ChaosDefinitions.periodicPoints shift) = 0
def periodicDensePlusStatement : Prop :=
  Dense (Specs.D13Unified.Ch17.ChaosDefinitions.periodicPoints shiftPlus)
def periodicDenseTwoSidedStatement : Prop :=
  Dense (Specs.D13Unified.Ch17.ChaosDefinitions.periodicPoints shift)
end
end Specs.D13Unified.Ch19.BernoulliMixing
