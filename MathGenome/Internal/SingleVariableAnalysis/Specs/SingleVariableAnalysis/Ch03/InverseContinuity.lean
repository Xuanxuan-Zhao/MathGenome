import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.IntervalImages
import Mathlib.Topology.Homeomorph.Defs

/-! Independent types for K03.03.inverse_continuity, paper.tex:576–587.
Intervals include empty sets and singletons. All topologies are induced from ℝ;
the homeomorphism and inverse assertions include any endpoints in the image.
The final assertion records the manuscript's specific disconnected example. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch03.InverseContinuity

open Specs.SingleVariableAnalysis.Ch03.Continuity
open Specs.SingleVariableAnalysis.Ch03.IntervalImages

def continuousMonotoneHomeomorph : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), realIntervalValue I →
    relativeContinuousValue f I → (StrictMonoOn f I ∨ StrictAntiOn f I) →
    realIntervalValue (f '' I) ∧
      ∃ e : I ≃ₜ (f '' I), ∀ x : I, (e x : ℝ) = f x

def continuousMonotoneInverse : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), realIntervalValue I →
    relativeContinuousValue f I → (StrictMonoOn f I ∨ StrictAntiOn f I) →
    Set.BijOn f I (f '' I) ∧ realIntervalValue (f '' I) ∧
      ∃ g : (f '' I) → I, Continuous g ∧
        (∀ x : I, g ⟨f x, ⟨x, x.property, rfl⟩⟩ = x) ∧
        (∀ y : (f '' I), f (g y) = (y : ℝ))

def disconnectedDomainType : Type := Set ℝ
def disconnectedDomainValue : Set ℝ := Set.Ico 0 1 ∪ {2}
def disconnectedMapType : Type := ℝ → ℝ
def disconnectedMapValue : ℝ → ℝ := fun x => if x < 1 then x else 1
def disconnectedInverseType : Type := ℝ → ℝ
def disconnectedInverseValue : ℝ → ℝ := fun y => if y < 1 then y else 2

def disconnectedInverseCounterexample : Prop :=
  ¬ realIntervalValue disconnectedDomainValue ∧
    relativeContinuousValue disconnectedMapValue disconnectedDomainValue ∧
    StrictMonoOn disconnectedMapValue disconnectedDomainValue ∧
    disconnectedMapValue '' disconnectedDomainValue = Set.Icc 0 1 ∧
    Set.MapsTo disconnectedInverseValue (Set.Icc 0 1) disconnectedDomainValue ∧
    (∀ x ∈ disconnectedDomainValue,
      disconnectedInverseValue (disconnectedMapValue x) = x) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1,
      disconnectedMapValue (disconnectedInverseValue y) = y) ∧
    ¬ relativeContinuousAtValue disconnectedInverseValue (Set.Icc 0 1) 1

end Specs.SingleVariableAnalysis.Ch03.InverseContinuity
