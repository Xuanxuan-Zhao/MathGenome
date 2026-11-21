import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.RotationUniqueErgodic
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.RigidRotation

/-! Full statement of `paper.tex`, Theorem `d13:19:rotation-ergodicity`.
The circle, rotation, Lebesgue measure, and mod-null predicates are the
canonical upstream objects. Uniformity is over every real starting point. -/
namespace Specs.D13Unified.Ch19.RotationErgodicity

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
open RotationUniqueErgodic

/-- Unit-interval normalization of the circle probability and its integral. -/
def normalizationStatement : Prop :=
  IsProbabilityMeasure (volume : Measure Circle) ∧
  (∀ t : ℝ, (volume : Measure Circle) = Measure.map
    Specs.D13Unified.Ch15.CircleLift.quotientMap (volume.restrict (Ioc t (t + 1)))) ∧
  ∀ f : Circle → ℝ, (∫ x, f x ∂(volume : Measure Circle)) =
    ∫ t in (0 : ℝ)..1, f (Specs.D13Unified.Ch15.CircleLift.quotientMap t)

def preservesStatement : Prop :=
  ∀ α : ℝ, MeasureDefinitions.PreservesMeasure (rotation α) (volume : Measure Circle)

def ergodicStatement : Prop :=
  ∀ α : ℝ, Irrational α →
    MeasureDefinitions.IsErgodic (rotation α) (volume : Measure Circle)

def uniquelyErgodicStatement : Prop :=
  ∀ α : ℝ, Irrational α → ∀ η : Measure Circle, IsProbabilityMeasure η →
    MeasureDefinitions.PreservesMeasure (rotation α) η → η = (volume : Measure Circle)

def notMixingStatement : Prop :=
  ∀ α : ℝ, Irrational α →
    ¬ MeasureDefinitions.IsMixing (rotation α) (volume : Measure Circle)

/-- A concrete measurable witness: the arc of radius 1/8 has mass 1/4,
and its self-correlation vanishes at arbitrarily large positive times. -/
def nonmixingWitnessStatement : Prop :=
  ∀ α : ℝ, Irrational α →
    ∃ A : Set Circle, MeasurableSet A ∧
      (volume : Measure Circle) A = ENNReal.ofReal (1 / 4) ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        (volume : Measure Circle) (A ∩ ((rotation α)^[n] ⁻¹' A)) = 0

/-- For each continuous 1-periodic real function, one eventual bound works
for all real x. No rate or additional regularity is assumed. -/
def periodicUniformAveragesStatement : Prop :=
  ∀ α : ℝ, Irrational α → ∀ g : ℝ → ℝ, Continuous g → Function.Periodic g 1 →
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ,
      |(∑ j ∈ Finset.range n, g (x + (j : ℝ) * α)) / (n : ℝ) -
        ∫ t in (0 : ℝ)..1, g t| < ε

end
end Specs.D13Unified.Ch19.RotationErgodicity
