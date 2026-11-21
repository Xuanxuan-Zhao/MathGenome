import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LogisticFixedPoints
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! Independent specification of paper.tex, Proposition `d13:15:logistic-tent`.
The maps have the entire closed interval as both domain and codomain. -/
noncomputable section

namespace D13Unified.Ch15.LogisticTent

abbrev Interval := Set.Icc (0 : ℝ) 1

end D13Unified.Ch15.LogisticTent

namespace Specs.D13Unified.Ch15.LogisticTent
open _root_.D13Unified.Ch15.LogisticTent

def tentMapType := Interval → Interval

def tentMap : tentMapType := fun t =>
  ⟨if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ), by
    split_ifs with ht
    · constructor <;> linarith [t.property.1]
    · constructor <;> linarith [t.property.2]⟩

def coordinateType := Interval → Interval

def coordinate : coordinateType := fun t =>
  ⟨Real.sin (Real.pi * (t : ℝ) / 2) ^ 2,
    sq_nonneg _, Real.sin_sq_le_one _⟩

def logisticFourType := Interval → Interval

/-- Restriction of the canonical logistic map, at parameter four. -/
def logisticFour : logisticFourType := fun x =>
  ⟨Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap 4 x, by
    change 0 ≤ 4 * (x : ℝ) * (1 - x) ∧ 4 * (x : ℝ) * (1 - x) ≤ 1
    constructor
    · nlinarith [mul_nonneg x.property.1 (sub_nonneg.mpr x.property.2)]
    · nlinarith [sq_nonneg ((x : ℝ) - 1 / 2)]⟩

def tentBranches : Prop :=
  (∀ t : Interval, (t : ℝ) ≤ 1 / 2 → (tentMap t : ℝ) = 2 * (t : ℝ)) ∧
  (∀ t : Interval, 1 / 2 ≤ (t : ℝ) → (tentMap t : ℝ) = 2 - 2 * (t : ℝ))

def tentContinuous : Prop := Continuous tentMap

def coordinateIncreasing : Prop := StrictMono coordinate

/-- The specified sine-square coordinate is an increasing homeomorphism and
conjugates the tent map to the restriction of f₄, pointwise on all of [0,1]. -/
def conjugacy : Prop :=
  ∃ h : Interval ≃ₜ Interval,
    (∀ t : Interval, h t = coordinate t) ∧ StrictMono h ∧
      Specs.D13Unified.Ch15.DiscreteDefinitions.IsConjugacy tentMap logisticFour h

end Specs.D13Unified.Ch15.LogisticTent
