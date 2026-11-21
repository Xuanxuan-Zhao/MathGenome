import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! Independent statements for the probability representation in
`fa2:p1:convex-function-extremes`, paper.tex:6515–6562.

The function is represented as an ambient real function with assumptions and
conclusions only on [0,1]. In particular no continuity at 1 is assumed.
Measures live on the actual closed interval with its Borel sigma algebra.
-/
namespace ExpandedFA.Supplements.ConvexFunctionRepresentationSpec

open Set MeasureTheory Filter
open scoped Topology

abbrev UnitInterval := Icc (0 : ℝ) 1

/-- The hinge at 1 is the discontinuous endpoint function from the source. -/
noncomputable def hinge (r : UnitInterval) (x : ℝ) : ℝ :=
  if (r : ℝ) = 1 then (if x = 1 then 1 else 0)
  else max (x - (r : ℝ)) 0 / (1 - (r : ℝ))

def Normalized (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) ∧
  ConvexOn ℝ (Icc (0 : ℝ) 1) f ∧ f 0 = 0 ∧ f 1 = 1

noncomputable def mixture (μ : Measure UnitInterval) (x : ℝ) : ℝ :=
  ∫ r, hinge r x ∂μ

/-- Integrability and regularity are explicit; uniqueness is among actual
positive Borel measures, including arbitrary atoms at both endpoints. -/
def Represents (μ : Measure UnitInterval) (f : ℝ → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ Measure.Regular μ ∧
  ∀ x ∈ Icc (0 : ℝ) 1,
    Integrable (fun r => hinge r x) μ ∧ f x = mixture μ x

def Representation : Prop :=
  ∀ f : ℝ → ℝ, Normalized f → ∃! μ : Measure UnitInterval, Represents μ f

def Converse : Prop :=
  ∀ μ : Measure UnitInterval, IsProbabilityMeasure μ →
    Represents μ (mixture μ) ∧ Normalized (mixture μ)

/-- The original interval-domain formulation, with convexity written directly
using convex combinations of interval points. -/
def IntervalNormalized (f : UnitInterval → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  (∀ (x y : UnitInterval) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    f ⟨a * (x : ℝ) + b * (y : ℝ),
      (convex_Icc (0 : ℝ) 1) x.property y.property ha hb hab⟩ ≤ a * f x + b * f y) ∧
  f ⟨0, by norm_num⟩ = 0 ∧ f ⟨1, by norm_num⟩ = 1

def IntervalRepresents (μ : Measure UnitInterval) (f : UnitInterval → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ Measure.Regular μ ∧
  ∀ x : UnitInterval, Integrable (fun r => hinge r (x : ℝ)) μ ∧ f x = mixture μ (x : ℝ)

def SubtypeRepresentation : Prop :=
  ∀ f : UnitInterval → ℝ, IntervalNormalized f →
    ∃! μ : Measure UnitInterval, IntervalRepresents μ f

def SubtypeConverse : Prop :=
  ∀ μ : Measure UnitInterval, IsProbabilityMeasure μ →
    IntervalRepresents μ (fun x => mixture μ (x : ℝ)) ∧
      IntervalNormalized (fun x => mixture μ (x : ℝ))

/-- The two endpoint atoms and every interior cumulative mass are recovered
from the represented function. The upper endpoint formula is precisely
μ{1}=1-f(1-); the lower endpoint formula gives μ{0}=f'₊(0). -/
def Recovery : Prop :=
  ∀ (f : ℝ → ℝ) (μ : Measure UnitInterval), Represents μ f →
    Tendsto (fun x => f x / x) (𝓝[>] (0 : ℝ))
      (𝓝 (μ.real {r : UnitInterval | (r : ℝ) = 0})) ∧
    Tendsto f (𝓝[<] (1 : ℝ))
      (𝓝 (1 - μ.real {r : UnitInterval | (r : ℝ) = 1})) ∧
    ∀ x ∈ Ico (0 : ℝ) 1,
      Tendsto (fun y => f x + (1 - x) / (y - x) * (f y - f x)) (𝓝[>] x)
        (𝓝 (μ.real {r : UnitInterval | (r : ℝ) ≤ x}))

end ExpandedFA.Supplements.ConvexFunctionRepresentationSpec
