import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuityPartitions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.EReal.Lemmas

/-! Independent statements for the Portmanteau theorem, paper.tex 1473–1514.
The extended integral of a function bounded below by the real number `c` is
computed by integrating its nonnegative translate and adding `c`. For a function
bounded above, negate first. These formulas retain infinite values, and require
no integrability assumption. Bounds are quantified, not fixed in advance.
`lowerIntegral` is used only with `c ≤ f`; `upperIntegral` only with `f ≤ c`.
The implementation also proves independence of the chosen lower bound.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch06.Portmanteau

universe u
noncomputable section

variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The extended Lebesgue integral, evaluated using a real lower bound. -/
def lowerIntegral (μ : ProbabilityMeasure S) (f : S → EReal) (c : ℝ) : EReal :=
  (c : EReal) + ((∫⁻ x, (f x - (c : EReal)).toENNReal ∂(μ : Measure S)) : EReal)

/-- The extended Lebesgue integral, evaluated using a real upper bound. -/
def upperIntegral (μ : ProbabilityMeasure S) (f : S → EReal) (c : ℝ) : EReal :=
  -lowerIntegral μ (fun x => -f x) (-c)

def ClosedUpperBound (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) : Prop :=
  ∀ F : Set S, IsClosed F → limsup (fun n => (μs n : Measure S) F) atTop ≤ (μ : Measure S) F

def OpenLowerBound (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) : Prop :=
  ∀ G : Set S, IsOpen G → (μ : Measure S) G ≤ liminf (fun n => (μs n : Measure S) G) atTop

def ContinuitySetConvergence (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) : Prop :=
  ∀ A : Set S, ContinuityPartitions.isContinuitySetValue (μ : Measure S) A →
    Tendsto (fun n => (μs n : Measure S) A) atTop (𝓝 ((μ : Measure S) A))

def LowerIntegralBound (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) : Prop :=
  ∀ (f : S → EReal), LowerSemicontinuous f → ∀ c : ℝ, (∀ x, (c : EReal) ≤ f x) →
    lowerIntegral μ f c ≤ liminf (fun n => lowerIntegral (μs n) f c) atTop

def UpperIntegralBound (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) : Prop :=
  ∀ (f : S → EReal), UpperSemicontinuous f → ∀ c : ℝ, (∀ x, f x ≤ (c : EReal)) →
    limsup (fun n => upperIntegral (μs n) f c) atTop ≤ upperIntegral μ f c

def weakIffClosedType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) ↔ ClosedUpperBound μs μ

def weakIffOpenType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) ↔ OpenLowerBound μs μ

def weakIffContinuityType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) ↔ ContinuitySetConvergence μs μ

def weakIffLowerType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) ↔ LowerIntegralBound μs μ

def weakIffUpperType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) ↔ UpperIntegralBound μs μ

/-- The representation of the extended integral is independent of its bound. -/
def lowerIntegralBoundIndependentType : Prop := ∀ {S : Type u} [MeasurableSpace S]
  (μ : ProbabilityMeasure S) (f : S → EReal) (c d : ℝ),
  (∀ x, (c : EReal) ≤ f x) → (∀ x, (d : EReal) ≤ f x) →
  lowerIntegral μ f c = lowerIntegral μ f d

def lowerIntegralNonnegativeType : Prop := ∀ {S : Type u} [MeasurableSpace S]
  (μ : ProbabilityMeasure S) (f : S → ℝ≥0∞),
  lowerIntegral μ (fun x => (f x : EReal)) 0 =
    ((∫⁻ x, f x ∂(μ : Measure S)) : EReal)

def lowerIntegralIntegrableType : Prop := ∀ {S : Type u} [MeasurableSpace S]
  (μ : ProbabilityMeasure S) (f : S → ℝ), Integrable f (μ : Measure S) →
  ∀ c : ℝ, (∀ x, c ≤ f x) →
  lowerIntegral μ (fun x => (f x : EReal)) c =
    ((∫ x, f x ∂(μ : Measure S) : ℝ) : EReal)

end
end Specs.ProbabilityFoundations.Ch06.Portmanteau
