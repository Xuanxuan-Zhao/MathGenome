import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.MaximalNotL1

/-! Independent statements for paper.tex:3521–3531.
The weak quantity is an extended nonnegative supremum for every positive
real exponent. `weakNorm` takes an extended nonnegative magnitude, allowing
the maximal function; `scalarWeakNorm` applies it to the norm of a finite
scalar function. No completeness or sigma-finiteness is assumed in the
abstract assertions. The endpoint witness uses the shared completed
Euclidean line and the fixed indicator from Chapter 13.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
universe u v
namespace Specs.D11.Ch10.WeakEndpointBridge

def weakNorm_type := ∀ {X : Type u} [MeasurableSpace X],
  Measure X → ℝ → (X → ℝ≥0∞) → ℝ≥0∞

def weakNorm_value : weakNorm_type.{u} := fun μ p g =>
  ⨆ (α : ℝ) (_ : 0 < α), ENNReal.ofReal α * μ {x | ENNReal.ofReal α < g x} ^ (1 / p)

def scalarWeakNorm_type := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E], Measure X → ℝ → (X → E) → ℝ≥0∞

def scalarWeakNorm_value : scalarWeakNorm_type.{u,v} := fun μ p f =>
  weakNorm_value μ p (fun x => ENNReal.ofReal ‖f x‖)

def scalarWeakNorm_formula : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X) (p : ℝ) (f : X → E),
  scalarWeakNorm_value μ p f =
    ⨆ (α : ℝ) (_ : 0 < α), ENNReal.ofReal α * μ {x | α < ‖f x‖} ^ (1 / p)

/-- Stronger extended inequality; in particular it holds when the norm is finite. -/
def weak_le_powerNorm : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure X) (p : ℝ) (f : X → E), 0 < p → Measurable f →
  scalarWeakNorm_value μ p f ≤ Specs.D11.Ch10.LpDefinition.powerNorm_value μ p f

/-- At exponent one a uniform level-set estimate is exactly a weak-norm bound. -/
def weak_one_iff : Prop := ∀ {X : Type u} [MeasurableSpace X]
  (μ : Measure X) (g : X → ℝ≥0∞) (C : ℝ≥0∞),
  weakNorm_value μ 1 g ≤ C ↔
    ∀ α : ℝ, 0 < α → μ {x | ENNReal.ofReal α < g x} ≤ C / ENNReal.ofReal α

open _root_.D11.Ch03
local instance : MeasurableSpace (Point 1) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1

/-- A concrete weak bound and infinite strong integral for the same fixed maximal function.
The input has L1 norm one; the constant three need not be sharp. -/
def maximal_endpoint_witness : Prop :=
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)
      Specs.D11.Ch13.MaximalNotL1.indicator_value ∧
  (∫ y, ‖Specs.D11.Ch13.MaximalNotL1.indicator_value y‖
      ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)) = 1 ∧
  ∃ hf : Specs.D11.Ch13.AveragesMaximalDefinition.locallyIntegrable_value
      Specs.D11.Ch13.MaximalNotL1.indicator_value,
    weakNorm_value (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1) 1
      (Specs.D11.Ch13.AveragesMaximalDefinition.maximal_value
        Specs.D11.Ch13.MaximalNotL1.indicator_value hf) ≤ 3 ∧
    (∫⁻ y, Specs.D11.Ch13.AveragesMaximalDefinition.maximal_value
        Specs.D11.Ch13.MaximalNotL1.indicator_value hf y
      ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)) = ∞

end Specs.D11.Ch10.WeakEndpointBridge
