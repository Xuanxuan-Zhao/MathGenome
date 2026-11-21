import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConvexEnergySubendpoint
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Endpoint assertions of paper.tex, fa2:p4:nemytskii-energy, 21459–21503.
The canonical primitive, remainder, exponents and hypotheses are those of the
accepted subendpoint interface. The underlying finite measure may be zero. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u
namespace ExpandedFA.PartIV.ConvexEnergyEndpoints.Spec
open ExpandedFA.PartIV.ConvexEnergySubendpoint.Spec

/-- The additional lower growth assumption in the manuscript. -/
def LowerGrowth (p : ℝ≥0∞) (g : ℝ → ℝ) : Prop :=
  ∃ α C : ℝ, 0 < α ∧ ∀ t : ℝ, α * |t| ^ (p.toReal - 1) - C ≤ |g t|

/-- Coercivity is derived from scalar growth; it is not a hypothesis on the sequence. -/
def RemainderCoercivity : Prop :=
  ∀ (p : ℝ≥0∞), 1 < p → p ≠ ∞ → ∀ g : ℝ → ℝ,
    Continuous g → Monotone g → UpperGrowth p g → LowerGrowth p g →
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ a b : ℝ,
      |a| ^ p.toReal ≤ A * remainder g a b + B * (1 + |b| ^ p.toReal)

def PowerUniformIntegrability : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ℝ → ℝ)
    (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ),
    Hypotheses μ p g v u → LowerGrowth p g →
      UnifIntegrable (fun n x => |v n x| ^ p.toReal) 1 μ

def ImageEndpoint : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ℝ → ℝ)
    (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ),
    Hypotheses μ p g v u → LowerGrowth p g →
      (∀ n, MemLp (fun x => g (v n x)) (conjugate p) μ) ∧
      MemLp (fun x => g (u x)) (conjugate p) μ ∧
      Tendsto (fun n => eLpNorm (fun x => g (v n x) - g (u x)) (conjugate p) μ)
        atTop (𝓝 0)

def StrictEndpoint : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ℝ → ℝ)
    (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ),
    Hypotheses μ p g v u → LowerGrowth p g → StrictMono g →
      Tendsto (fun n => eLpNorm (fun x => v n x - u x) p μ) atTop (𝓝 0)
end ExpandedFA.PartIV.ConvexEnergyEndpoints.Spec
