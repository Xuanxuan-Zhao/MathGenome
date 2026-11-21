import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Order.LiminfLimsup

/-!
Independent statements for paper.tex, `fa2:p4:nemytskii-energy`, lines 21449–21486.
Only the subendpoint assertions are assigned here. Endpoint assertions and the
counterexample are allocated to separate goals. Functions are real valued and
μ is an arbitrary finite positive measure, including the zero measure.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace ExpandedFA.PartIV.ConvexEnergySubendpoint.Spec

/-- The oriented primitive appearing in the source. -/
def primitive (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, g s

/-- Bregman remainder, with the tangent based at the second argument. -/
def remainder (g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  primitive g a - primitive g b - g b * (a - b)

/-- Polynomial upper growth at the original exponent. -/
def UpperGrowth (p : ℝ≥0∞) (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |g t| ≤ C * (1 + |t| ^ (p.toReal - 1))

/-- Continuous scalar-linear tests, on the ordinary a.e. Lp quotient. -/
def WeaklyConverges {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ) : Prop :=
  ∀ L : Lp ℝ p μ →L[ℝ] ℝ, Tendsto (fun n => L (v n)) atTop (𝓝 (L u))

/-- The conjugate exponent, written explicitly to expose its real power. -/
def conjugate (p : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (p.toReal / (p.toReal - 1))

/-- Exactly the hypotheses of the assigned subendpoint assertion. -/
def Hypotheses {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ℝ → ℝ)
    (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ) : Prop :=
  1 < p ∧ p ≠ ∞ ∧ Continuous g ∧ Monotone g ∧ UpperGrowth p g ∧
    WeaklyConverges μ p v u ∧
    limsup (fun n => ∫ x, primitive g (v n x) ∂μ) atTop ≤
      ∫ x, primitive g (u x) ∂μ

/-- All the integrals in the energy argument have their intended integrable meaning. -/
def GrowthIntegrability : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ g : ℝ → ℝ, Continuous g → Monotone g → UpperGrowth p g →
    ∀ u : Lp ℝ p μ,
      MemLp (fun x => g (u x)) (conjugate p) μ ∧
      Integrable (fun x => primitive g (u x)) μ

def RemainderNonnegative : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → Monotone g → ∀ a b : ℝ, 0 ≤ remainder g a b

/-- This scalar assertion does not presuppose boundedness of the scalar sequence. -/
def ScalarImageConvergence : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → Monotone g → ∀ (a : ℕ → ℝ) (b : ℝ),
    Tendsto (fun n => remainder g (a n) b) atTop (𝓝 0) →
      Tendsto (fun n => g (a n)) atTop (𝓝 (g b))

def ScalarStrictConvergence : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → StrictMono g → ∀ (a : ℕ → ℝ) (b : ℝ),
    Tendsto (fun n => remainder g (a n) b) atTop (𝓝 0) →
      Tendsto a atTop (𝓝 b)

/-- Establish L¹ convergence of the nonnegative remainder before passing to measure. -/
def RemainderConvergence : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ℝ → ℝ)
    (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ), Hypotheses μ p g v u →
    (∀ n, Integrable (fun x => remainder g (v n x) (u x)) μ) ∧
      Tendsto (fun n => ∫ x, remainder g (v n x) (u x) ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => remainder g (v n x) (u x)) 1 μ)
        atTop (𝓝 0)

/-- The full-sequence nonlinear image converges in measure, then in every lower Lq. -/
def ImageSubendpoint : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ℝ → ℝ)
    (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ), Hypotheses μ p g v u →
    TendstoInMeasure μ (fun n x => g (v n x)) atTop (fun x => g (u x)) ∧
      ∀ q : ℝ≥0∞, 1 ≤ q → q < conjugate p →
        (∀ n, MemLp (fun x => g (v n x)) q μ) ∧ MemLp (fun x => g (u x)) q μ ∧
        Tendsto (fun n => eLpNorm (fun x => g (v n x) - g (u x)) q μ)
          atTop (𝓝 0)

/-- Strict increase gives convergence of the original sequence, at every lower exponent. -/
def StrictSubendpoint : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ℝ → ℝ)
    (v : ℕ → Lp ℝ p μ) (u : Lp ℝ p μ), Hypotheses μ p g v u → StrictMono g →
    TendstoInMeasure μ (fun n x => v n x) atTop (fun x => u x) ∧
      ∀ q : ℝ≥0∞, 1 ≤ q → q < p →
        (∀ n, MemLp (v n) q μ) ∧ MemLp u q μ ∧
        Tendsto (fun n => eLpNorm (fun x => v n x - u x) q μ) atTop (𝓝 0)

end ExpandedFA.PartIV.ConvexEnergySubendpoint.Spec
