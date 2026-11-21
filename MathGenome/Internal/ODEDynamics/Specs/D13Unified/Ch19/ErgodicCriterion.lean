import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! Independent types for Corollary d13:19:ergodic-criterion in paper.tex.
The full-measure convergence set is quantified separately for each observable.
Preservation is supplied separately from the zero-one and mixing predicates;
no inverse, completed space, or topological assumption on X is imposed. -/
namespace Specs.D13Unified.Ch19.ErgodicCriterion
noncomputable section
open MeasureTheory Filter
open scoped Topology
universe u

/-- The real and complex formulations use the same canonical averages. -/
def ergodic_criterionStatement (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    (MeasureDefinitions.IsErgodic T μ ↔
      ∀ f : X → 𝕜, Integrable f μ → ∀ᵐ x ∂μ,
        Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
          atTop (𝓝 (∫ y, f y ∂μ)))

def real_ergodic_criterionStatement : Prop := ergodic_criterionStatement.{u} ℝ

def complex_ergodic_criterionStatement : Prop := ergodic_criterionStatement.{u} ℂ

/-- Preimage invariance modulo null sets persists under every nonnegative iterate. -/
def invariantModNull_iterateStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
    MeasureDefinitions.PreservesMeasure T μ → ∀ E : Set X,
    MeasureDefinitions.InvariantModNull T μ E → ∀ n : ℕ,
      MeasureDefinitions.InvariantModNull (T^[n]) μ E

def mixing_implies_ergodicStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    MeasureDefinitions.IsMixing T μ → MeasureDefinitions.IsErgodic T μ

end
end Specs.D13Unified.Ch19.ErgodicCriterion
