import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import Mathlib.Topology.Instances.Real.Lemmas

/-! K03.15.rs_existence, paper.tex:3696–3709. The original strict endpoint
partitions, arbitrary closed-cell tags, and actual values of the BV integrator
are retained. No continuity or one-sided normalization of the integrator is
assumed. The singleton interval and zero variation are included. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsExistence
open _root_.SingleVariableAnalysis.Riemann

/-- Unrestricted mesh convergence, using exactly the upstream tagged sums. -/
def meshLimit {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (a b : ℝ) (f : ℝ → E) (α : ℝ → ℝ) (I : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ P : PartitionData a b,
      Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue P < δ →
      ∀ t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
        ‖Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue P t f α - I‖ < ε

/-- The usual supremum norm on the specified compact interval. -/
noncomputable def supNorm {E : Type*} [NormedAddCommGroup E]
    (a b : ℝ) (f : ℝ → E) : ℝ := sSup ((fun x => ‖f x‖) '' Set.Icc a b)

/-- Real-valued existence, the variation bound, and convergence of all fine
mesh tagged sums to the same refinement integral. -/
def realExistence : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ),
  ContinuousOn f (Set.Icc a b) →
  Specs.SingleVariableAnalysis.Ch15.Variation.boundedVariationValue α a b →
  ∃ I : ℝ,
    Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I ∧
    ‖I‖ ≤ supNorm a b f *
      (Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue α a b).toReal ∧
    meshLimit a b f α I

/-- Complex values use real increments of the real BV integrator. -/
def complexExistence : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f : ℝ → ℂ) (α : ℝ → ℝ),
  ContinuousOn f (Set.Icc a b) →
  Specs.SingleVariableAnalysis.Ch15.Variation.boundedVariationValue α a b →
  ∃ I : ℂ,
    Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I ∧
    ‖I‖ ≤ supNorm a b f *
      (Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue α a b).toReal ∧
    meshLimit a b f α I

end Specs.SingleVariableAnalysis.Ch15.RsExistence
