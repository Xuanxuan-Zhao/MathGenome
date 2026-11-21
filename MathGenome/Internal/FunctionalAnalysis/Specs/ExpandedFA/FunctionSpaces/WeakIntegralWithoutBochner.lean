import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
The explicit counterexample in paper.tex:17089–17095. The canonical Part I
ℓ² has coordinates indexed by ℕ; index n means manuscript index n+1.
Scalars are ℝ or ℂ, and the dual consists of scalar-linear continuous maps.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
open ExpandedFA.P1.C01SequenceSpaces
universe u

namespace ExpandedFA.FunctionSpaces.WeakIntegralWithoutBochner

/-- The manuscript's e_n/n, with the positive coordinate convention. -/
def harmonicTerm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : SequenceLp 𝕜 2 :=
  lp.single 2 n (((n + 1 : ℕ) : 𝕜)⁻¹)

namespace Spec

/-- The weak integral is an actual ℓ² vector with the stated coordinates.
Every scalar evaluation is absolutely summable and integrable for counting
measure, and integration is represented by that vector. In contrast the
norm integral is infinite and the function fails the manuscript's L¹ simple
approximation definition of Bochner integrability. -/
def Counterexample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ I : SequenceLp 𝕜 2,
      (∀ n : ℕ, I n = ((n + 1 : ℕ) : 𝕜)⁻¹) ∧
      HasSum (harmonicTerm 𝕜) I ∧
      BochnerDefinitionsSpec.StrongMeasurableValue Measure.count (harmonicTerm 𝕜) ∧
      (∀ L : SequenceLp 𝕜 2 →L[𝕜] 𝕜,
        Summable (fun n => ‖L (harmonicTerm 𝕜 n)‖) ∧
        Integrable (fun n => L (harmonicTerm 𝕜 n)) Measure.count ∧
        L I = ∫ n, L (harmonicTerm 𝕜 n) ∂Measure.count) ∧
      (∀ n : ℕ, ‖harmonicTerm 𝕜 n‖ = ((n + 1 : ℕ) : ℝ)⁻¹) ∧
      ¬ Summable (fun n => ‖harmonicTerm 𝕜 n‖) ∧
      (∫⁻ n, ‖harmonicTerm 𝕜 n‖ₑ ∂Measure.count) = ∞ ∧
      ¬ BochnerDefinitionsSpec.BochnerIntegrableValue Measure.count (harmonicTerm 𝕜)

end Spec
end ExpandedFA.FunctionSpaces.WeakIntegralWithoutBochner
