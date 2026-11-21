import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalWhole
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology ContDiff
namespace P102.Sobolev.CriticalGNApproximationExpected
open P102.U4

/-- Simultaneous approximation for the finite-exponent passage in U5-02.
The gradient is the Euclidean tuple of the actual classical coordinate derivatives. -/
def Approximation : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (r : ℝ≥0), 1 ≤ r →
    ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (d : ℝ≥0∞))]
      (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 (d : ℝ≥0∞)),
      MemLp (sobolevUnderlying u) r volume →
      ∃ f : ℕ → Space d → 𝕜,
        (∀ n, ContDiff ℝ 1 (f n) ∧ HasCompactSupport (f n)) ∧
        (∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (sobolevUnderlying u x))) ∧
        Tendsto (fun n => eLpNorm (fun x =>
          (WithLp.toLp 2 (fun i : Fin d => fderiv ℝ (f n) x (coordinateVector d i)) :
            EuclideanSpace 𝕜 (Fin d))) (d : ℝ≥0∞) volume)
          atTop (𝓝 (eLpNorm (weakGradient u) (d : ℝ≥0∞) volume)) ∧
        Tendsto (fun n => eLpNorm (f n) r volume)
          atTop (𝓝 (eLpNorm (sobolevUnderlying u) r volume))

end P102.Sobolev.CriticalGNApproximationExpected
