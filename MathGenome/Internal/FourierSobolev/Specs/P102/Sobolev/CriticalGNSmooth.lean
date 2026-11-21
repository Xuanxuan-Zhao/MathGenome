import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalWhole

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace P102.Sobolev.CriticalGNSmoothExpected
open P102.U4

/-- The smooth compactly supported critical whole-space inequality, uniformly
in real and complex scalars. Finite NNReal exponents include every real
1 ≤ r ≤ q < ∞. The classical gradient uses the canonical Euclidean coordinates. -/
def Inequality : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (r q : ℝ≥0), 1 ≤ r → r ≤ q →
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] (f : Space d → 𝕜),
      ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm f q volume ≤ (C : ℝ≥0∞) *
        eLpNorm (fun x => (WithLp.toLp 2
          (fun i => fderiv ℝ f x (coordinateVector d i)) :
            EuclideanSpace 𝕜 (Fin d))) (d : ℝ≥0∞) volume ^ (1 - (r : ℝ) / q) *
        eLpNorm f r volume ^ ((r : ℝ) / q)
end P102.Sobolev.CriticalGNSmoothExpected
