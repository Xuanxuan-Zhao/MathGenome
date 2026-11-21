import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.MeanValueStrongPrinciple

/-! The converse assertion of paper.tex:2550–2555. The mean radii may
depend on the individual center; harmonicity is the shared C² coordinate
Laplacian predicate, with no extra regularity assumed. -/
noncomputable section

namespace Specs.D12Complex.Ch13.MeanValueConverse
open _root_.D12Complex

def continuous_local_circle_mean_harmonic_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsOpen U → ContinuousOn u U →
    LocalCircleMeanProperty U u → HarmonicOn U u

end Specs.D12Complex.Ch13.MeanValueConverse
