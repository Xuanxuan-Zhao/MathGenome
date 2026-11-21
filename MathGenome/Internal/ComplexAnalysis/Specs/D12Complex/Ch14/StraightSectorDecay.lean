import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularExhaustion
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The straight-sector estimate in paper.tex:2660–2669. The circular outer
boundary is excluded from all continuity and zero-boundary assumptions. -/
noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch14.StraightSectorDecay
open _root_.D12Complex

def sector_decay_type : Prop :=
  ∀ (θ R : ℝ) (u : ℂ → ℝ), 0 < θ → θ < 2 * Real.pi → 0 < R →
    HarmonicOn (CircularExhaustion.sector θ ∩ ball 0 R) u →
    ContinuousOn u (closure (CircularExhaustion.sector θ) ∩ ball 0 R) →
    (∀ z ∈ frontier (CircularExhaustion.sector θ) ∩ ball 0 R, u z = 0) →
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ∀ z ∈ CircularExhaustion.sector θ, ‖z‖ < r →
        |u z| ≤ C * ‖z‖ ^ (Real.pi / θ) ∧
        ‖gradient u z‖ ≤ C * ‖z‖ ^ (Real.pi / θ - 1)

end Specs.D12Complex.Ch14.StraightSectorDecay
