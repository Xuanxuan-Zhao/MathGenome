import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.CcDensityEuclidean
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Independent statements of paper.tex:3783–3805. Smoothness is real smoothness
for both real and complex scalar functions. The Lp space uses the completed
Euclidean Lebesgue measure and the ordinary almost-everywhere quotient. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace Specs.D11.Ch11.SmoothDensity
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

/-- Smooth functions with genuinely compact support approximate every finite-p
ordinary Lp class, including p = 1 and both real and complex scalars. -/
def smooth_density : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    letI := lebesgueSpace_value d
    ∀ f : Lp 𝕜 p (lebesgue_value d), ∀ ε : ℝ, 0 < ε →
      ∃ g : Point d → 𝕜, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        ∃ hg : MemLp g p (lebesgue_value d), ‖f - hg.toLp g‖ < ε

/-- Compact support is contained in U, rather than merely vanishing outside U.
The compact set may be empty. Functions are defined on all of Euclidean space,
so their restriction to U is an element of C_c^∞(U). -/
def smooth_cutoff : Prop :=
  ∀ (d : ℕ) [NeZero d] (K U : Set (Point d)),
    IsCompact K → IsOpen U → K ⊆ U →
      ∃ ψ : Point d → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ U ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
        EqOn ψ (fun _ => 1) K

end Specs.D11.Ch11.SmoothDensity
