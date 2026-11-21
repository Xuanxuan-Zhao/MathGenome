import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.Rellich
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.ZeroGradient

/-! Mean-zero Poincaré, paper.tex:1937–1958, with the Euclidean
weak gradient required by the section convention at 1708–1711.
Preconnectedness includes the trivial empty-domain case. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace P102.Sobolev.MeanZeroPoincare
open P102.U4

/-- Integral average; inverse zero gives zero on the empty domain. -/
def average {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (f : Space d → 𝕜) : 𝕜 :=
  (volume (Ω : Set (Space d))).toReal⁻¹ • ∫ x in Ω, f x

namespace Expected

def Inequality : Prop :=
  ∀ (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    IsPreconnected (Ω : Set (Space (m + 1))) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : U4.Sobolev 𝕜 Ω 1 p,
      (eLpNorm (fun x => sobolevUnderlying u x - average Ω (sobolevUnderlying u)) p
        (volume.restrict (Ω : Set (Space (m + 1))))).toReal ≤
      C * (eLpNorm (weakGradientOn u) p
        (volume.restrict (Ω : Set (Space (m + 1))))).toReal

end Expected
end P102.Sobolev.MeanZeroPoincare
