import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.GraphFractionalTransport
import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Localization

/-! One-chart forward estimate in paper.tex:2574–2586. All norms of the
localized pullback below use whole tangential space. The cutoff carries only
smoothness, compact support, and the specified geometric support condition. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace P102.Trace.BoundaryChartLocalization
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry

def surfaceMeasure {m : ℕ} (Ω : Set (Ambient m)) : Measure (Ambient m) :=
  (μHE[m] : Measure (Ambient m)).restrict (frontier Ω)

def chartGraph {m : ℕ} {Ω : Set (Ambient m)} (C : BoundaryChart Ω) :
    P102.U4.Space m → Ambient m :=
  GraphFractionalTransport.graphMap C.frame C.graphFunction

/-- The representative is explicitly zero off the full tangential chart base. -/
def localizedPullback {m : ℕ} {Ω : Set (Ambient m)} (C : BoundaryChart Ω)
    (χ : Ambient m → ℝ) {𝕜 : Type*} [RCLike 𝕜] (g : Ambient m → 𝕜)
    (x : P102.U4.Space m) : 𝕜 := by
  classical
  exact if x ∈ ball C.center C.radius then χ (chartGraph C x) • g (chartGraph C x) else 0

namespace Expected

/-- The constant is independent of both the scalar field and representative.
No connectedness, trace, or finiteness of fractional energy is assumed. -/
def LocalizedEstimate : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (Ω : Set (Ambient m)), IsLipschitzOpen Ω →
    ∀ (C : BoundaryChart Ω) (r a : ℝ),
      0 < r → r < C.radius → 0 < a → a < C.height →
      ∀ χ : Ambient m → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        tsupport χ ⊆ chartImage C.frame C.graphFunction C.center r a →
        ∀ (s : ℝ), 0 < s → s < 1 → ∀ (p : ℝ≥0∞), 1 ≤ p → p < ∞ →
          ∃ K : ℝ≥0, 0 < K ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (g : Ambient m → 𝕜),
            MemLp g p (surfaceMeasure Ω) →
            MemLp (localizedPullback C χ g) p volume ∧
            MeasuredFractional.metricNorm m volume s p (localizedPullback C χ g) ≤
              (K : ℝ≥0∞) * MeasuredFractional.metricNorm m (surfaceMeasure Ω) s p g

def RepresentativeIndependence : Prop :=
  ∀ (m : ℕ) (Ω : Set (Ambient m)) (C : BoundaryChart Ω)
    (χ : Ambient m → ℝ) (𝕜 : Type) [RCLike 𝕜] (g h : Ambient m → 𝕜),
      g =ᵐ[surfaceMeasure Ω] h →
        localizedPullback C χ g =ᵐ[volume] localizedPullback C χ h

end Expected
end P102.Trace.BoundaryChartLocalization
