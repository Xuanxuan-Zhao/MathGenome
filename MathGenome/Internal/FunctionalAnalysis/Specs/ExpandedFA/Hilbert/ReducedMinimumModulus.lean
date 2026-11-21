import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.ClosedRangeEquivalences
import Mathlib.Basic.ENNReal.Inv

/-! The reduced minimum modulus in paper.tex, fa2:p2:closed-range.
The infimum is taken in [0,∞], so the empty unit sphere has infimum ∞.
No closed-range assumption is imposed on the adjoint equality. -/
noncomputable section
open scoped ENNReal NNReal
namespace ExpandedFA.Hilbert.ReducedMinimumModulus.Spec
universe u v w

def ReducedMinimumModulusType :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K], (H →L[𝕜] K) → ℝ≥0∞

def ReducedMinimumModulusValue : ReducedMinimumModulusType.{u, v, w} :=
  fun _ H _ _ _ _ _ _ T =>
    ⨅ (x : H) (_ : x ∈ T.ker.orthogonal) (_ : ‖x‖ = 1), (‖T x‖₊ : ℝ≥0∞)

def AdjointEquality : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ReducedMinimumModulusValue 𝕜 H K T =
      ReducedMinimumModulusValue 𝕜 K H (Adjoint.Spec.AdjointValue 𝕜 H K T)

def ZeroModulus : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K],
    ReducedMinimumModulusValue 𝕜 H K (0 : H →L[𝕜] K) = ⊤

abbrev ClosedRangeIffLowerBound := ClosedRangeEquivalences.Spec.ClosedRangeIffLowerBound.{u,v,w}
abbrev ClosedRangeAdjointIff := ClosedRangeEquivalences.Spec.ClosedRangeAdjointIff.{u,v,w}
abbrev ClosedRangeIdentities := ClosedRangeEquivalences.Spec.ClosedRangeIdentities.{u,v,w}
end ExpandedFA.Hilbert.ReducedMinimumModulus.Spec
