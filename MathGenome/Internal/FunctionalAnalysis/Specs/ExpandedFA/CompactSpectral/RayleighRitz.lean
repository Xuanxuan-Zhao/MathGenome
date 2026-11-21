import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.PositiveMinMax
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Independent specification of fa2:p2:ritz-approximation (paper.tex 10851ff).
The index k below represents the manuscript's k+1. Trial spaces may be infinite
 dimensional. Complete multiplicity-counting positive lists supply zero padding. -/
noncomputable section
universe u v
namespace ExpandedFA.CompactSpectral.RayleighRitz.Spec
open Filter
open scoped Topology InnerProductSpace
open PositiveMinMax.Spec

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

structure TrialSequence (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  space : ℕ → Submodule 𝕜 H
  closed : ∀ n, IsClosed (space n : Set H)
  increasing : Monotone space
  dense : Dense (⋃ n, (space n : Set H))

instance [CompleteSpace H] (V : TrialSequence 𝕜 H) (n : ℕ) :
    CompleteSpace (V.space n) := (V.closed n).completeSpace_coe

def compression (T : H →L[𝕜] H) (U : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] : U →L[𝕜] U :=
  U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL

def extendedCompression (T : H →L[𝕜] H) (U : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] : H →L[𝕜] H :=
  U.starProjection ∘L T ∘L U.starProjection

/-- The whole positive spectral list, including its expansion, eigenspace
multiplicities and all the kernel, specifies the ordered eigenvalues. -/
def EigenvalueSequence (T : H →L[𝕜] H) (μ : ℕ → ℝ) : Prop :=
  ∃ (I : Set ℕ) (e : I → H) (a : I → ℝ),
    PositiveSpectralList T I e a ∧ μ = paddedValue I a

def Principle : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), T.IsPositive →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ V : TrialSequence 𝕜 H,
    ∃ (μ : ℕ → ℝ) (ν : ℕ → ℕ → ℝ),
      EigenvalueSequence T μ ∧
      (∀ n, EigenvalueSequence (compression T (V.space n)) (ν n)) ∧
      (∀ k, Admissible 𝕜 H k → CourantFischerAt T k (μ k)) ∧
      (Function.Injective T → ∀ k, Admissible 𝕜 H k → ReciprocalAt T k (μ k)) ∧
      (∀ n k, 0 ≤ ν n k ∧ ν n k ≤ ν (n+1) k ∧ ν (n+1) k ≤ μ k) ∧
      (∀ n k, |ν n k - μ k| ≤ ‖extendedCompression T (V.space n) - T‖) ∧
      Tendsto (fun n => ‖extendedCompression T (V.space n) - T‖) atTop (𝓝 0) ∧
      (∀ k, Tendsto (fun n => ν n k) atTop (𝓝 (μ k)))

end ExpandedFA.CompactSpectral.RayleighRitz.Spec
