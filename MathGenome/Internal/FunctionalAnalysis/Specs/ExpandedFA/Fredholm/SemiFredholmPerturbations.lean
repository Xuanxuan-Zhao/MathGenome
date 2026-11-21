import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.ReducedMinimumModulus
import Mathlib.LinearAlgebra.Dimension.Basic

/-! Quantitative perturbation assertion of `fa2:p2:local-spectrum`.
Dimensions are extended natural numbers: their finite values are the usual
vector-space dimensions, and every infinite-dimensional space has value ∞.
The modulus is the upstream [0,∞]-valued infimum, including empty spheres. -/
noncomputable section
namespace ExpandedFA.Fredholm.SemiFredholmPerturbations.Spec
universe u v w
open scoped ENNReal

def Perturbation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (A B : H →L[𝕜] K),
    DefinitionsSpec.IsSemiFredholmValue A →
    (‖B‖₊ : ℝ≥0∞) < Hilbert.ReducedMinimumModulus.Spec.ReducedMinimumModulusValue 𝕜 H K A →
    DefinitionsSpec.IsSemiFredholmValue (A + B) ∧
      (Module.rank 𝕜 (A + B).ker).toENat ≤ (Module.rank 𝕜 A.ker).toENat ∧
      (Module.rank 𝕜 (K ⧸ (A + B).range)).toENat ≤
        (Module.rank 𝕜 (K ⧸ A.range)).toENat

end ExpandedFA.Fredholm.SemiFredholmPerturbations.Spec
