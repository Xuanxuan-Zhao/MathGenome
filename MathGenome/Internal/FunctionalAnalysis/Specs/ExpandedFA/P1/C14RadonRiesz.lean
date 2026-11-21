import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12BoundedSequences

/-!
Independent statements for Proposition fa2:p1:c14:radon-riesz (paper.tex
2942–2946). The weak topology is σ(E,E′) for the continuous scalar-linear
dual of the displayed norm. The real limsup is well behaved here because
weakly convergent sequences are norm bounded. Neither completeness nor
nontriviality nor a nonzero limit is required.
-/
namespace ExpandedFA.P1.C14RadonRiesz.Spec

universe u v
open Filter
open scoped Topology
noncomputable section

/-- Weak convergence and the upper limit bound imply norm convergence. -/
def RadonRiesz : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
    ∀ (s : ℕ → E) (x : E),
    Tendsto s atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) →
    limsup (fun n => ‖s n‖) atTop ≤ ‖x‖ →
    Tendsto s atTop (𝓝 x)

/-- In particular, convergence of the norms to the norm of the weak limit
gives convergence in the original norm topology. -/
def RadonRieszOfNormConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
    ∀ (s : ℕ → E) (x : E),
    Tendsto s atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) →
    Tendsto (fun n => ‖s n‖) atTop (𝓝 ‖x‖) →
    Tendsto s atTop (𝓝 x)

end
end ExpandedFA.P1.C14RadonRiesz.Spec
