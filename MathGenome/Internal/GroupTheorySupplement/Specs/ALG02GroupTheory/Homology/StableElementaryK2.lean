import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.StableSteinberg
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.UniversalCentral

namespace ALG02GroupTheory.StableElementaryK2.Spec

open Extensions.StableSteinberg.Spec (Elementary Steinberg K₂ toElementary)
open Extensions.UniversalCentral.Spec (freePresentation)
open Extensions.CentralPresentation.Spec (PresentationGroup projection kernelInclusion)
open IntegralBar (homology)
open HopfFormula (PresentationQuotient toKernelQuotient)
open BarProjectionKernel (KernelQuotient)

universe u

/-- The classical kernel of the stable Steinberg map is second integral homology.
The isomorphism is the Hopf isomorphism followed by the restriction of the
comparison over the stable elementary group. -/
def K2HomologyIdentification : Prop :=
  ∀ (R : Type u) [Ring R],
    let P := freePresentation (Elementary R)
    ∃ (e : Multiplicative (homology (Elementary R) 2) ≃* K₂ R)
      (comparison : PresentationGroup P ≃* Steinberg R)
      (hopf : Multiplicative (homology (Elementary R) 2) ≃* PresentationQuotient P.inl.range)
      (d : Multiplicative (homology (Elementary R) 2) →* KernelQuotient P),
      toElementary.comp comparison.toMonoidHom = projection P ∧
      FiveTerm.Spec.IsSignedTransgression P d ∧
      ∀ x, toKernelQuotient P (hopf x) = d x ∧
        (e x).val = comparison (kernelInclusion P (hopf x))

end ALG02GroupTheory.StableElementaryK2.Spec
