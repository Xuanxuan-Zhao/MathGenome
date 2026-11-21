import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.DomainConjugateIdentities
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12ConvexClosure

/-! Closure assertion of `fa2:p1:infconv-domain-closure`.
The algebraic identities and proper convexity are separate accepted upstream
obligations. These statements retain the actual continuous dual, the original
proper convex lower semicontinuous functions, their common finite point, and
reflexivity through surjectivity of canonical evaluation. All domains mean
finite real values. No equality before closure or minimizer is assumed.
-/
namespace ExpandedFA.InfimalConvolution.ConjugateDomainClosure.Spec

open scoped Pointwise
open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates.Spec
open ExpandedFA.InfimalConvolution.DomainConjugateIdentities.Spec

noncomputable def conjugateSumDomain (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ ψ : ExtendedFunction E) : Set (E →L[ℝ] ℝ) :=
  {f | ∃ r : ℝ, ConvexConjugateValue E (fun x => φ x + ψ x) f = (r : EReal)}

noncomputable def sumConjugateDomains (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ ψ : ExtendedFunction E) : Set (E →L[ℝ] ℝ) :=
  {f | ∃ r : ℝ, ConvexConjugateValue E φ f = (r : EReal)} +
  {g | ∃ s : ℝ, ConvexConjugateValue E ψ g = (s : EReal)}

/-- The displayed equality of norm closures in E′. -/
def NormDomainClosure : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E →
    ∀ (φ ψ : ExtendedFunction E), Regular E φ → Regular E ψ →
    (ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue E φ ∩
      ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue E ψ).Nonempty →
    closure (conjugateSumDomain E φ ψ) = closure (sumConjugateDomains E φ ψ)

/-- Both domains are convex; thus their weak closures equal their norm
closures, and the two weak closures are equal as well. The weak topology is
σ(E′,E′′), using the native norm-continuous bidual. -/
def WeakDomainClosures : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E →
    ∀ (φ ψ : ExtendedFunction E), Regular E φ → Regular E ψ →
    (ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue E φ ∩
      ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue E ψ).Nonempty →
    let A := conjugateSumDomain E φ ψ
    let B := sumConjugateDomains E φ ψ
    let τnorm := (inferInstance : TopologicalSpace (E →L[ℝ] ℝ))
    let τ := ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue ℝ
      (E →L[ℝ] ℝ) ((E →L[ℝ] ℝ) →L[ℝ] ℝ)
      (topDualPairing ℝ (E →L[ℝ] ℝ))
    Convex ℝ A ∧ Convex ℝ B ∧
      @closure _ τ A = @closure _ τnorm A ∧ @closure _ τ B = @closure _ τnorm B ∧
      @closure _ τ A = @closure _ τ B

end ExpandedFA.InfimalConvolution.ConjugateDomainClosure.Spec
