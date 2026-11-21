import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.CompactNonzeroSpectrum

/-! The full Riesz--Schauder theorem, paper.tex:10328–10341.
Compact closure is in the original normed space. In particular there is
no completeness assumption. The RCLike formulation includes both real
and complex spaces; its spectral clause strengthens the required complex case.
The previously specified decomposition includes bounded complementary
projections, nilpotence on the kernel, and a bounded inverse on the range. -/
namespace ExpandedFA.Fredholm.RieszSchauderSpec

universe u v
variable {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

def FredholmAlternative : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    (Function.Injective (ContinuousLinearMap.id 𝕂 E - K) ↔
      Function.Surjective (ContinuousLinearMap.id 𝕂 E - K))

def BoundedInverse : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    Function.Bijective (ContinuousLinearMap.id 𝕂 E - K) →
    ∃ e : E ≃L[𝕂] E, ∀ x, e x = (ContinuousLinearMap.id 𝕂 E - K) x

/-- All normed-space conclusions for a specified compact bounded operator.
The generalized-eigenspace clause uses the union of all positive power
kernels, so it asserts finite algebraic multiplicity, not just finite
geometric multiplicity. -/
def Conclusion (K : E →L[𝕂] E) : Prop :=
  let A := ContinuousLinearMap.id 𝕂 E - K
  FiniteDimensional 𝕂 A.toLinearMap.ker ∧
  IsClosed (A.toLinearMap.range : Set E) ∧
  CompactDefectStabilizationSpec.FullConclusion K ∧
  (Function.Injective A ↔ Function.Surjective A) ∧
  (Function.Bijective A → ∃ e : E ≃L[𝕂] E, ∀ x, e x = A x) ∧
  CompactNonzeroSpectrumSpec.SpectralConclusion K

def BoundedRieszSchauder : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap → Conclusion K

/-- Starting with a compact algebraic linear map requires no additional
boundedness assumption: the bounded representative is the same linear map.
All conclusions therefore concern the original operator and space. -/
def LinearRieszSchauder : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →ₗ[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K →
    ∃ Kb : E →L[𝕂] E, Kb.toLinearMap = K ∧ Conclusion Kb

end ExpandedFA.Fredholm.RieszSchauderSpec
