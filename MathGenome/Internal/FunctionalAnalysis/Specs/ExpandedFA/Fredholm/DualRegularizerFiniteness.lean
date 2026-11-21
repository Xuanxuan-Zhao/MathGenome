import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.DualSystems
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Independent statement of the finiteness and range clauses of
`fa2:p2:dual-regularization` (paper.tex:10386–10402).
The complex interface uses the shared dual-system data; a scalar-general
statement below covers both real and complex spaces, possibly incomplete. The pairings
are nondegenerate algebraic bilinear pairings, with no continuity assumption.
Cokernels are algebraic quotients by the actual operator ranges. -/
namespace ExpandedFA.Fredholm.DualRegularizerFinitenessSpec
universe u₁ v₁ u₂ v₂

variable {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
  [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
  [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂]

/-- Both original maps, their original norm topologies and both codimension
identities; no completeness or bound on either pairing is included. -/
def Conclusion (D₁ : DualSystemsSpec.DualSystemData X₁ Y₁)
    (D₂ : DualSystemsSpec.DualSystemData X₂ Y₂)
    (T : X₁ →L[ℂ] X₂) (U : Y₂ →L[ℂ] Y₁) : Prop :=
  FiniteDimensional ℂ T.toLinearMap.ker ∧
  FiniteDimensional ℂ U.toLinearMap.ker ∧
  IsClosed (T.toLinearMap.range : Set X₂) ∧
  IsClosed (U.toLinearMap.range : Set Y₁) ∧
  FiniteDimensional ℂ (X₂ ⧸ T.toLinearMap.range) ∧
  FiniteDimensional ℂ (Y₁ ⧸ U.toLinearMap.range) ∧
  (∀ f : X₂, f ∈ T.toLinearMap.range ↔
    ∀ y : Y₂, y ∈ U.toLinearMap.ker → D₂.pairing y f = 0) ∧
  (∀ g : Y₁, g ∈ U.toLinearMap.range ↔
    ∀ x : X₁, x ∈ T.toLinearMap.ker → D₁.pairing g x = 0) ∧
  Module.finrank ℂ (X₂ ⧸ T.toLinearMap.range) = Module.finrank ℂ U.toLinearMap.ker ∧
  Module.finrank ℂ (Y₁ ⧸ U.toLinearMap.range) = Module.finrank ℂ T.toLinearMap.ker

def RegularizerFiniteness : Prop :=
  ∀ (D₁ : DualSystemsSpec.DualSystemData X₁ Y₁)
    (D₂ : DualSystemsSpec.DualSystemData X₂ Y₂)
    (T : X₁ →L[ℂ] X₂) (U : Y₂ →L[ℂ] Y₁)
    (R : X₂ →L[ℂ] X₁) (V : Y₁ →L[ℂ] Y₂),
    (∀ x y, D₂.pairing y (T x) = D₁.pairing (U y) x) →
    (∀ f g, D₁.pairing g (R f) = D₂.pairing (V g) f) →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id ℂ X₁ - R.comp T).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id ℂ X₂ - T.comp R).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id ℂ Y₁ - U.comp V).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id ℂ Y₂ - V.comp U).toLinearMap →
    Conclusion D₁ D₂ T U

end ExpandedFA.Fredholm.DualRegularizerFinitenessSpec

/-! Scalar-general form, including the real case under the global convention.
Raw bilinear maps and explicit nondegeneracy agree with the existing complex
system data, without introducing another complex dual-system structure. -/
namespace ExpandedFA.Fredholm.DualRegularizerFinitenessSpec
universe u₁ v₁ u₂ v₂

variable {𝕂 : Type*} [RCLike 𝕂]
variable {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
  [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
  [NormedAddCommGroup Y₁] [NormedSpace 𝕂 Y₁]
  [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
  [NormedAddCommGroup Y₂] [NormedSpace 𝕂 Y₂]

/-- Both original maps, their original norm topologies and both codimension
identities; no completeness or bound on either pairing is included. -/
def BilinearConclusion (C₁ : Y₁ →ₗ[𝕂] X₁ →ₗ[𝕂] 𝕂)
    (C₂ : Y₂ →ₗ[𝕂] X₂ →ₗ[𝕂] 𝕂)
    (T : X₁ →L[𝕂] X₂) (U : Y₂ →L[𝕂] Y₁) : Prop :=
  FiniteDimensional 𝕂 T.toLinearMap.ker ∧
  FiniteDimensional 𝕂 U.toLinearMap.ker ∧
  IsClosed (T.toLinearMap.range : Set X₂) ∧
  IsClosed (U.toLinearMap.range : Set Y₁) ∧
  FiniteDimensional 𝕂 (X₂ ⧸ T.toLinearMap.range) ∧
  FiniteDimensional 𝕂 (Y₁ ⧸ U.toLinearMap.range) ∧
  (∀ f : X₂, f ∈ T.toLinearMap.range ↔
    ∀ y : Y₂, y ∈ U.toLinearMap.ker → C₂ y f = 0) ∧
  (∀ g : Y₁, g ∈ U.toLinearMap.range ↔
    ∀ x : X₁, x ∈ T.toLinearMap.ker → C₁ g x = 0) ∧
  Module.finrank 𝕂 (X₂ ⧸ T.toLinearMap.range) = Module.finrank 𝕂 U.toLinearMap.ker ∧
  Module.finrank 𝕂 (Y₁ ⧸ U.toLinearMap.range) = Module.finrank 𝕂 T.toLinearMap.ker

def BilinearRegularizerFiniteness : Prop :=
  ∀ (C₁ : Y₁ →ₗ[𝕂] X₁ →ₗ[𝕂] 𝕂)
    (C₂ : Y₂ →ₗ[𝕂] X₂ →ₗ[𝕂] 𝕂)
    (T : X₁ →L[𝕂] X₂) (U : Y₂ →L[𝕂] Y₁)
    (R : X₂ →L[𝕂] X₁) (V : Y₁ →L[𝕂] Y₂),
    (∀ x, (∀ y, C₁ y x = 0) → x = 0) →
    (∀ y, (∀ x, C₁ y x = 0) → y = 0) →
    (∀ x, (∀ y, C₂ y x = 0) → x = 0) →
    (∀ y, (∀ x, C₂ y x = 0) → y = 0) →
    (∀ x y, C₂ y (T x) = C₁ (U y) x) →
    (∀ f g, C₁ g (R f) = C₂ (V g) f) →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 X₁ - R.comp T).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 X₂ - T.comp R).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 Y₁ - U.comp V).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 Y₂ - V.comp U).toLinearMap →
    BilinearConclusion C₁ C₂ T U


end ExpandedFA.Fredholm.DualRegularizerFinitenessSpec

namespace ExpandedFA.Fredholm.DualRegularizerFinitenessSpec
universe u₁ v₁ u₂ v₂ w

/-- Fully quantified expected proposition for the shared complex interface. -/
def RegularizerFinitenessAll : Prop :=
  ∀ {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
    [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂],
    RegularizerFiniteness (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)

/-- Fully quantified expected proposition for either scalar field. -/
def BilinearRegularizerFinitenessAll : Prop :=
  ∀ {𝕂 : Type w} [RCLike 𝕂]
    {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
    [NormedAddCommGroup Y₁] [NormedSpace 𝕂 Y₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
    [NormedAddCommGroup Y₂] [NormedSpace 𝕂 Y₂],
    BilinearRegularizerFiniteness (𝕂 := 𝕂)
      (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)

end ExpandedFA.Fredholm.DualRegularizerFinitenessSpec
