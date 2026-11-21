import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions

/-! Purely algebraic composition theorem from paper.tex:10428–10457 and
10620–10651. No topology, completeness, or finite ambient dimension is assumed. -/

namespace ExpandedFA.Fredholm.AlgebraicIndexAdditivitySpec
universe u v w z

def CompositionFiniteIndex : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module 𝕜 X] [Module 𝕜 Y] [Module 𝕜 Z]
    (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] Z),
    DefinitionsSpec.IsAlgebraicFiniteIndexValue T →
    DefinitionsSpec.IsAlgebraicFiniteIndexValue S →
    DefinitionsSpec.IsAlgebraicFiniteIndexValue (S.comp T)

def IndexAdditivity : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module 𝕜 X] [Module 𝕜 Y] [Module 𝕜 Z]
    (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] Z)
    (hT : DefinitionsSpec.IsAlgebraicFiniteIndexValue T)
    (hS : DefinitionsSpec.IsAlgebraicFiniteIndexValue S)
    (hST : DefinitionsSpec.IsAlgebraicFiniteIndexValue (S.comp T)),
    DefinitionsSpec.algebraicIndexValue (S.comp T) hST =
      DefinitionsSpec.algebraicIndexValue S hS + DefinitionsSpec.algebraicIndexValue T hT

end ExpandedFA.Fredholm.AlgebraicIndexAdditivitySpec
