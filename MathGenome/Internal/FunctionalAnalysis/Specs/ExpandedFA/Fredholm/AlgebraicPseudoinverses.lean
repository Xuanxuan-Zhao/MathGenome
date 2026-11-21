import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.AlgebraicIndexAdditivity
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Algebraic pseudoinverses, paper.tex:10434–10464. No topology is imposed.
Finite rank always means finite-dimensional actual range. -/
namespace ExpandedFA.Fredholm.AlgebraicPseudoinversesSpec
universe u v w z

section TwoSpaces
/-- Every choice of the two complements yields the indicated generalized inverse
and precisely the projections along the chosen complements. -/
def ComplementConstruction : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y] [Module 𝕜 X] [Module 𝕜 Y],
  ∀ (T : X →ₗ[𝕜] Y) (X₀ : Submodule 𝕜 X) (C : Submodule 𝕜 Y)
    (hX : IsCompl T.ker X₀) (hY : IsCompl T.range C),
    ∃ S : Y →ₗ[𝕜] X,
      (T.comp S).comp T = T ∧ (S.comp T).comp S = S ∧
      S.comp T = X₀.projection T.ker hX.symm ∧
      T.comp S = T.range.projection C hY ∧
      LinearMap.id - S.comp T = T.ker.projection X₀ hX ∧
      LinearMap.id - T.comp S = C.projection T.range hY.symm

/-- Existence includes the zero spaces and maps, with no finiteness assumption. -/
def GeneralizedInverseExistence : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y] [Module 𝕜 X] [Module 𝕜 Y],
  ∀ T : X →ₗ[𝕜] Y, ∃ S : Y →ₗ[𝕜] X,
    (T.comp S).comp T = T ∧ (S.comp T).comp S = S ∧
    IsIdempotentElem (LinearMap.id - S.comp T) ∧
    IsIdempotentElem (LinearMap.id - T.comp S) ∧
    (LinearMap.id - S.comp T).range = T.ker ∧
    IsCompl T.range (LinearMap.id - T.comp S).range

def FiniteDefectCharacterization : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y] [Module 𝕜 X] [Module 𝕜 Y],
  ∀ T : X →ₗ[𝕜] Y,
    DefinitionsSpec.IsAlgebraicFiniteIndexValue T ↔
      ∃ S : Y →ₗ[𝕜] X,
        FiniteDimensional 𝕜 (LinearMap.id - S.comp T).range ∧
        FiniteDimensional 𝕜 (LinearMap.id - T.comp S).range

/-- For every generalized inverse the dimensions of its two defect projections
compute the algebraic index. -/
def DefectIndexFormula : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y] [Module 𝕜 X] [Module 𝕜 Y],
  ∀ (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] X),
    (T.comp S).comp T = T → (S.comp T).comp S = S →
    ∀ h : DefinitionsSpec.IsAlgebraicFiniteIndexValue T,
      FiniteDimensional 𝕜 (LinearMap.id - S.comp T).range ∧
      FiniteDimensional 𝕜 (LinearMap.id - T.comp S).range ∧
      DefinitionsSpec.algebraicIndexValue T h =
        (Module.finrank 𝕜 (LinearMap.id - S.comp T).range : ℤ) -
        (Module.finrank 𝕜 (LinearMap.id - T.comp S).range : ℤ)

def FiniteRankPerturbationFiniteness : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y] [Module 𝕜 X] [Module 𝕜 Y],
  ∀ (T D : X →ₗ[𝕜] Y), FiniteDimensional 𝕜 D.range →
    (DefinitionsSpec.IsAlgebraicFiniteIndexValue (T + D) ↔
      DefinitionsSpec.IsAlgebraicFiniteIndexValue T)

def FiniteRankPerturbationIndex : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y] [Module 𝕜 X] [Module 𝕜 Y],
  ∀ (T D : X →ₗ[𝕜] Y), FiniteDimensional 𝕜 D.range →
    ∀ (hT : DefinitionsSpec.IsAlgebraicFiniteIndexValue T)
      (hTD : DefinitionsSpec.IsAlgebraicFiniteIndexValue (T + D)),
      DefinitionsSpec.algebraicIndexValue (T + D) hTD =
        DefinitionsSpec.algebraicIndexValue T hT
end TwoSpaces

/-- The algebraic product law, including finiteness of both defects of a product. -/
def CompositionIndex : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module 𝕜 X] [Module 𝕜 Y] [Module 𝕜 Z]
    (T : X →ₗ[𝕜] Y) (U : Y →ₗ[𝕜] Z)
    (hT : DefinitionsSpec.IsAlgebraicFiniteIndexValue T)
    (hU : DefinitionsSpec.IsAlgebraicFiniteIndexValue U),
    ∃ hUT : DefinitionsSpec.IsAlgebraicFiniteIndexValue (U.comp T),
      DefinitionsSpec.algebraicIndexValue (U.comp T) hUT =
        DefinitionsSpec.algebraicIndexValue U hU + DefinitionsSpec.algebraicIndexValue T hT
end ExpandedFA.Fredholm.AlgebraicPseudoinversesSpec
