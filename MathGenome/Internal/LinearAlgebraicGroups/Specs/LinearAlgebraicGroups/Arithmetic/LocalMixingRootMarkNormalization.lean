import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralFibreReductivity

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingRootMarkNormalization

open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots)
open GeometricRadicals (IsReductive IsSplitTorus baseChangedSubgroup)
open IntegralFibreReductivity (rankOnePoints)
open IntegralRootRelations (upper lower diagonal)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine HasScalarAction rootPoint)
open Unipotent (baseChangedAlgebraicGroup)

noncomputable section

/-- Opposite absolute root marks over a finite Galois extension can be
normalized to descend together, preserving the marked diagonal. -/
def RootMarkNormalization : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T : ClosedSubgroup G.val)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left),
    let E := groupBaseChange F K
    let GK := baseChangedAlgebraicGroup K G
    let TK := baseChangedSubgroup K T hT
    IsReductive GK → IsSplitTorus TK.group → IsGeometricallyMaximal TK →
    ∀ (e : MultiplicativeComparison F K), PreservesUnits e →
    ∀ (χ : Character T.group),
      let b : Character TK.group := E.map χ ≫ e.inv
      b ∈ absoluteRoots TK →
      ∀ (A : AdditiveLine K) (xPlus xMinus : A.group ⟶ GK.val),
        IsClosedImmersion xPlus.hom.hom.left → IsClosedImmersion xMinus.hom.hom.left →
        HasScalarAction TK b xPlus → HasScalarAction TK b⁻¹ xMinus →
        ∀ (D : Cocharacter GK.val)
          (m : rankOnePoints K ⟶ (groupPointsFunctor K).obj GK.val),
          (∀ R : TestAlgebra K, Function.Injective (m.app R)) →
          (∀ (R : TestAlgebra K) (z : R), m.app R (upper z) = rootPoint xPlus R z) →
          (∀ (R : TestAlgebra K) (z : R), m.app R (lower z) = rootPoint xMinus R z) →
          (∀ (R : TestAlgebra K) (v : Rˣ), m.app R (diagonal v) = cocharacterPoint D R v) →
          ∃ (A₀ : AdditiveLine F) (j : E.obj A₀.group ≅ A.group)
            (yPlus yMinus : A₀.group ⟶ G.val),
            (∀ (R : TestAlgebra K) (z : R),
              baseChangePoint F K A₀.group.X R (rootPoint j.inv R z) =
                rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) z) ∧
            IsClosedImmersion yPlus.hom.hom.left ∧ IsClosedImmersion yMinus.hom.hom.left ∧
            let yPlusK := j.inv ≫ E.map yPlus
            let yMinusK := j.inv ≫ E.map yMinus
            HasScalarAction TK b yPlusK ∧ HasScalarAction TK b⁻¹ yMinusK ∧
            ∃ m' : rankOnePoints K ⟶ (groupPointsFunctor K).obj GK.val,
              (∀ R : TestAlgebra K, Function.Injective (m'.app R)) ∧
              (∀ (R : TestAlgebra K) (z : R), m'.app R (upper z) = rootPoint yPlusK R z) ∧
              (∀ (R : TestAlgebra K) (z : R), m'.app R (lower z) = rootPoint yMinusK R z) ∧
              (∀ (R : TestAlgebra K) (v : Rˣ),
                m'.app R (diagonal v) = cocharacterPoint D R v)

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingRootMarkNormalization
