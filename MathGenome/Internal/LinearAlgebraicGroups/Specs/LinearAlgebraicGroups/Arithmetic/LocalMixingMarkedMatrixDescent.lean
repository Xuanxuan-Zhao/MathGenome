import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralFibreReductivity

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingMarkedMatrixDescent

open CharacterDescent (Cocharacter)
open GeneralLinearStructure (SpecialMatrixPoints)
open IntegralFibreReductivity (rankOnePoints)
open IntegralRootRelations (upper lower diagonal)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open RootGroups (AdditiveLine rootPoint)
open StandardGroups (HopfOperations SLCoordinates determinantOneIdeal universalMatrix)
open Unipotent (Index)

noncomputable section

/-- Reindex a size-two determinant-one matrix by the common lifted index. -/
def liftMatrix {R : Type u} [CommRing R] (x : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup (Index.{u} 2) R :=
  ⟨x.val.submatrix Equiv.ulift Equiv.ulift,
    (Matrix.det_submatrix_equiv_self Equiv.ulift x.val).trans x.property⟩

/-- Descend an injective determinant-one point map whose elementary and diagonal
marks are defined over the ground field. -/
def MarkedMatrixDescent : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (A₀ : AdditiveLine F) (A : AdditiveLine K),
    let E := groupBaseChange F K
    ∀ (j : E.obj A₀.group ≅ A.group) (e : MultiplicativeComparison F K),
      (∀ (R : TestAlgebra K) (z : R),
        baseChangePoint F K A₀.group.X R (rootPoint j.inv R z) =
          rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) z) →
      PreservesUnits e →
      ∀ (yPlus yMinus : A₀.group ⟶ G.val) (C : Cocharacter G.val),
        IsClosedImmersion yPlus.hom.hom.left → IsClosedImmersion yMinus.hom.hom.left →
        ∀ m : rankOnePoints K ⟶ (groupPointsFunctor K).obj (E.obj G.val),
          (∀ R : TestAlgebra K, Function.Injective (m.app R)) →
          (∀ (R : TestAlgebra K) (z : R),
            m.app R (upper z) = rootPoint (j.inv ≫ E.map yPlus) R z) →
          (∀ (R : TestAlgebra K) (z : R),
            m.app R (lower z) = rootPoint (j.inv ≫ E.map yMinus) R z) →
          (∀ (R : TestAlgebra K) (v : Rˣ),
            m.app R (diagonal v) = cocharacterPoint (e.hom ≫ E.map C) R v) →
          ∃ operations : HopfOperations F (SLCoordinates F (Index.{u} 2)),
            let H := @StandardGroups.spectrum F _ (SLCoordinates F (Index.{u} 2))
              _ operations.hopf inferInstance
            ∃ (matrix : SpecialMatrixPoints H 2) (f : H.val ⟶ G.val),
              IsClosedImmersion f.hom.hom.left ∧
              (∀ (R : TestAlgebra F) (a : SLCoordinates F (Index.{u} 2) →ₐ[F] R),
                let p : Points H.val.X R := (testSpec F).map (CommAlgCat.ofHom a).op
                let x : Matrix.SpecialLinearGroup (Index.{u} 2) R := matrix.hom.app R p
                let q := Ideal.Quotient.mkₐ F (determinantOneIdeal F (Index.{u} 2))
                x.val = (a.comp q).mapMatrix (universalMatrix F (Index.{u} 2))) ∧
              (∀ (R : TestAlgebra F) (z : R),
                (matrix.inv.app R (liftMatrix (upper z)) : Points H.val.X R) ≫ f.hom.hom =
                  rootPoint yPlus R z) ∧
              (∀ (R : TestAlgebra F) (z : R),
                (matrix.inv.app R (liftMatrix (lower z)) : Points H.val.X R) ≫ f.hom.hom =
                  rootPoint yMinus R z) ∧
              (∀ (R : TestAlgebra F) (v : Rˣ),
                (matrix.inv.app R (liftMatrix (diagonal v)) : Points H.val.X R) ≫ f.hom.hom =
                  cocharacterPoint C R v) ∧
              ∀ (R : TestAlgebra K) (x : Matrix.SpecialLinearGroup (Fin 2) R),
                let p : Points H.val.X ((restrictTestAlgebra F K).obj R) :=
                  matrix.inv.app ((restrictTestAlgebra F K).obj R) (liftMatrix x)
                baseChangePoint F K G.val.X R (m.app R x) = p ≫ f.hom.hom

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingMarkedMatrixDescent
