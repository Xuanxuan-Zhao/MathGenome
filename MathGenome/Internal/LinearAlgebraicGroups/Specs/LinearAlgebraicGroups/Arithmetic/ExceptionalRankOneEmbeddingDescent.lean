import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralFibreReductivity
import Mathlib.FieldTheory.SeparableClosure

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalRankOneEmbeddingDescent

open AdjointRepresentation (GroupPoints)
open IntegralFibreReductivity (rankOnePoints)
open IntegralRootRelations (upper lower)
open RootGroups (AdditiveLine rootPoint)

noncomputable section

/-- The two marked copies of the standard rank-one group and their scalar comparison. -/
structure MatrixComparison (F K : Type u) [Field F] [Field K] [Algebra F K] where
  ground : AffineAlgebraicGroup F
  extended : AffineAlgebraicGroup K
  groundMatrices : (groupPointsFunctor F).obj ground.val ≅ rankOnePoints F
  extendedMatrices : (groupPointsFunctor K).obj extended.val ≅ rankOnePoints K
  scalarIso : extended.val ≅ (groupBaseChange F K).obj ground.val
  scalarMatrices : ∀ (R : TestAlgebra K) (m : Matrix.SpecialLinearGroup (Fin 2) R),
    groundMatrices.hom.app ((restrictTestAlgebra F K).obj R)
      (baseChangePoint F K ground.val.X R
        (extendedMatrices.inv.app R m ≫ scalarIso.hom.hom.hom)) = m

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- Evaluate the specified geometric embedding and view the result over the ground field. -/
def MatrixComparison.embeddedPoint (J : MatrixComparison F K) {G : AffineAlgebraicGroup F}
    (i : J.extended.val ⟶ (groupBaseChange F K).obj G.val) (R : TestAlgebra K)
    (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    GroupPoints G.val ((restrictTestAlgebra F K).obj R) :=
  baseChangePoint F K G.val.X R (J.extendedMatrices.inv.app R m ≫ i.hom.hom)

/-- A closed embedding of split rank one whose two elementary maps are defined
over the ground field descends to a closed embedding with those elementary maps. -/
def DescendMatrixEmbedding : Prop :=
  ∀ (F : Type u) [Field F] (G : AffineAlgebraicGroup F)
    (J : MatrixComparison F (SeparableClosure F))
    (i : J.extended.val ⟶ (groupBaseChange F (SeparableClosure F)).obj G.val),
    IsClosedImmersion i.hom.hom.left →
    ∀ (A B : AdditiveLine F) (x : A.group ⟶ G.val) (y : B.group ⟶ G.val),
      (∀ (R : TestAlgebra (SeparableClosure F)) (t : R),
        J.embeddedPoint i R (upper t) =
          rootPoint x ((restrictTestAlgebra F (SeparableClosure F)).obj R) t) →
      (∀ (R : TestAlgebra (SeparableClosure F)) (t : R),
        J.embeddedPoint i R (lower t) =
          rootPoint y ((restrictTestAlgebra F (SeparableClosure F)).obj R) t) →
      ∃ j : J.ground.val ⟶ G.val, IsClosedImmersion j.hom.hom.left ∧
        J.scalarIso.hom ≫ (groupBaseChange F (SeparableClosure F)).map j = i ∧
        (∀ (R : TestAlgebra F) (t : R),
          J.groundMatrices.inv.app R (upper t) ≫ j.hom.hom = rootPoint x R t) ∧
        (∀ (R : TestAlgebra F) (t : R),
          J.groundMatrices.inv.app R (lower t) ≫ j.hom.hom = rootPoint y R t)

end

end LinearAlgebraicGroups.Specs.ExceptionalRankOneEmbeddingDescent
