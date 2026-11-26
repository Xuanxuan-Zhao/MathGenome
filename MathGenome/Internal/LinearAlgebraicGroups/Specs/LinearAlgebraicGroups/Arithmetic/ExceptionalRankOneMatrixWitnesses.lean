import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalRankOneMatrixWitnesses

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open GeneralLinearStructure (SpecialMatrixPoints)
open RootGroups (AdditiveLine rootPoint)
open IntegralRootRelations (upper lower diagonal)
open Unipotent (Index)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)

noncomputable section

variable {F : Type u} [Field F]

/-- Reindex the two-by-two matrices to the index of the standard group. -/
def liftMatrix {R : Type u} [CommRing R] :
    Matrix.SpecialLinearGroup (Fin 2) R ≃*
      Matrix.SpecialLinearGroup (Index.{u} 2) R where
  toFun m := ⟨Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm m.val,
    (Matrix.det_reindex_self Equiv.ulift.symm m.val).trans m.property⟩
  invFun m := ⟨Matrix.reindex Equiv.ulift Equiv.ulift m.val,
    (Matrix.det_reindex_self Equiv.ulift m.val).trans m.property⟩
  left_inv m := Subtype.ext ((Matrix.reindexRingEquiv R Equiv.ulift.symm).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((Matrix.reindexRingEquiv R Equiv.ulift.symm).apply_symm_apply m.val)
  map_mul' x y := Subtype.ext ((Matrix.reindexRingEquiv R Equiv.ulift.symm).map_mul x.val y.val)

/-- The common multiplicative group used in the cocharacter interface. -/
abbrev multiplicativeLine (F : Type u) [Field F] : GroupScheme F :=
  specGroup (DiagonalizableGroups.groupAlgebra F DiagonalizableGroups.IntegerCharacters)

abbrev pointHom {P Q : GroupScheme F} (f : P ⟶ Q) (R : TestAlgebra F)
    (p : GroupPoints P R) : GroupPoints Q R := p ≫ f.hom.hom

/-- The elementary groups and Weyl section in a marked presentation of the
size-two determinant-one functor. -/
structure Witnesses (A : AdditiveLine F) {J : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints J 2) where
  pos : ClosedSubgroup J.val
  neg : ClosedSubgroup J.val
  posCoord : A.group ≅ pos.group
  negCoord : A.group ≅ neg.group
  pos_matrix : ∀ (R : TestAlgebra F) (r : R),
    matrix.hom.app R (rootPoint (posCoord.hom ≫ pos.inclusion) R r) = liftMatrix (upper r)
  neg_matrix : ∀ (R : TestAlgebra F) (r : R),
    matrix.hom.app R (rootPoint (negCoord.hom ≫ neg.inclusion) R r) = liftMatrix (lower r)
  pos_membership : ∀ (R : TestAlgebra F) (p : GroupPoints J.val R),
    (∃ z : GroupPoints pos.group R, pointHom pos.inclusion R z = p) ↔
      let m := (matrix.hom.app R p).val
      m ⟨0⟩ ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨1⟩ ⟨0⟩ = 0
  neg_membership : ∀ (R : TestAlgebra F) (p : GroupPoints J.val R),
    (∃ z : GroupPoints neg.group R, pointHom neg.inclusion R z = p) ↔
      let m := (matrix.hom.app R p).val
      m ⟨0⟩ ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨0⟩ ⟨1⟩ = 0
  generates : ∀ (G : AffineAlgebraicGroup F) (i : J.val ⟶ G.val),
    IsClosedImmersion i.hom.hom.left → ∀ H : ClosedSubgroup G.val,
    (∃ f : pos.group ⟶ H.group, f ≫ H.inclusion = pos.inclusion ≫ i) →
    (∃ f : neg.group ⟶ H.group, f ≫ H.inclusion = neg.inclusion ≫ i) →
    ∃ f : J.val ⟶ H.group, f ≫ H.inclusion = i
  diag : Cocharacter J.val
  diag_matrix : ∀ (R : TestAlgebra F) (t : Rˣ),
    matrix.hom.app R (cocharacterPoint diag R t) = liftMatrix (diagonal t)
  weyl : 𝟙_ (SchemeOver F) ⟶ J.val.X
  weyl_matrix :
    (matrix.hom.app (CommAlgCat.of F F) (toUnit _ ≫ weyl)).val =
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).submatrix ULift.down ULift.down

/-- The witnesses exist in every marked affine algebraic presentation of the
size-two special linear point functor. -/
def MatrixWitnesses : Prop :=
  ∀ (F : Type u) [Field F] (A : AdditiveLine F) (J : AffineAlgebraicGroup F)
    (matrix : SpecialMatrixPoints J 2), Nonempty (Witnesses A matrix)

/-- Scalar extension with the matrix comparison and the additive and multiplicative
parameter comparisons. -/
def MatrixScalarExtension : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K]
    (A : AdditiveLine F) (B : AdditiveLine K) (J : AffineAlgebraicGroup F)
    (J' : AffineAlgebraicGroup K) (matrix : SpecialMatrixPoints J 2)
    (matrix' : SpecialMatrixPoints J' 2) (W : Witnesses A matrix),
    let E := groupBaseChange F K
    let restrict := restrictTestAlgebra F K
    ∃ (e : J'.val ≅ E.obj J.val) (a : B.group ≅ E.obj A.group)
      (m : multiplicativeLine K ≅ E.obj (multiplicativeLine F)),
      (∀ (R : TestAlgebra K) (p : GroupPoints J'.val R),
        matrix.hom.app (restrict.obj R)
          (baseChangePoint F K J.val.X R (pointHom e.hom R p)) = matrix'.hom.app R p) ∧
      (∀ (R : TestAlgebra K) (r : R),
        baseChangePoint F K A.group.X R (rootPoint a.hom R r) =
          rootPoint (𝟙 A.group) (restrict.obj R) r) ∧
      (∀ (R : TestAlgebra K) (t : Rˣ),
        baseChangePoint F K (multiplicativeLine F).X R (pointHom m.hom R (unitPoint R t)) =
          unitPoint (restrict.obj R) t) ∧
      (∀ (R : TestAlgebra K) (r : R),
        matrix'.hom.app R
          (rootPoint (a.hom ≫ E.map (W.posCoord.hom ≫ W.pos.inclusion) ≫ e.inv) R r) =
          liftMatrix (upper r)) ∧
      (∀ (R : TestAlgebra K) (r : R),
        matrix'.hom.app R
          (rootPoint (a.hom ≫ E.map (W.negCoord.hom ≫ W.neg.inclusion) ≫ e.inv) R r) =
          liftMatrix (lower r)) ∧
      (∀ (R : TestAlgebra K) (t : Rˣ),
        matrix'.hom.app R (cocharacterPoint (m.hom ≫ E.map W.diag ≫ e.inv) R t) =
          liftMatrix (diagonal t))

end

end LinearAlgebraicGroups.Specs.ExceptionalRankOneMatrixWitnesses
