import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import Mathlib.AlgebraicGeometry.Geometrically.Connected

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs.StandardGroups
open LinearAlgebraicGroups.Specs.SmoothDiagonalKernel

universe u

namespace LinearAlgebraicGroups.Specs.SplitSolvableRadical

noncomputable section

variable {k : Type u} [Field k]

/-- Splitness of a torus is expressed over the ground field. -/
def IsSplitTorus (D : AffineAlgebraicGroup k) : Prop :=
  ∃ r : ℕ, Nonempty ((groupPointsFunctor k).obj D.val ≅
    multiplicativePowerPoints k (Unipotent.Index.{u} r))

/-- A split solvable affine group has a faithful upper triangular realization on every
commutative test algebra. -/
def FaithfulTriangularization : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    SchemeDerivedGroup.IsSplitSolvable G.val →
    ∃ (n : ℕ) (H : AffineAlgebraicGroup k) (j : G.val ⟶ H.val)
      (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Unipotent.Index.{u} n)),
      IsClosedImmersion j.hom.hom.left ∧ IsUpperTriangular j e

/-- The diagonal quotient and its scheme kernel in a faithful triangular realization. -/
def HasDiagonalRadical {n : ℕ} {G H T : AffineAlgebraicGroup k} (j : G.val ⟶ H.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Unipotent.Index.{u} n))
    (t : (groupPointsFunctor k).obj T.val ≅ multiplicativePowerPoints k (Unipotent.Index.{u} n))
    (d : G.val ⟶ T.val) (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val)
    (i : D.val ⟶ T.val) (U : ClosedSubgroup G.val) : Prop :=
  IsDiagonalMorphism j e t d ∧ IsImageFactorization d p i ∧ IsCanonicalImage d p i ∧
    IsSchemeKernel d U ∧ Unipotent.IsFppfGroupQuotient U p ∧ IsSplitTorus D ∧
    Smooth U.group.X.hom ∧ GeometricallyConnected U.group.X.hom ∧
    IsNormalSubgroup U.inclusion ∧ Unipotent.IsUnipotent (Unipotent.closedSubgroupAlgebraicGroup U) ∧
    ∀ V : ClosedSubgroup G.val, Unipotent.IsUnipotent (Unipotent.closedSubgroupAlgebraicGroup V) →
      SchemeDerivedGroup.IsSubgroupOf V U

/-- The diagonal kernel is the split unipotent radical of a split solvable group. -/
def SplitKernelOfTriangularization : Prop :=
  ∀ {k : Type u} [Field k] (n : ℕ) (G H T : AffineAlgebraicGroup k)
    (j : G.val ⟶ H.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Unipotent.Index.{u} n))
    (t : (groupPointsFunctor k).obj T.val ≅ multiplicativePowerPoints k (Unipotent.Index.{u} n)),
    SchemeDerivedGroup.IsSplitSolvable G.val →
    IsClosedImmersion j.hom.hom.left → IsUpperTriangular j e →
    ∃ (d : G.val ⟶ T.val) (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val)
      (i : D.val ⟶ T.val) (U : ClosedSubgroup G.val),
      HasDiagonalRadical j e t d D p i U ∧
        Unipotent.IsSplitUnipotent (Unipotent.closedSubgroupAlgebraicGroup U)

end
end LinearAlgebraicGroups.Specs.SplitSolvableRadical
