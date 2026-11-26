import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.UnitriangularSupportSubgroups

open StandardGroups Unipotent

/-- A matrix is supported on the strict upper positions allowed by the relation. -/
def HasSupport {J R : Type*} [LinearOrder J] [Zero R] (q : J → J → Prop)
    (a : Matrix J J R) : Prop :=
  ∀ i j, ¬ (i < j ∧ q i j) → a i j = 0

/-- A transitive restriction on the strict upper entries cuts out a closed
subgroup of a faithfully realized unitriangular affine algebraic group.
The inclusion represents the restriction over every commutative test algebra. -/
def ClosedSubgroupOfSupport : Prop :=
  ∀ {k : Type u} [Field k] (U : AffineAlgebraicGroup k) (n : ℕ)
    (E : (groupPointsFunctor k).obj U.val ⟶ generalLinearPoints k (Index.{u} n)),
    (∀ R : TestAlgebra k, Function.Injective (E.app R)) →
    (∀ (R : TestAlgebra k) (x : Points U.val.X R),
      IsUpperUnitriangular ((E.app R x).val)) →
    ∀ (q : Index.{u} n → Index.{u} n → Prop),
      (∀ i j l, q i j → q j l → q i l) →
      ∃ H : ClosedSubgroup U.val,
        ∀ (R : TestAlgebra k) (x : Points U.val.X R),
          HasSupport q ((E.app R x).val - 1) ↔
            ∃ y : Points H.group.X R, y ≫ H.inclusion.hom.hom = x

end LinearAlgebraicGroups.Specs.UnitriangularSupportSubgroups
