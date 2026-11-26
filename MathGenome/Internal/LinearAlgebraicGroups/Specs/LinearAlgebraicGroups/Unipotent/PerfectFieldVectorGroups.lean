import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.KilledByPVectorEmbedding
import Mathlib.FieldTheory.Perfect

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

/-- A smooth connected commutative unipotent algebraic group killed by
multiplication by the positive characteristic of a perfect field is a vector group. -/
def PerfectFieldVectorGroups : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : AffineAlgebraicGroup k) [Smooth H.val.X.hom] [ConnectedSpace H.val.X.left],
    IsUnipotent H →
    (∀ (R : TestAlgebra k) (x y : ((groupPointsFunctor k).obj H.val).obj R), Commute x y) →
    (∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj H.val).obj R), x ^ p = 1) →
    ∃ (d : ℕ) (V : AffineAlgebraicGroup k),
      Nonempty (H.val ≅ V.val) ∧
        Nonempty ((groupPointsFunctor k).obj V.val ≅
          StandardGroups.additivePowerPoints k (Index.{u} d))

end LinearAlgebraicGroups.Specs.Unipotent
