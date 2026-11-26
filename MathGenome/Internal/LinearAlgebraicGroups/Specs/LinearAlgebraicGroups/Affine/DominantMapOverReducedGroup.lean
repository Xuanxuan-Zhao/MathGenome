import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.HopfAlgebras
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace LinearAlgebraicGroups.Specs

open CategoryTheory

universe u

/-- The reduced-target case of A07 over an algebraically closed field. The source
of the associated group morphism can be nonreduced. -/
def FaithfullyFlatOfInjectiveHopfOfReduced : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] {A B : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] [IsReduced A]
    (f : A ⟶ B),
    Function.Injective f.hom.toAlgHom → f.hom.toAlgHom.toRingHom.FaithfullyFlat

end LinearAlgebraicGroups.Specs
