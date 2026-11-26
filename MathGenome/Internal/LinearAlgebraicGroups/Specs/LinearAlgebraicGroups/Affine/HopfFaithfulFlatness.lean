import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.HopfAlgebras
import Mathlib.RingTheory.RingHom.FaithfullyFlat

namespace LinearAlgebraicGroups.Specs

open CategoryTheory

universe u

/-- An inclusion of finite-type commutative Hopf algebras over a field is faithfully flat. -/
def HopfFaithfulFlatness : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] (f : A ⟶ B),
    Function.Injective f.hom.toAlgHom → f.hom.toAlgHom.toRingHom.FaithfullyFlat

end LinearAlgebraicGroups.Specs
