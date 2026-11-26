import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs

/-- Every affine algebraic group over a field has a closed immersion into the
general linear group of a finite-dimensional vector space. In a basis of
dimension `n`, the target represents invertible `n × n` matrices on all
commutative test algebras. -/
def FaithfulLinearization : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k),
    ∃ (n : ℕ) (L : AffineAlgebraicGroup k),
      Nonempty ((groupPointsFunctor k).obj L.val ≅
        StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))) ∧
      ∃ f : G.val ⟶ L.val, IsClosedImmersion f.hom.hom.left

end LinearAlgebraicGroups.Specs
