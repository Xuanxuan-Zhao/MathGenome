import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Fppf

/-- A right fppf torsor under an affine algebraic group over a field is represented
by a nonempty affine scheme of finite type, with the original right action. -/
def AffineTorsorRepresentability : Prop :=
  ∀ {k : Type u} [Field k] (H : AffineAlgebraicGroup k)
    (P : FppfTorsor (fieldBase k) H.val),
    ∃ (X : Over (fieldBase k)) (a : SchemeRightAction X H.val),
      Nonempty (RightActionIso (representedAction a) P.val) ∧
      Nonempty X.left.left ∧ IsAffine X.left.left ∧
      LocallyOfFiniteType X.hom.left ∧ QuasiCompact X.hom.left ∧
      (Smooth H.val.X.hom → Smooth X.hom.left)

/-- The comparison criterion over a field uses nonemptiness and finite type. -/
def NonemptySchemeTorsorCriterion : Prop :=
  ∀ {k : Type u} [Field k] (H : AffineAlgebraicGroup k)
    {X : Over (fieldBase k)} (a : SchemeRightAction X H.val),
    Nonempty X.left.left → LocallyOfFiniteType X.hom.left → QuasiCompact X.hom.left →
    IsIso (comparison a) → IsTorsor (representedAction a)

end LinearAlgebraicGroups.Specs.Fppf
