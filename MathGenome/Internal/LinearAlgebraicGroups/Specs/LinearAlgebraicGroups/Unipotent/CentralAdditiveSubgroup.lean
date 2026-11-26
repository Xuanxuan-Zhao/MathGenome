import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralKilledByPCurves

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

/-- A nonconstant affine-line curve over a separable extension forces a
central closed copy of the additive group over the ground field. -/
def CentralAdditiveSubgroup : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : AffineAlgebraicGroup k), Smooth U.val.X.hom → ConnectedSpace U.val.X.left →
    IsUnipotent U →
    ∀ (L : Type u) [Field L] [Algebra k L] [Algebra.IsTranscendentalSeparable k L],
      ∀ x : AffineLineCurve ((groupBaseChange k L).obj U.val), IsNonconstantCurve x →
      ∃ H : ClosedSubgroup U.val,
        Centralizes (𝟙 U.val) H.inclusion.hom.hom ∧
        Nonempty ((groupPointsFunctor k).obj H.group ≅ StandardGroups.additivePoints k)

end LinearAlgebraicGroups.Specs.Unipotent
