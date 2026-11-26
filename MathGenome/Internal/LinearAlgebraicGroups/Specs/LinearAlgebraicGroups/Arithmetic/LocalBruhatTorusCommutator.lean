import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeChambers

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalBruhatTorusCommutator

open _root_.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport (RationalPoints)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition HasLimit cocharacterPoint)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsReductive)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (IsRegular)

/-- An element of a normal subgroup outside the regular limit parabolic yields
a parabolic point with the same quotient image as a Weyl representative. The
parabolic point limits into the split-torus centralizer, and the commutator
with the representative is given by a scheme-noncentral cocharacter. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] (J : AffineAlgebraicGroup F), IsReductive J →
    ∀ (S : ClosedSubgroup J.val), IsMaximalSplitTorus S →
      ∀ (c : Cocharacter S.group), IsRegular S c →
        ∀ (D : LimitDecomposition (c ≫ S.inclusion))
          (N : Subgroup (RationalPoints J.val.X)) [N.Normal],
          let R := CommAlgCat.of F F
          let B := SubgroupSections D.parabolic ((testSpec F).obj (op R))
          let a (t : Fˣ) : RationalPoints J.val.X :=
            cocharacterPoint (c ≫ S.inclusion) R t
          (∃ g : RationalPoints J.val.X, g ∈ N ∧ g ∉ B) →
          ∃ (b p z : RationalPoints J.val.X) (d : Cocharacter S.group),
            (QuotientGroup.mk b : RationalPoints J.val.X ⧸ N) = QuotientGroup.mk p ∧
            p ∈ B ∧
            HasLimit (c ≫ S.inclusion) p z ∧
            Centralizes S.inclusion z ∧
            (∃ (X : SchemeOver F) (x : X ⟶ J.val.X), ¬ Centralizes (d ≫ S.inclusion) x) ∧
            (∀ t : Fˣ, a t * b * (a t)⁻¹ * b⁻¹ =
              cocharacterPoint (d ≫ S.inclusion) R t) ∧
            ∀ s t : Fˣ, Commute (a s) (cocharacterPoint (d ≫ S.inclusion) R t)

end LinearAlgebraicGroups.Specs.Arithmetic.LocalBruhatTorusCommutator
