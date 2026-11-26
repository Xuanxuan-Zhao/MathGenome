import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalParahoricRationalBruhat

open AbstractPairing (Datum)
open AdjointRepresentation (GroupPoints)
open BruhatOrbitParametrization (IsRepresentative)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)

/-- Rational Bruhat coverage and the identity label for the specified Borel,
using any chosen family of rational representatives of the scheme Weyl quotient. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    IsKBorel B → IsSubgroupOf T B →
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (J : Identification D),
        ∀ n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X),
          (∀ w, IsRepresentative J w (n w)) →
          let R := CommAlgCat.of k k
          let Y := (testSpec k).obj (Opposite.op R)
          let r : D.rootDatum.weylGroup → GroupPoints G.val R :=
            fun w ↦ toUnit Y ≫ n w ≫ J.normalizer.inclusion.hom.hom
          let bPoint : GroupPoints B.group R → GroupPoints G.val R :=
            fun b ↦ b ≫ B.inclusion.hom.hom
          (∀ g : GroupPoints G.val R,
            ∃ (w : D.rootDatum.weylGroup) (b₁ b₂ : GroupPoints B.group R),
              g = bPoint b₁ * r w * bPoint b₂) ∧
          (∀ w, (∃ b : GroupPoints B.group R, bPoint b = r w) ↔ w = 1)

end LinearAlgebraicGroups.Specs.ExceptionalParahoricRationalBruhat
