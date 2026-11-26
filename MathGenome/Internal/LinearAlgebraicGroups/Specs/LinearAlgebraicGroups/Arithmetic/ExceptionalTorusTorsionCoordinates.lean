import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.ExceptionalTorusTorsionCoordinates

open AbstractPairing (Datum Root)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue)
open DatumAndWeyl (Identification)
open GeometricRadicals (IsSplitTorus)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

local notation "R" => CommAlgCat.of ℂ ℂ

/-- Evaluating a cocharacter at a unit and then applying a character gives
the power prescribed by their integral pairing. -/
def CharacterEvaluation : Prop :=
  ∀ {G : AffineAlgebraicGroup ℂ} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (y : Additive (Cocharacter T.group)) (ζ : ℂˣ) (χ : Character T.group),
      characterValue χ R (cocharacterPoint y.toMul R ζ) =
        (↑(ζ ^ D.rootDatum.toLinearMap (Additive.ofMul χ) y) : ℂ)

/-- For any primitive-root coordinates of a point, the actual normalizer
conjugations fix the point precisely up to a multiple of the order in the
cocharacter lattice. A root is trivial on the point precisely when its
pairing is divisible by the same order. -/
def CoordinateCongruences {G : AffineAlgebraicGroup ℂ} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (D : Datum T) (I : Identification D)
    (t : GroupPoints T.group R) (d : ℕ) (y : Additive (Cocharacter T.group)) : Prop :=
  (∀ w : D.rootDatum.weylGroup,
    t ≫ (I.image.conjugation (I.labelEquiv w)).hom.hom.hom = t ↔
      ∃ a : Additive (Cocharacter T.group), w.val.coweightEquiv.symm y - y = (d : ℤ) • a) ∧
  (∀ α : Root T,
    characterValue α.val R t = 1 ↔ (d : ℤ) ∣ D.rootDatum.toLinearMap (D.rootDatum.root α) y)

def PrimitiveCoordinateCongruences : Prop :=
  ∀ {G : AffineAlgebraicGroup ℂ} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (I : Identification D), IsSplitTorus T.group →
    ∀ (t : GroupPoints T.group R) (d : ℕ) (ζ : ℂˣ) (y : Additive (Cocharacter T.group)),
      0 < d → IsPrimitiveRoot ζ d → t = cocharacterPoint y.toMul R ζ →
      CoordinateCongruences D I t d y

/-- A finite-order point of the actual split torus has primitive-root
coordinates, with the evaluation formula and both congruences for the
same choice of order and cocharacter. -/
def TorsionCoordinates : Prop :=
  ∀ {G : AffineAlgebraicGroup ℂ} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (I : Identification D), IsSplitTorus T.group →
    ∀ t : GroupPoints T.group R, IsOfFinOrder t →
      ∃ (d : ℕ) (ζ : ℂˣ) (y : Additive (Cocharacter T.group)),
        0 < d ∧ t ^ d = 1 ∧ IsPrimitiveRoot ζ d ∧ t = cocharacterPoint y.toMul R ζ ∧
        (∀ χ : Character T.group,
          characterValue χ R t = (↑(ζ ^ D.rootDatum.toLinearMap (Additive.ofMul χ) y) : ℂ)) ∧
        CoordinateCongruences D I t d y

end LinearAlgebraicGroups.Specs.ExceptionalTorusTorsionCoordinates
