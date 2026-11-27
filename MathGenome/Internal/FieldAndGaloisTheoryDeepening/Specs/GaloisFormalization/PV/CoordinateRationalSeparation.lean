import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.LineStabilizerRepresentation
import Mathlib.RingTheory.Localization.FractionRing

namespace GaloisFormalization.PV.CoordinateRationalSeparation.Specs

open MatrixGroupCoordinates.Specs
open scoped MatrixGroupCoordinates.Specs

universe u

noncomputable section

variable {C : Type u} [Field C] {n : ℕ}

/-- Polynomial coordinate functions on the matrix subgroup. -/
abbrev GroupCoordinateRing (G : Subgroup (GL (Fin n) C)) :=
  CoordinateRing (G : Set (GL (Fin n) C))

/-- The total quotient ring, obtained by inverting all non-zero-divisors. -/
abbrev TotalCoordinateRing (G : Subgroup (GL (Fin n) C)) :=
  FractionRing (GroupCoordinateRing G)

/-- An action pulls back right translations when its value at x is evaluation at xg. -/
def IsRightTranslation (G : Subgroup (GL (Fin n) C))
    (τ : G →* (GroupCoordinateRing G ≃ₐ[C] GroupCoordinateRing G)) : Prop :=
  ∀ (g x : G) (r : GroupCoordinateRing G), evalCoordinate x (τ g r) = evalCoordinate (x * g) r

/-- Right translations induce algebra automorphisms of the coordinate ring. -/
def ExistsRightTranslation : Prop :=
  ∀ {C : Type u} [Field C] {n : ℕ} (G : Subgroup (GL (Fin n) C)),
    ∃ τ : G →* (GroupCoordinateRing G ≃ₐ[C] GroupCoordinateRing G), IsRightTranslation G τ

/-- Extension of a coordinate-ring automorphism to the total quotient ring. -/
def extendToTotal {G : Subgroup (GL (Fin n) C)}
    (e : GroupCoordinateRing G ≃ₐ[C] GroupCoordinateRing G) :
    TotalCoordinateRing G ≃+* TotalCoordinateRing G :=
  IsFractionRing.ringEquivOfRingEquiv e.toRingEquiv

/-- A function nonzero somewhere on each irreducible component is a non-zero-divisor. -/
def NonZeroDivisorOfComponents : Prop :=
  ∀ {C : Type u} [Field C] {n : ℕ} (G : Subgroup (GL (Fin n) C))
    (r : GroupCoordinateRing G),
    (∀ X ∈ irreducibleComponents G, ∃ x ∈ X, evalCoordinate x r ≠ 0) →
      r ∈ nonZeroDivisors (GroupCoordinateRing G)

/-- A regular orbit gives a quotient separating g from the closed subgroup H.
The values at 1 and g use only evaluation of the numerator and denominator. -/
def ExistsCoordinateRationalSeparator : Prop :=
  ∀ {C : Type u} [Field C] [IsAlgClosed C] [CharZero C] {n : ℕ}
    (G : Subgroup (GL (Fin n) C)), IsAlgebraicSubgroup G →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
    ∀ g : G, g ∉ H →
    ∀ (τ : G →* (GroupCoordinateRing G ≃ₐ[C] GroupCoordinateRing G)),
      IsRightTranslation G τ →
      ∃ (m : ℕ) (ρ : G →* GL (Fin m) C) (w : Fin m → C)
        (a b : (Fin m → C) →ₗ[C] C)
        (d : nonZeroDivisors (GroupCoordinateRing G)) (r : GroupCoordinateRing G),
        IsRegularRepresentation ρ ∧ w ≠ 0 ∧
        (∀ x : G, (Submodule.span C {w}).map (Matrix.toLin' (ρ x).val) =
          Submodule.span C {w} ↔ x ∈ H) ∧
        (∀ x : G, evalCoordinate x d.val = a (Matrix.toLin' (ρ x).val w)) ∧
        (∀ x : G, evalCoordinate x r = b (Matrix.toLin' (ρ x).val w)) ∧
        (∀ X ∈ irreducibleComponents G, ∃ x ∈ X, evalCoordinate x d.val ≠ 0) ∧
        evalCoordinate (1 : G) d.val ≠ 0 ∧ evalCoordinate g d.val ≠ 0 ∧
        evalCoordinate (1 : G) r / evalCoordinate (1 : G) d.val ≠
          evalCoordinate g r / evalCoordinate g d.val ∧
        (∀ h : H, τ h.val r * d.val = r * τ h.val d.val) ∧
        let f := IsLocalization.mk' (TotalCoordinateRing G) r d
        (∀ h : H, extendToTotal (τ h.val) f = f) ∧ extendToTotal (τ g) f ≠ f

end

end GaloisFormalization.PV.CoordinateRationalSeparation.Specs
