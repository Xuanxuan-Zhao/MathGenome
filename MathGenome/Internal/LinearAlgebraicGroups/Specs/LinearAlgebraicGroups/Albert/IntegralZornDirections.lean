import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.PeirceFrames
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.Triality

namespace LinearAlgebraicGroups.Albert.IntegralZornDirectionsSpecification

open _root_.LinearAlgebraicGroups.Composition
open Composition.PeirceSpecification Composition.ZornSpecification TrialitySpecification
open scoped TensorProduct

universe u

/-- The two diagonal slots and the three upper and three lower slots. -/
abbrev DirectionIndex := Option (Fin 3) ⊕ Option (Fin 3)

abbrev Automorphism (R : Type u) [CommRing R] := ZornIsomorphism (norm R)

/-- The first and second diagonal idempotents, and the first plus each upper or lower
standard coordinate vector, with positive signs in the original Zorn coordinates. -/
def direction (R : Type u) [CommRing R] : DirectionIndex → Zorn R
  | .inl none => first R
  | .inr none => second R
  | .inl (some i) => Zorn.ofCoordinates (1, Pi.single i 1, 0, 0)
  | .inr (some i) => Zorn.ofCoordinates (1, 0, Pi.single i 1, 0)

def IntegralLifting : Prop :=
  ∀ e : QuadricPoint (norm ℤ), ∃ F : Automorphism ℤ, F.toLinearEquiv (first ℤ) = e.val

/-- The eight integral vectors form a basis whose scalar extension gives the same eight
vectors over each commutative test ring. -/
def DirectionBasis : Prop :=
  ∃ b : Module.Basis DirectionIndex ℤ (Zorn ℤ),
    (∀ i, b i = direction ℤ i) ∧
    ∀ (R : Type u) [CommRing R] (i : DirectionIndex),
      ((b.baseChange R).map (ZornSpecification.baseChange ℤ R)) i = direction R i

/-- The equality expressing transport of scalar extension through the Zorn coordinates. -/
def IsExtension (F : Automorphism ℤ) {R : Type u} [CommRing R] (G : Automorphism R) : Prop :=
  ∀ x : R ⊗[ℤ] Zorn ℤ,
    G.toLinearEquiv (ZornSpecification.baseChange ℤ R x) = ZornSpecification.baseChange ℤ R (F.toLinearEquiv.baseChange ℤ R (Zorn ℤ) (Zorn ℤ) x)

/-- The chosen integral automorphisms give the eight directions over every test ring.
Integral automorphisms extend to natural actions on both the octonion and Albert models.
The Albert actions fix the ordered frame and apply the same octonion map to every block. -/
def DirectionActions : Prop :=
  ∃ (F : DirectionIndex → Automorphism ℤ)
    (extend : ∀ (R : Type u) [CommRing R], Automorphism ℤ → Automorphism R)
    (act : ∀ (R : Type u) [CommRing R], Automorphism ℤ → frameStabilizer (R := R)),
    (∀ i, (F i).toLinearEquiv (first ℤ) = direction ℤ i) ∧
    (∀ (R : Type u) [CommRing R] (i : DirectionIndex),
      (extend R (F i)).toLinearEquiv (first R) = direction R i) ∧
    (∀ (R : Type u) [CommRing R] (a : Automorphism ℤ), IsExtension a (extend R a)) ∧
    (∀ (R : Type u) [CommRing R] (a : Automorphism ℤ) (x : Model R),
      (act R a).val x = (x.1, fun i => (extend R a).toLinearEquiv (x.2 i))) ∧
    ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (a : Automorphism ℤ),
      (∀ x, mapCoordinates f ((extend R a).toLinearEquiv x) =
        (extend S a).toLinearEquiv (mapCoordinates f x)) ∧
      ∀ x, mapModel f ((act R a).val x) = (act S a).val (mapModel f x)

end LinearAlgebraicGroups.Albert.IntegralZornDirectionsSpecification
