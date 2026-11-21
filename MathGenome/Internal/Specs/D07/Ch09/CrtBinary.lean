import MathGenome.Internal.Specs.D07.Ch09.FirstIsomorphism
import MathGenome.Internal.Specs.D07.Ch09.ProductIntersection
import Mathlib.Algebra.Ring.Prod

/-!
Independent specifications for K07.09.crt_binary, paper.tex:1735–1758.
The chapter assumes commutativity from paper.tex:1631 onward. Ideals
need not be proper, and the zero ring is included. All quotients and
ideal products are the canonical objects identified by the upstream Specs.
-/

universe u

namespace Specs.D07.Ch09.CrtBinary

def ReductionMapType : Type (u + 1) :=
  {R : Type u} → [CommRing R] → (I J : Ideal R) →
    R →+* (R ⧸ I) × (R ⧸ J)

/-- The simultaneous reduction map, with its unital ring-homomorphism structure. -/
def reductionMapValue : ReductionMapType.{u} :=
  fun {_} _ I J => (Ideal.Quotient.mk I).prod (Ideal.Quotient.mk J)

def KernelIsIntersection : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    RingHom.ker (reductionMapValue I J) = I ⊓ J

/-- The stated representative works for every choice of witnesses and residues. -/
def ExplicitPreimage : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R)
    (i j : R), i ∈ I → j ∈ J → i + j = 1 →
      ∀ a b : R, reductionMapValue I J (a * j + b * i) =
        (Ideal.Quotient.mk I a, Ideal.Quotient.mk J b)

def ReductionSurjective : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    Comaximal.comaximalPredicateValue I J →
      Function.Surjective (reductionMapValue I J)

/-- Both directions of the induced isomorphism, including the inverse formula. -/
def BinaryCRT : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    Comaximal.comaximalPredicateValue I J →
      ∃ e : R ⧸ (I * J) ≃+* (R ⧸ I) × (R ⧸ J),
        (∀ r : R, e (Ideal.Quotient.mk (I * J) r) = reductionMapValue I J r) ∧
        (∀ (i j : R), i ∈ I → j ∈ J → i + j = 1 →
          ∀ a b : R, e.symm (Ideal.Quotient.mk I a, Ideal.Quotient.mk J b) =
            Ideal.Quotient.mk (I * J) (a * j + b * i))

/-- For I = J = (2) in ℤ the range is exactly the diagonal, and the
map is not onto. This is indeed a noncomaximal pair. -/
def IntegerCounterexample : Prop :=
  let I : Ideal ℤ := Ideal.span {2}
  ¬ Comaximal.comaximalPredicateValue I I ∧
    (∀ x y : ℤ ⧸ I, (x, y) ∈ (reductionMapValue I I).range ↔ x = y) ∧
    ¬ Function.Surjective (reductionMapValue I I)

end Specs.D07.Ch09.CrtBinary
