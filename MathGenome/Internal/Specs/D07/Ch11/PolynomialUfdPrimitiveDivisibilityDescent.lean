import MathGenome.Internal.Specs.D07.Ch11.ContentPrimitive
import Mathlib.RingTheory.Localization.FractionRing

/-!
Independent statements for the prime-factor step of K07.11.polynomial_ufd,
paper.tex:2623–2645. The fraction field is any compatible model of Frac(R).
Only the coefficient ring is assumed to be a UFD. In particular no UFD
structure on R[X] is among the hypotheses.
-/

universe u v

namespace Specs.D07.Ch11.PolynomialUfdPrimitiveDivisibilityDescent

open Polynomial

/-- Divisibility by a primitive positive-degree polynomial descends along
the coefficient embedding, including when the dividend is zero. -/
def PrimitiveDivisibilityDescent : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (h a : R[X]), h.IsPrimitive → 0 < h.natDegree →
      h.map (algebraMap R K) ∣ a.map (algebraMap R K) → h ∣ a

/-- A primitive positive-degree polynomial whose fraction-field image is
irreducible is a prime element of the original polynomial ring. -/
def PrimitiveIrreducibleIsPrime : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (h : R[X]), h.IsPrimitive → 0 < h.natDegree →
      Irreducible (h.map (algebraMap R K)) → Prime h

/-- A prime of the UFD remains prime under the constant-polynomial map. -/
def ConstantPrime : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (p : R), Prime p → Prime (C p)

end Specs.D07.Ch11.PolynomialUfdPrimitiveDivisibilityDescent
