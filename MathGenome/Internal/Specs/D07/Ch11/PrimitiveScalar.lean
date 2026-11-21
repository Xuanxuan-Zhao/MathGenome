import MathGenome.Internal.Specs.D07.Ch11.ContentPrimitive
import Mathlib.RingTheory.Localization.FractionRing

/-!
Independent statements for paper.tex:2552–2581, Lemma `primitive-scalar`.
`map (algebraMap R K)` is the coefficient embedding into an arbitrary model
of the fraction field. Thus an equality with `g.map ...` expresses that a
scalar multiple has coefficients in R, without identifying R and its image.
Primitivity is the canonical coefficient-divisor predicate used upstream.
No chosen normalization of content is an additional hypothesis.
-/

universe u v

namespace Specs.D07.Ch11.PrimitiveScalar

open Polynomial

/-- Every nonzero fraction-field polynomial is a nonzero scalar multiple of
a primitive polynomial over the original UFD. -/
def PrimitiveScalarDecomposition : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : K[X]), A ≠ 0 →
      ∃ (t : Kˣ) (A₀ : R[X]), A₀.IsPrimitive ∧
        A = C (t : K) * A₀.map (algebraMap R K)

/-- Integrality of a scalar multiple of a primitive polynomial forces the
scalar into the embedded coefficient ring. -/
def IntegralPrimitiveScalar : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (h g : R[X]) (t : Kˣ), h.IsPrimitive →
      g.map (algebraMap R K) = C (t : K) * h.map (algebraMap R K) →
      ∃ r : R, algebraMap R K r = (t : K)

/-- When the multiple is also primitive, the scalar is the image of a unit
of the original coefficient ring. -/
def PrimitiveScalarUnit : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (h g : R[X]) (t : Kˣ), h.IsPrimitive → g.IsPrimitive →
      g.map (algebraMap R K) = C (t : K) * h.map (algebraMap R K) →
      ∃ r : Rˣ, algebraMap R K (r : R) = (t : K)

end Specs.D07.Ch11.PrimitiveScalar
