import MathGenome.Internal.Specs.D07.Ch11.PrimitiveScalar
import MathGenome.Internal.Specs.D07.Ch11.GaussContent

/-!
Independent statements for K07.11.gauss_fraction_irreducible,
paper.tex:2583–2605. The preceding primitive-scalar lemma has its own
upstream statements. Coefficients are embedded into an arbitrary fraction
field model. A UFD structure is required, but no normalization is assumed.
The rescaling statement retains the specified factors and their degrees;
its input polynomial need not be primitive or monic.
-/

universe u v

namespace Specs.D07.Ch11.GaussFractionIrreducible

open Polynomial

def PrimitiveIrreducibleIff : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R[X]), f.IsPrimitive →
      (Irreducible f ↔ Irreducible (f.map (algebraMap R K)))

/-- Rescale the two given factors by reciprocal nonzero scalars. Their
formal degrees, and hence their positive degrees, are retained. -/
def RescaleFactorization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R[X]) (A B : K[X]), f ≠ 0 →
      f.map (algebraMap R K) = A * B → 0 < A.natDegree → 0 < B.natDegree →
      ∃ (a b : R[X]) (t : Kˣ), f = a * b ∧
        a.map (algebraMap R K) = C (t : K) * A ∧
        b.map (algebraMap R K) = C (↑(t⁻¹) : K) * B ∧
        a.degree = A.degree ∧ b.degree = B.degree ∧
        0 < a.natDegree ∧ 0 < b.natDegree

def MonicIrreducibleIff : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R[X]), f.Monic →
      (Irreducible f ↔ Irreducible (f.map (algebraMap R K)))

/-- Includes all primitive polynomials of natural degree zero, since these
are constant formal polynomials. They are units in both coefficient rings. -/
def PrimitiveConstant : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R[X]), f.IsPrimitive → f.natDegree = 0 →
      IsUnit f ∧ IsUnit (f.map (algebraMap R K)) ∧
        ¬Irreducible f ∧ ¬Irreducible (f.map (algebraMap R K))

/-- Failure without primitivity, including a factorization by nonunits. -/
def NonprimitiveCounterexample : Prop :=
  let f : ℤ[X] := C 2 * X + C 2
  ¬f.IsPrimitive ∧ f = C 2 * (X + 1) ∧
    ¬IsUnit (C (2 : ℤ)) ∧ ¬IsUnit (X + 1 : ℤ[X]) ∧
    ¬Irreducible f ∧ Irreducible (f.map (algebraMap ℤ ℚ))

end Specs.D07.Ch11.GaussFractionIrreducible
