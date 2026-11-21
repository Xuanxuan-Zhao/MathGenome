import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
Independent statements for the last assertion of Theorem 4.6,
`paper.tex:904–910` (`p103:ALG-05-C01-R03`).

The rings are commutative and unital. A ring map is integral when every
element of its codomain satisfies a monic polynomial over that map.
Prime ideals are proper. No injectivity or nontriviality is assumed;
in particular the zero-ring cases are included.
-/

namespace P103.Ch04.LyingOver.Specs

universe u v

/-- Contraction along any unital ring map contains its kernel. -/
def contraction_contains_kernel : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A) (q : PrimeSpectrum A),
    RingHom.ker g ≤ (PrimeSpectrum.comap g q).asIdeal

/-- Every proper prime containing the kernel of an integral map has a
proper prime lying over it. -/
def exists_prime_over : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral →
    ∀ (p : Ideal R), p.IsPrime → RingHom.ker g ≤ p →
      ∃ q : Ideal A, q.IsPrime ∧ Ideal.comap g q = p

/-- The full image statement, with `zeroLocus` denoting V(ker g). -/
def spectrum_image : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral →
    Set.range (PrimeSpectrum.comap g) =
      PrimeSpectrum.zeroLocus (RingHom.ker g : Set R)

end P103.Ch04.LyingOver.Specs
