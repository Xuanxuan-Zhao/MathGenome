import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
The dimension assertion of Theorem 4.7 (`paper.tex:913–919`). All rings
are commutative and unital, including the zero ring; the integral map need
not be injective. `ringKrullDim` is the supremum of finite strict prime-chain
lengths in `WithBot ℕ∞`, with value `⊥` for an empty spectrum.
-/

namespace P103.Ch04.IntegralDimension.Specs

universe u v

/-- Every strict upstairs chain contracts strictly. -/
def strict_contraction : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral → StrictMono (PrimeSpectrum.comap g)

/-- Every finite strict chain containing the kernel has a strict lift of the
same length. The parameter `n` counts steps, including `n = 0`. -/
def finite_strict_chain_lift : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral →
    ∀ (n : ℕ) (p : Fin (n + 1) → PrimeSpectrum R), StrictMono p →
      RingHom.ker g ≤ (p 0).asIdeal →
      ∃ q : Fin (n + 1) → PrimeSpectrum A, StrictMono q ∧
        ∀ i, PrimeSpectrum.comap g (q i) = p i

/-- Equality includes both unbounded dimension and the empty-spectrum value. -/
def dimension_eq : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral →
      ringKrullDim A = ringKrullDim (R ⧸ RingHom.ker g)

/-- The two spectra in the dimension equality are empty simultaneously. -/
def empty_spectrum_iff : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral →
      (IsEmpty (PrimeSpectrum A) ↔ IsEmpty (PrimeSpectrum (R ⧸ RingHom.ker g)))

end P103.Ch04.IntegralDimension.Specs
