import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
The flat-map assertion of Theorem 4.8, paper.tex 922–932.
Rings and ring maps are unital; zero rings are allowed. `g.Flat` means
flatness of A as an R-module via g, without any injectivity, integrality,
domain, Noetherian, or finiteness hypothesis.
-/

universe u v

namespace Specs.P103.Ch04.FlatGoingDown

open scoped TensorProduct

/-- One step of going down, with contraction along the original ring map. -/
def goingDown : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.Flat →
    ∀ (p p' : PrimeSpectrum R) (q' : PrimeSpectrum A),
      p ≤ p' → PrimeSpectrum.comap g q' = p' →
      ∃ q : PrimeSpectrum A, q ≤ q' ∧ PrimeSpectrum.comap g q = p

/-- The local step for the actual map R_(g⁻¹q') → A_q'.
The fiber assertion is for every prime of the localized base, in particular
for the extension of any p contained in g⁻¹q'. -/
def localizedFaithfulFiber : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.Flat → ∀ q' : PrimeSpectrum A,
    let f := Localization.localRingHom
      (q'.asIdeal.comap g) q'.asIdeal g rfl
    letI := f.toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime (q'.asIdeal.comap g))
      (Localization.AtPrime q'.asIdeal) ∧
    ∀ p : PrimeSpectrum (Localization.AtPrime (q'.asIdeal.comap g)),
      Nontrivial ((Localization.AtPrime q'.asIdeal) ⊗[
        Localization.AtPrime (q'.asIdeal.comap g)] p.asIdeal.ResidueField)

/-- A finite descending chain lifts from any specified prime above its
first (largest) prime. Equal consecutive primes are allowed, and n = 0
is included. All contractions and the specified endpoint are retained. -/
def finiteDescendingChains : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.Flat →
    ∀ (n : ℕ) (p : Fin (n + 1) → PrimeSpectrum R), Antitone p →
      ∀ q₀ : PrimeSpectrum A, PrimeSpectrum.comap g q₀ = p 0 →
      ∃ q : Fin (n + 1) → PrimeSpectrum A,
        Antitone q ∧ q 0 = q₀ ∧ ∀ i, PrimeSpectrum.comap g (q i) = p i

/-- Strict descending chains lift with the same number of strict inclusions. -/
def finiteStrictDescendingChains : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.Flat →
    ∀ (n : ℕ) (p : Fin (n + 1) → PrimeSpectrum R), StrictAnti p →
      ∀ q₀ : PrimeSpectrum A, PrimeSpectrum.comap g q₀ = p 0 →
      ∃ q : Fin (n + 1) → PrimeSpectrum A,
        StrictAnti q ∧ q 0 = q₀ ∧ ∀ i, PrimeSpectrum.comap g (q i) = p i

end Specs.P103.Ch04.FlatGoingDown
