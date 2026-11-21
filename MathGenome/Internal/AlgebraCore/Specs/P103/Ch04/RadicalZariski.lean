import Mathlib.RingTheory.Spectrum.Prime.Topology

universe u v

/-! Independent statements for paper.tex, Chapter 4, Theorem 4.3 and its
preceding definition of the Zariski topology. The library objects are used
canonically: radical, nilradical, prime spectrum, zeroLocus = V, and basicOpen = D.
The localization homeomorphism is assigned to the localization spectrum goal. -/

namespace Specs.P103.Ch04.RadicalZariski

def radical_membership_positive : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (a : R),
    a ∈ I.radical ↔ ∃ n : ℕ, 1 ≤ n ∧ a ^ n ∈ I

def radical_eq_prime_intersection : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    I.radical = sInf {p : Ideal R | I ≤ p ∧ p.IsPrime}

def prime_is_proper : Prop :=
  ∀ (R : Type u) [CommRing R] (p : PrimeSpectrum R), p.asIdeal ≠ ⊤

def empty_ideal_intersection : Prop :=
  ∀ (R : Type u) [CommRing R], sInf (∅ : Set (Ideal R)) = ⊤

def nilradical_eq_radical_zero : Prop :=
  ∀ (R : Type u) [CommRing R], nilradical R = (⊥ : Ideal R).radical

def nilradical_membership : Prop :=
  ∀ (R : Type u) [CommRing R] (a : R),
    a ∈ nilradical R ↔ IsNilpotent a

def vanishing_membership : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (p : PrimeSpectrum R),
    p ∈ PrimeSpectrum.zeroLocus (I : Set R) ↔ I ≤ p.asIdeal

def principal_membership : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R) (p : PrimeSpectrum R),
    p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ↔ f ∉ p.asIdeal

def vanishing_iSup : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Sort v) (I : ι → Ideal R),
    (⋂ i, PrimeSpectrum.zeroLocus (I i : Set R)) =
      PrimeSpectrum.zeroLocus ((⨆ i, I i : Ideal R) : Set R)

def vanishing_union : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    PrimeSpectrum.zeroLocus (I : Set R) ∪ PrimeSpectrum.zeroLocus (J : Set R) =
      PrimeSpectrum.zeroLocus ((I * J : Ideal R) : Set R)

def vanishing_zero : Prop :=
  ∀ (R : Type u) [CommRing R],
    PrimeSpectrum.zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ

def vanishing_unit : Prop :=
  ∀ (R : Type u) [CommRing R],
    PrimeSpectrum.zeroLocus ((⊤ : Ideal R) : Set R) = ∅

def closed_iff_vanishing : Prop :=
  ∀ (R : Type u) [CommRing R] (Z : Set (PrimeSpectrum R)),
    IsClosed Z ↔ ∃ I : Ideal R, Z = PrimeSpectrum.zeroLocus (I : Set R)

def principal_mul : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R),
    (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R))

def principal_basis : Prop :=
  ∀ (R : Type u) [CommRing R],
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : R => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)))

def principal_zero : Prop :=
  ∀ (R : Type u) [CommRing R],
    (PrimeSpectrum.basicOpen (0 : R) : Set (PrimeSpectrum R)) = ∅

def principal_one : Prop :=
  ∀ (R : Type u) [CommRing R],
    (PrimeSpectrum.basicOpen (1 : R) : Set (PrimeSpectrum R)) = Set.univ

def spectrum_zero_ring : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R], IsEmpty (PrimeSpectrum R)

end Specs.P103.Ch04.RadicalZariski
