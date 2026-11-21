import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.RingLocalization
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.SpectrumFunctorQuotient

/-! Independent statements for the localization assertions of Theorems 4.3–4.4.
`Localization S` is the ring of fractions from Theorem 4.1; extension is
`Ideal.map` and contraction is `PrimeSpectrum.comap` along its algebra map.
All subtype topologies below are inherited Zariski topologies. No regularity,
nontriviality, or exclusion of zero from S is assumed. -/

universe u

namespace Specs.P103.Ch04.LocalizationSpectrum

/-- An order isomorphism specifies both inverse bijections and preservation of
ideal inclusion in both directions. Its maps are contraction and extension. -/
def order_correspondence : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    ∃ e : PrimeSpectrum (Localization S) ≃o
        {p : PrimeSpectrum R // Disjoint (S : Set R) (p.asIdeal : Set R)},
      (∀ q, (e q).val = PrimeSpectrum.comap (algebraMap R (Localization S)) q) ∧
      (∀ p, (e.symm p).asIdeal = p.val.asIdeal.map (algebraMap R (Localization S)))

/-- The extension of a disjoint prime consists precisely of fractions whose
numerator belongs to the original prime. -/
def fraction_membership : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (p : PrimeSpectrum R),
    Disjoint (S : Set R) (p.asIdeal : Set R) → ∀ (a : R) (s : S),
      Localization.mk a s ∈ p.asIdeal.map (algebraMap R (Localization S)) ↔ a ∈ p.asIdeal

/-- The image is exactly the primes disjoint from S. -/
def contraction_range : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
      {p : PrimeSpectrum R | Disjoint (S : Set R) (p.asIdeal : Set R)}

/-- The bijection is a homeomorphism onto the subspace, with the same specified
forward and inverse maps as the order correspondence. -/
def localization_homeomorphism : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    ∃ e : PrimeSpectrum (Localization S) ≃ₜ
        {p : PrimeSpectrum R // Disjoint (S : Set R) (p.asIdeal : Set R)},
      (∀ q, (e q).val = PrimeSpectrum.comap (algebraMap R (Localization S)) q) ∧
      (∀ p, (e.symm p).asIdeal = p.val.asIdeal.map (algebraMap R (Localization S)))

/-- The principal-localization specialization, including f = 0. -/
def principal_homeomorphism : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R),
    ∃ e : PrimeSpectrum (Localization.Away f) ≃ₜ
        {p : PrimeSpectrum R // p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))},
      (∀ q, (e q).val = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) q) ∧
      (∀ p, (e.symm p).asIdeal = p.val.asIdeal.map (algebraMap R (Localization.Away f)))

/-- When zero is inverted both spectra in the correspondence are empty. -/
def zero_in_submonoid : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), (0 : R) ∈ S →
    IsEmpty (PrimeSpectrum (Localization S)) ∧
      IsEmpty {p : PrimeSpectrum R // Disjoint (S : Set R) (p.asIdeal : Set R)}

end Specs.P103.Ch04.LocalizationSpectrum
