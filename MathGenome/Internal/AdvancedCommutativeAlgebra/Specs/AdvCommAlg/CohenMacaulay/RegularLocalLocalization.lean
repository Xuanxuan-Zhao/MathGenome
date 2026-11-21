import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-! CM-19: every prime localization of a regular local ring is regular local.
No restriction is imposed on the prime, including the zero and maximal primes. -/
universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay.Specs

/-- Localizing any bounded projective resolution of R/p resolves κ(p),
with the same localized complex and the same length bound. -/
def localizedQuotient_boundedResolutionType : Prop :=
  ∀ (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : ProjectiveResolution (ModuleCat.of R (R ⧸ p))) (n : ℕ),
    (∀ i : ℕ, n < i → Subsingleton (P.complex.X i)) →
    ∃ Q : ProjectiveResolution (ModuleCat.of (Localization.AtPrime p) p.ResidueField),
      Q.complex = ((ModuleCat.localizedModuleFunctor.{u} p.primeCompl).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex ∧
      (∀ i : ℕ, n < i → Subsingleton (Q.complex.X i))

def residueField_localization_projectiveDimension_leType : Prop :=
  ∀ (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime],
    projectiveDimension (ModuleCat.of (Localization.AtPrime p) p.ResidueField) ≤
      projectiveDimension (ModuleCat.of R (R ⧸ p))

def regularLocal_localization_atPrimeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p)

end AdvCommAlg.CohenMacaulay.Specs
