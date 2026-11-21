import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimaryDecomposition
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Order.Minimal

/-!
The localization formula and minimal-component uniqueness in Theorem 5.5,
paper.tex:1004–1009,1020. The ambient fraction module and localized submodule
are those of Chapter 4. Disjointness is literal set disjointness, so the
intersection includes precisely the components whose radicals avoid S.
-/
namespace P103.Specs.Ch05.PrimaryLocalizationUniqueness

universe u v
open P103.Specs.Ch05.PrimaryDecomposition
open P103.Specs.Ch05.PrimarySubmodules
open P103.Specs.Ch05.AssociatedPrimesInterface

def ContractionType := ∀ (R : Type u) [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M], Submonoid R → Submodule R M → Submodule R M

/-- The intrinsic submodule {m | m/1 ∈ S⁻¹N}. -/
noncomputable def contractionValue : ContractionType.{u,v} := fun R _ M _ _ S N =>
  ((N.localized S).restrictScalars R).comap (LocalizedModule.mkLinearMap S M)

def localizationFormulaType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (s : Finset (Submodule R M)), IsDecomposition N s →
    ∀ S : Submonoid R,
      contractionValue R M S N =
        ⨅ Q ∈ s, ⨅ (_ : Disjoint (radicalValue R M Q : Set R) (S : Set R)), Q

/-- If no component survives, the formula gives all of M. This also
covers multiplicative sets containing zero. -/
def emptyIntersectionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (s : Finset (Submodule R M)), IsDecomposition N s →
    ∀ S : Submonoid R,
      (∀ Q ∈ s, ¬ Disjoint (radicalValue R M Q : Set R) (S : Set R)) →
      contractionValue R M S N = ⊤

/-- Every decomposition has a component for a minimal associated prime,
and every component for that prime equals the intrinsic contraction. -/
def minimalComponentType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (s : Finset (Submodule R M)), IsDecomposition N s →
    ∀ p : PrimeSpectrum R,
      Minimal (fun q => q ∈ associatedPrimesValue R (M ⧸ N)) p.asIdeal →
      (∃ Q ∈ s, radicalValue R M Q = p.asIdeal) ∧
      ∀ Q ∈ s, radicalValue R M Q = p.asIdeal →
        Q = contractionValue R M p.asIdeal.primeCompl N

/-- Equality across arbitrary irredundant decompositions with distinct
radicals. No uniqueness is asserted for embedded associated primes. -/
def minimalComponentUniqueType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (s t : Finset (Submodule R M)),
    IsDecomposition N s → IsDecomposition N t →
    ∀ p : PrimeSpectrum R,
      Minimal (fun q => q ∈ associatedPrimesValue R (M ⧸ N)) p.asIdeal →
      ∀ Q ∈ s, ∀ P ∈ t,
        radicalValue R M Q = p.asIdeal → radicalValue R M P = p.asIdeal → Q = P

end P103.Specs.Ch05.PrimaryLocalizationUniqueness
