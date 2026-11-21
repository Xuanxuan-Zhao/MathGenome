import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
Independent specification for the localization step of K07.22.lying_over,
paper.tex:7309–7316, with the chapter conventions at 6699–6703.

An inclusion is represented by an injective unital ring homomorphism. The
denominators in B are exactly the image of the denominators in R. No domain,
regular-denominator, Noetherian, or nonzero-ring hypothesis is imposed.
The first three assertions and the explicit equation hold for any submonoid;
the nonzeroness assertion uses precisely the complement of a prime ideal.
-/

universe u v

namespace Specs.D07.Ch22.LyingOverIntegralLocalizationInclusion

open Polynomial
open scoped BigOperators

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B]

/-- The denominator s in B is the image of the same denominator in R. -/
def mappedDenominator (f : R →+* B) (S : Submonoid R) (s : S) : S.map f :=
  ⟨f s, Submonoid.mem_map.mpr ⟨s, s.property, rfl⟩⟩

/-- The canonical map induced by the original ring homomorphism. -/
noncomputable def localizationMap (f : R →+* B) (S : Submonoid R) :
    Localization S →+* Localization (S.map f) :=
  IsLocalization.map (Localization (S.map f)) f S.le_comap_map

/-- The exact polynomial from the source: its i-th lower coefficient is
a_i / s^(n-i), in particular a_(n-1)/s and a_0/s^n. -/
noncomputable def fractionPolynomial (S : Submonoid R) (n : ℕ)
    (a : ℕ → R) (s : S) : Polynomial (Localization S) :=
  X ^ n + ∑ i ∈ Finset.range n, C (Localization.mk (a i) (s ^ (n - i))) * X ^ i

def MapOnFractions : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
      (f : R →+* B) (S : Submonoid R) (r : R) (s : S),
    localizationMap f S (Localization.mk r s) =
      Localization.mk (f r) (mappedDenominator f S s)

def MapInjective : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
      (f : R →+* B) (S : Submonoid R),
    Function.Injective f → Function.Injective (localizationMap f S)

def MapIntegral : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
      (f : R →+* B) (S : Submonoid R),
    f.IsIntegral → (localizationMap f S).IsIntegral

/-- The nonzero source localization embeds in the target localization.
Only a prime of R is assumed; its image need not be a prime of B. -/
def NonzeroAtPrime : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
      (f : R →+* B) (P : Ideal R) [P.IsPrime],
    Function.Injective f →
      Nontrivial (Localization.AtPrime P) ∧
      Nontrivial (Localization (P.primeCompl.map f))

/-- Every supplied positive-exponent monic equation gives the specific
displayed monic polynomial and equation for b/s, not just some integral
equation. All lower coefficients and their powers of s are fixed. -/
def FractionMonicEquation : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
      (f : R →+* B) (S : Submonoid R) (b : B) (s : S)
      (n : ℕ) (_hn : 0 < n) (a : ℕ → R),
    b ^ n + ∑ i ∈ Finset.range n, f (a i) * b ^ i = 0 →
    let x := Localization.mk b (mappedDenominator f S s)
    (fractionPolynomial S n a s).Monic ∧
      (fractionPolynomial S n a s).eval₂ (localizationMap f S) x = 0 ∧
      x ^ n + ∑ i ∈ Finset.range n,
        localizationMap f S (Localization.mk (a i) (s ^ (n - i))) * x ^ i = 0

end Specs.D07.Ch22.LyingOverIntegralLocalizationInclusion
