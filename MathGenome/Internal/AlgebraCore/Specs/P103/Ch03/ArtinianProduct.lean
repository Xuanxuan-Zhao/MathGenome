import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.ArtinianRadical
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.LocalRing.Defs

/-!
Independent statements for the commutative product conclusion of Theorem 3.3
(paper.tex, lines 652–706), under the conventions at line 47.

The indexing type `MaximalSpectrum R` consists of ALL proper maximal ideals,
without repetition. `Finite` makes the dependent function ring below a finite
product. The factors are the canonical quotient rings R / m^N, and the formula
for the equivalence specifies the Chinese remainder map on every element.
`IsLocalRing` includes nontriviality and the unique-maximal-ideal condition;
`IsArtinianRing` refers to the descending chain condition on ideals.
No field, algebra, or nonzero-ring hypothesis is imposed on the decomposition.
The last statement identifies the zero-ring case with the empty product.
-/

universe u

namespace P103.Specs.Ch03.ArtinianProduct

open P103.Specs.Ch03.JacobsonRadical (radical)

def finite_maximalIdealsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsArtinianRing R], Finite (MaximalSpectrum R)

def factors_local_artinianType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsArtinianRing R] (N : ℕ), 0 < N →
    ∀ m : MaximalSpectrum R,
      IsLocalRing (R ⧸ m.asIdeal ^ N) ∧ IsArtinianRing (R ⧸ m.asIdeal ^ N)

/-- Any exponent annihilating the radical gives the displayed CRT isomorphism. -/
def chinese_remainderType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsArtinianRing R] (N : ℕ),
    radical R ^ N = ⊥ →
      ∃ e : R ≃+* ((m : MaximalSpectrum R) → R ⧸ m.asIdeal ^ N),
        ∀ (x : R) (m : MaximalSpectrum R), e x m = Ideal.Quotient.mk (m.asIdeal ^ N) x

/-- The complete finite local Artinian product decomposition, including zero. -/
def decompositionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsArtinianRing R],
    Finite (MaximalSpectrum R) ∧
      ∃ N : ℕ, 0 < N ∧ radical R ^ N = ⊥ ∧
        (∀ m : MaximalSpectrum R,
          IsLocalRing (R ⧸ m.asIdeal ^ N) ∧ IsArtinianRing (R ⧸ m.asIdeal ^ N)) ∧
        ∃ e : R ≃+* ((m : MaximalSpectrum R) → R ⧸ m.asIdeal ^ N),
          ∀ (x : R) (m : MaximalSpectrum R), e x m = Ideal.Quotient.mk (m.asIdeal ^ N) x

def zero_ringType : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R],
    IsEmpty (MaximalSpectrum R) ∧ Nonempty (R ≃+* (Fin 0 → R))

end P103.Specs.Ch03.ArtinianProduct
