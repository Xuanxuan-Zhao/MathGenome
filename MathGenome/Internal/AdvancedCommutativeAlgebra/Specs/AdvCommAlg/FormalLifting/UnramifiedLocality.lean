import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-! Independent statements for the formal-unramified locality assertions of
FL-10 (paper.tex:683–719). Formal unramifiedness means uniqueness of lifts
through square-zero quotients, as in FL-01. No finiteness hypothesis is imposed
on the algebra. The finite family may be empty, and the zero ring is allowed.
-/
namespace Specs.AdvCommAlg.FormalLifting.UnramifiedLocality

universe u v

/-- A finite family generating the unit ideal detects formal unramifiedness.
For `n = 0`, the unit-ideal condition says that the target ring is zero. -/
def finitePrincipalCover : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (b : Fin n → B), Ideal.span (Set.range b) = ⊤ →
      (formallyUnramifiedValue A B ↔
        ∀ i, formallyUnramifiedValue A (Localization.Away (b i)))

/-- Formal unramifiedness is equivalent to formal unramifiedness of the
localization at every prime of the target. This also applies to empty spectra. -/
def primeLocalizations : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    formallyUnramifiedValue A B ↔
      ∀ q : PrimeSpectrum B,
        formallyUnramifiedValue A (Localization.AtPrime q.asIdeal)

end Specs.AdvCommAlg.FormalLifting.UnramifiedLocality
