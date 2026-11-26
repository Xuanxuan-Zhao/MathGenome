import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing

namespace CommutativeAlgebraNotes.Specs

universe u v w

/-- A finite extension of the fraction field of a domain has a finite subalgebra model
over that domain. The given field is the fraction field via the subalgebra inclusion. -/
def existsFiniteDomainModel : Prop :=
  ∀ (S : Type u) (K : Type v) (M : Type w)
    [CommRing S] [IsDomain S] [Field K] [Field M]
    [Algebra S K] [IsFractionRing S K] [Algebra K M] [Module.Finite K M]
    [Algebra S M] [IsScalarTower S K M],
    ∃ B : Subalgebra S M, IsDomain B ∧ Module.Finite S B ∧ IsFractionRing B M

/-- A nonzero denominator in a fraction field can be taken to a positive power
while still clearing the denominator of a given element. -/
def existsPowMulMem : Prop :=
  ∀ (S : Type u) (M : Type w) [CommRing S] [Field M] [Algebra S M]
    (B : Subalgebra S M) [IsFractionRing B M] (f : M) (p : ℕ), 0 < p →
    ∃ b : B, b ≠ 0 ∧ (algebraMap B M b) ^ p * f ∈ B

/-- Multiplying a radicand by a power of a nonzero scalar changes the distinguished
root by that scalar in the binomial adjunction. -/
def existsScaledAdjoinRootEquiv : Prop :=
  ∀ (M : Type w) [Field M] (p : ℕ) (f c : M), c ≠ 0 →
    ∃ e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C (c ^ p * f)) ≃ₐ[M]
        AdjoinRoot (Polynomial.X ^ p - Polynomial.C f),
      e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C (c ^ p * f))) =
        algebraMap M _ c * AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C f)

end CommutativeAlgebraNotes.Specs
