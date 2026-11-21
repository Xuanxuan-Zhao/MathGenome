import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
Independent specifications for K07.22.lying_over, paper.tex:7286–7333.

An inclusion is an injective unital ring homomorphism. Integrality is
elementwise integrality for this very homomorphism, and contraction is
the literal inverse image of an ideal. Both rings are arbitrary
commutative unital rings; in particular neither is assumed to be a
domain, Noetherian, or nonzero. Prime ideals are proper.

The second assertion records the subsequent noninjective formulation:
precisely the primes containing the kernel have a prime above them.
The field criterion and localization statements inside the source proof
are supplied by the separately assigned prerequisite goals.
-/

universe u v

namespace Specs.D07.Ch22.LyingOver

/-- Every prime of the base of an integral inclusion has a prime above it. -/
def PrimeLyingOver : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    (f : R →+* B), Function.Injective f → f.IsIntegral →
    ∀ P : Ideal R, P.IsPrime →
      ∃ Q : Ideal B, Q.IsPrime ∧ Ideal.comap f Q = P

/-- For an integral map, the kernel condition is necessary and sufficient.
This includes the noninjective case mentioned after the source theorem. -/
def LyingOverIffKernelLe : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    (f : R →+* B), f.IsIntegral →
    ∀ P : Ideal R, P.IsPrime →
      ((∃ Q : Ideal B, Q.IsPrime ∧ Ideal.comap f Q = P) ↔ RingHom.ker f ≤ P)

/-- The zero-ring boundary: it has no prime ideal. -/
def ZeroRingNoPrimes : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R] (P : Ideal R), ¬ P.IsPrime

end Specs.D07.Ch22.LyingOver
