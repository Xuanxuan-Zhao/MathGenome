import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.FractionRing

namespace Specs.CommutativeAlgebraNotes.DerivationsOfNonPowers

open FrobeniusCoefficientDefinitions

universe u v w

/-- Lemma 5.5. An element of the domain whose image in its fraction field
is outside the Frobenius image is detected by an absolute derivation. The
extension of fraction fields is taken along the given embedding of algebras. -/
def DerivationsDetectNonPowers : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (r s : ℕ),
    let S := CoefficientTowerBase k r s
    ∀ (B : Type v) [CommRing B] [IsDomain B] [Algebra S B] [Algebra.FiniteType S B]
      (hSB : Function.Injective (algebraMap S B))
      (F : Type w) [Field F] [Algebra B F] [IsFractionRing B F],
      letI : Algebra (FractionRing S) F :=
        (IsFractionRing.lift (K := FractionRing S)
          (g := (algebraMap B F).comp (algebraMap S B))
          ((IsFractionRing.injective B F).comp hSB)).toAlgebra
      ∀ [Module.Finite (FractionRing S) F] (f : B),
        (¬ ∃ x : F, x ^ p = algebraMap B F f) →
        ∃ D : Derivation ℤ B B, D f ≠ 0

end Specs.CommutativeAlgebraNotes.DerivationsOfNonPowers
