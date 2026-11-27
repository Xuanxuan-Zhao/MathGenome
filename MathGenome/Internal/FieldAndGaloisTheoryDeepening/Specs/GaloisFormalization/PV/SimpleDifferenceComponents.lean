import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace GaloisFormalization.PV.Specs

universe u

/-- A simple Noetherian difference ring is canonically a finite product of domains.
The forward permutation maps each minimal prime to its image under the automorphism.
The factor isomorphisms are compatible with this orientation on the product. -/
def simpleDifferenceComponents :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (σ : R ≃+* R), isSimple (difference σ) →
    Finite (minimalPrimes R) ∧ Nonempty (minimalPrimes R) ∧
    (∀ i : minimalPrimes R, IsDomain (R ⧸ i.val)) ∧
    ∃ (e : R ≃+* ((i : minimalPrimes R) → R ⧸ i.val))
      (p : Equiv.Perm (minimalPrimes R))
      (f : (i : minimalPrimes R) → (R ⧸ i.val) ≃+* (R ⧸ (p i).val)),
      (∀ i, (p i).val = i.val.map σ.toRingHom) ∧
      (∀ i j, ∃ n : ℤ, (p ^ n) i = j) ∧
      (∀ x i, e x i = Ideal.Quotient.mk i.val x) ∧
      (∀ x i, e (σ x) (p i) = f i (e x i))

end GaloisFormalization.PV.Specs
