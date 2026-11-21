import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height

/-! CM-09, converse, paper.tex:3456–3459 and 3483–3500.
A list presents an arbitrary finitely generated ideal. Associated primes here
are taken over R, so their heights are heights in the original ring.
The empty list is included; no local or finite-dimensional hypothesis is added.
-/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def unmixednessCriterionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    (∀ xs : List R, Ideal.ofList xs ≠ ⊤ →
      (Ideal.ofList xs).height = (xs.length : ℕ∞) →
      ∀ p : Ideal R, p ∈ associatedPrimes R (R ⧸ Ideal.ofList xs) →
        p.height = (xs.length : ℕ∞)) →
    CohenMacaulayRingValue R

end AdvCommAlg.CohenMacaulay.Specs
