import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic

/-! Independent statement for the associated-prime inequality in DP-10,
`paper.tex:2976–2982`. The dimension is the full dimension of R/p.
No restriction to minimal associated primes is made. -/

universe u v
namespace AdvCommAlg.Depth.Specs

def depth_le_dim_quotient_of_associatedPrimeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (p : Ideal R), p ∈ associatedPrimes R M →
      (depthValue R M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)

end AdvCommAlg.Depth.Specs
