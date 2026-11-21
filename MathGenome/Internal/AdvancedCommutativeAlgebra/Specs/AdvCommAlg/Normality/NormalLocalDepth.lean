import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic

/-! SN-07: depth is the regular-length depth, and dimension is Krull dimension.
The coercion to `WithBot ℕ∞` only aligns the codomains of these invariants. -/
namespace AdvCommAlg.Normality.Specs

def normal_local_depth_lower_boundType : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A],
    min (2 : WithBot ℕ∞) (ringKrullDim A) ≤
      (AdvCommAlg.Depth.Specs.depthValue A A : WithBot ℕ∞)

end AdvCommAlg.Normality.Specs
