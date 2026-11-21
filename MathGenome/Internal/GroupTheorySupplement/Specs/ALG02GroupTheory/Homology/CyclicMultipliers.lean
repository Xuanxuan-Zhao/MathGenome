import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.IntegralBar
import Mathlib.Data.ZMod.Basic

namespace Specs.ALG02GroupTheory.CyclicMultipliers

open _root_.ALG02GroupTheory.IntegralBar

/-- The integral second homology of the cyclic group of positive order vanishes. -/
def CyclicVanishing : Prop :=
  ∀ m : ℕ, 0 < m → Subsingleton (homology (Multiplicative (ZMod m)) 2)

/-- The integral second homology of two cyclic groups is cyclic of the gcd order. -/
def CyclicProduct : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    Nonempty (homology (Multiplicative (ZMod m) × Multiplicative (ZMod n)) 2 ≃+
      ZMod (Nat.gcd m n))

end Specs.ALG02GroupTheory.CyclicMultipliers
