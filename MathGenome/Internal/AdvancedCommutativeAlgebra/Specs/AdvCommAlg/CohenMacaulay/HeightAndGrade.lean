import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! Independent statements for the ideal assertions of CM-07.
Heights and grades take values in ℕ∞; dimensions take values in WithBot ℕ∞.
The local assertion ranges over all proper ideals, including nonprime ideals. -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def grade_eq_heightType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ (I : Ideal R), I ≠ ⊤ →
      AdvCommAlg.Depth.Specs.gradeValue I R = I.height

def height_add_quotient_dimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    CohenMacaulayRingValue R → ∀ (I : Ideal R), I ≠ ⊤ →
      (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) = ringKrullDim R

end AdvCommAlg.CohenMacaulay.Specs
