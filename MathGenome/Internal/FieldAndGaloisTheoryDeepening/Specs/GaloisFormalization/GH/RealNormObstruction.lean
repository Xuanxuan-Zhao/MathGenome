import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.CyclicDegreeTwo
import Mathlib.LinearAlgebra.Complex.Module

set_option autoImplicit false

namespace GaloisFormalization.GH.RealNormObstruction

open Model
open scoped Algebra CyclicDegreeTwo

local notation "G" => (ℂ ≃ₐ[ℝ] ℂ)
local notation "A" => (Additive ℂˣ)

/-- The real relative second cohomology group has order two. Its unique nonidentity
class has the cocycle that takes the value `-1` on the pair of conjugations and `1`
on every other pair. -/
def Specification : Prop := by
  classical
  exact
    Nat.card (ContinuousMulH G ℂˣ 2) = 2 ∧
      ∃ c : continuousCocycles G A 2,
        (∀ g h : G, (c.val.val ![g, h]).toMul =
          if g = Complex.conjAe ∧ h = Complex.conjAe then -(1 : ℂˣ) else 1) ∧
        continuousMulClass G ℂˣ 2 (Multiplicative.ofAdd c) ≠ 1 ∧
        ∀ x : ContinuousMulH G ℂˣ 2, x ≠ 1 →
          x = continuousMulClass G ℂˣ 2 (Multiplicative.ofAdd c)

end GaloisFormalization.GH.RealNormObstruction
