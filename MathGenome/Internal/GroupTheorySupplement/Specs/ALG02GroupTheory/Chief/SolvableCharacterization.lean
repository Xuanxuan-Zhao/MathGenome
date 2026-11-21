import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Series
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Solvable

/-! The solvability criterion in Corollary 1.4 of the group theory notes. -/

namespace Specs.ALG02GroupTheory.Chief.SolvableCharacterization

open Specs.ALG02GroupTheory.Chief.Series

universe u

/-- A finite group is solvable exactly when it has a chief series whose factors
are abelian of prime exponent. The prime may vary with the step. -/
def SolvableIffChiefSeriesElementaryAbelian : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Group.IsSolvable G ↔
      ∃ s : Chain G, ∀ i : Fin s.length,
        ∃ p : ℕ, p.Prime ∧ IsMulCommutative (chiefFactorValue s i) ∧
          Monoid.exponent (chiefFactorValue s i) = p

end Specs.ALG02GroupTheory.Chief.SolvableCharacterization
