import MathGenome.Internal.Specs.D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
import MathGenome.Internal.Specs.D07.Ch15.RadicalDefinition
import Mathlib.GroupTheory.Solvable

/-!
Independent statements for K07.15.explicit_S5_quintic, paper.tex:4467–4477.
The rational polynomial is the canonical polynomial from the root-group
prerequisite. Its polynomial Galois group is the automorphism group of its
splitting field. Radical solvability means membership in an actual finite
radical tower, with the specified rational embedding in an algebraic overfield.
-/

universe u

namespace Specs.D07.Ch15.ExplicitS5Quintic

open Polynomial ExplicitS5QuinticQuinticRealRootsAndGroup RadicalDefinition

def GaloisGroupS5 : Prop := Nonempty (quintic.Gal ≃* Equiv.Perm (Fin 5))

def GaloisGroupNotSolvable : Prop := ¬ Group.IsSolvable quintic.Gal

/-- Every root is excluded, in any specified algebraic overfield of ℚ. -/
def NoRadicalRoot : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (a : Ω),
    aeval a quintic = 0 → ¬ solvableByRadicalsValue ℚ Ω a

/-- The full conclusion of the source theorem. -/
def FullConclusion : Prop := GaloisGroupS5 ∧ NoRadicalRoot.{u}

end Specs.D07.Ch15.ExplicitS5Quintic
