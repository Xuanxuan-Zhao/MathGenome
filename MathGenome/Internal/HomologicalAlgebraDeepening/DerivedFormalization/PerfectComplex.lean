import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Cochains
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs

/-! Perfect complexes over a commutative ring. -/

namespace DerivedFormalization

open CategoryTheory

universe v u

variable {R : Type u} [CommRing R]

/-- A cochain complex of finitely generated projective modules whose terms vanish
outside a bounded interval of integer degrees. -/
def IsBoundedFiniteProjective (C : Comp.{v} R) : Prop :=
  (∀ i : ℤ, Module.Finite R (C.X i) ∧ Module.Projective R (C.X i)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → Limits.IsZero (C.X i)

/-- A derived object is perfect if it is isomorphic to the image of a bounded
cochain complex of finitely generated projective modules. -/
def IsPerfect (P : D.{v} R) : Prop :=
  ∃ C : Comp.{v} R, IsBoundedFiniteProjective C ∧ Nonempty (P ≅ (Q R).obj C)

end DerivedFormalization
