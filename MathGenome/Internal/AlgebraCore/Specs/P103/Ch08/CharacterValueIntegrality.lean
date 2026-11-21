import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterConstructions
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-! The character-value assertion of Theorem 8.12, for every finite-dimensional
complex representation of a finite group, including the zero representation. -/

universe u v

namespace P103.Ch08.CharacterValueIntegralitySpecs

/-- `IsIntegral ℤ z` means that a monic polynomial over `ℤ` annihilates `z`. -/
def character_integralType : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G),
    IsIntegral ℤ (CharacterSpecs.characterValue ρ g)

end P103.Ch08.CharacterValueIntegralitySpecs
