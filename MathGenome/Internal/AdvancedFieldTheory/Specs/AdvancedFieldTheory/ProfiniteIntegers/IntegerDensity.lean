import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.AbsoluteGaloisGroup
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-! FT-E07A: density and fixed field in the chosen algebraic closure.
The cyclic subgroup is the ordinary subgroup of integer powers. -/
universe u v
namespace Specs.AdvancedFieldTheory.IntegerDensity

open AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem

def FiniteCoordinateMatching : Prop :=
  ∀ (a : ResidueFamily) (s : Finset ℕ+),
    ∃ z : ℤ, ∀ n ∈ s, coordinate n (integerResidues z) = coordinate n a

def IntegerDense : Prop := DenseRange integerResidues

def FrobeniusCyclicDense : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
    Dense (Subgroup.zpowers (globalFrobenius_value k Ω) : Set (Ω ≃ₐ[k] Ω))

def FrobeniusCyclicFixedField : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
    IntermediateField.fixedField (Subgroup.zpowers (globalFrobenius_value k Ω)) =
      (⊥ : IntermediateField k Ω)

end Specs.AdvancedFieldTheory.IntegerDensity
