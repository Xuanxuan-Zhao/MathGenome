import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.ProfiniteIntegers.IntegerDensity

/-! FT-E07, advanced-field-theory.tex:1225–1254. Properness concerns the
ordinary integer image and ordinary cyclic subgroup, with the Krull topology. -/
universe u v
namespace Specs.AdvancedFieldTheory.DenseProperCyclicSubgroup

open AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem

/-- The canonical image is a proper subset of the literal residue-family group. -/
def IntegerImageProper : Prop :=
  Set.range integerResidues ⊂ (Set.univ : Set ResidueFamily)

/-- The complete conclusion of E07, for every chosen closure of a finite field. -/
def FrobeniusDenseProperFixedField : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
    Dense (Subgroup.zpowers (globalFrobenius_value k Ω) : Set (Ω ≃ₐ[k] Ω)) ∧
    Subgroup.zpowers (globalFrobenius_value k Ω) ≠ ⊤ ∧
    IntermediateField.fixedField (Subgroup.zpowers (globalFrobenius_value k Ω)) =
      (⊥ : IntermediateField k Ω)

end Specs.AdvancedFieldTheory.DenseProperCyclicSubgroup
