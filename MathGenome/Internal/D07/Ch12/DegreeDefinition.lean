import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition
import MathGenome.Internal.D07.Ch12.ExtensionDefinition

/-! Extension degree and finite degree for a field extension with its chosen
scalar action. No finiteness or algebraicity is required to define degree. -/

universe u v

namespace D07.Ch12.DegreeDefinition

noncomputable section

/-- The cardinal dimension of L over K for the specified Algebra structure. -/
def degree (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Cardinal.{v} :=
  Module.rank K L

/-- Degree of an extension given by its chosen unital field map. The induced
scalar action is the one constructed in ExtensionDefinition. -/
def degreeOf (K : Type u) (L : Type v) [Field K] [Field L]
    (ι : ExtensionDefinition.FieldExtension K L) : Cardinal.{v} :=
  letI := ExtensionDefinition.extensionAlgebra K L ι
  degree K L

/-- Finite degree is finiteness of dimension, not of the underlying set. -/
def IsFiniteExtension (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Prop :=
  ∃ n : ℕ, degree K L = (n : Cardinal.{v})

theorem finite_iff_finiteDimensional (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] :
    IsFiniteExtension K L ↔ FiniteDimensional K L :=
  Cardinal.lt_aleph0.symm.trans Module.rank_lt_aleph0_iff

theorem finite_iff_degree_lt_aleph0 (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] :
    IsFiniteExtension K L ↔ degree K L < Cardinal.aleph0 := by
  rw [finite_iff_finiteDimensional]
  exact Module.rank_lt_aleph0_iff.symm

theorem degree_eq_finrank (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    degree K L = (Module.finrank K L : Cardinal.{v}) :=
  (Module.finrank_eq_rank K L).symm

theorem degree_eq_nat_iff (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (n : ℕ) :
    degree K L = (n : Cardinal.{v}) ↔
      FiniteDimensional K L ∧ Module.finrank K L = n := by
  constructor
  · intro h
    have : FiniteDimensional K L := (finite_iff_finiteDimensional K L).mp ⟨n, h⟩
    refine ⟨inferInstance, ?_⟩
    exact Nat.cast_injective ((degree_eq_finrank K L).symm.trans h)
  · rintro ⟨h, hn⟩
    let := h
    rw [degree_eq_finrank, hn]

/-- The structure map already injects the infinite base field into L. The
finite-degree hypothesis is retained to state precisely the source's claim. -/
theorem finite_extension_of_infinite_base (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Infinite K]
    (_h : IsFiniteExtension K L) : Infinite L := by
  exact Infinite.of_injective (algebraMap K L)
    (ExtensionDefinition.structure_map_injective K L (algebraMap K L))

end

end D07.Ch12.DegreeDefinition
