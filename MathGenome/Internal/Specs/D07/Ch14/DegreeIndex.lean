import MathGenome.Internal.Specs.D07.Ch14.FixedField
import Mathlib.GroupTheory.Index

/-!
Independent specification of K07.14.degree_index (paper.tex:4173–4181).

The specified algebra structure records the embedding K → L. Finite degree
and the normal, separable Galois condition are separate hypotheses. The
intermediate field E is exactly the canonical field of elements fixed by H,
with its inherited scalar structures. The index counts left cosets: Mathlib's
`Subgroup.index` is `Nat.card (G ⧸ H)`. No normality of H is required.
All subgroups, including the trivial and full subgroups, are quantified over.
-/

universe u v

namespace Specs.D07.Ch14.DegreeIndex

/-- The three degree, subgroup-order, and index identities for E = L^H. -/
def DegreeIndexIdentities : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    let E := FixedField.fixedFieldValue K L H
    Module.finrank E L = Nat.card H ∧
      Module.finrank K E = H.index ∧
      Module.finrank K L = Nat.card (L ≃ₐ[K] L)

end Specs.D07.Ch14.DegreeIndex
