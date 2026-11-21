import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.SplittingFields
import Mathlib.FieldTheory.SplittingField.Construction

namespace P203.Ch02

universe u v w

/-- The distinct-root bound preceding Lemma 2.2. -/
theorem root_bound : P203Specs.Ch02.rootBoundStatement.{u, v} := by
  intro K _ L _ _ f hf
  have hroots : f.rootSet L = {x : L | Polynomial.aeval x f = 0} := by
    ext x
    exact Polynomial.mem_rootSet_of_ne hf
  rw [← hroots]
  exact ⟨f.rootSet_finite L, f.ncard_rootSet_le L⟩

/-- Lemma 2.2, existence: choose the library's constructed splitting field. -/
theorem splitting_field_exists : P203Specs.Ch02.splittingFieldExistenceStatement.{u} := by
  intro K _ f _
  refine ⟨f.SplittingField, inferInstance, inferInstance, ?_⟩
  exact isSplittingField_iff_intermediateField.mp inferInstance

/-- Lemma 2.2, uniqueness up to an isomorphism fixing the base field. -/
theorem splitting_field_unique :
    P203Specs.Ch02.splittingFieldUniquenessStatement.{u, v, w} := by
  intro K _ f _ L _ _ M _ _ hL hgenL hM hgenM
  have : Polynomial.IsSplittingField K L f :=
    isSplittingField_iff_intermediateField.mpr ⟨hL, hgenL⟩
  have : Polynomial.IsSplittingField K M f :=
    isSplittingField_iff_intermediateField.mpr ⟨hM, hgenM⟩
  exact ⟨(Polynomial.IsSplittingField.algEquiv L f).trans
    (Polynomial.IsSplittingField.algEquiv M f).symm⟩

end P203.Ch02
