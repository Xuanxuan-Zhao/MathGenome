import MathGenome.Internal.Specs.D07.Ch14.SplittingCriterion
import MathGenome.Internal.D07.Ch12.SplittingExistenceUniqueness
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparableClosure

/-!
Galois extensions as separable splitting fields, K07.14.splitting_criterion.

For the forward implication, a primitive element's minimal polynomial is
separable and splits by normality. Its roots generate the extension since
they contain the primitive element. Conversely, the splitting-field bridge
gives normality, and separability follows from generation by separable roots.
Finiteness uses the upstream splitting-field theorem, with no finiteness
assumed of the extension or either underlying field.
-/

universe u v

namespace D07.Ch14.SplittingCriterion

open Polynomial Specs.D07.Ch14.SplittingCriterion

theorem separableSplittingFieldFinite : SeparableSplittingFieldFinite.{u, v} := by
  intro K L _ _ _ f _hf hsplit
  exact Ch12.SplittingExistenceUniqueness.finiteSplittingField K L f hsplit

theorem separableSplittingFieldGalois : SeparableSplittingFieldGalois.{u, v} := by
  intro K L _ _ _ f hf hsplit
  let : Polynomial.IsSplittingField K L f :=
    (Ch12.SplittingDefinition.library_characterization K L f hsplit.1).mp hsplit
  let : Algebra.IsSeparable K L :=
    Algebra.isSeparable_of_separable_splitting_field K L hf
  exact ⟨inferInstance, Normal.of_isSplittingField f,
    show Algebra.IsSeparable K L from inferInstance⟩

theorem finiteGaloisIffSeparableSplittingField :
    FiniteGaloisIffSeparableSplittingField.{u, v} := by
  intro K L _ _ _ hfinite
  let : FiniteDimensional K L :=
    (Ch12.DegreeDefinition.finite_iff_finiteDimensional K L).mp hfinite
  constructor
  · rintro ⟨_halg, hnormal, hsep⟩
    let : Normal K L := hnormal
    let : Algebra.IsSeparable K L := hsep
    obtain ⟨a, ha⟩ := Field.exists_primitive_element K L
    have hint : IsIntegral K a := Algebra.IsSeparable.isIntegral K a
    refine ⟨minpoly K a, Algebra.IsSeparable.isSeparable K a,
      minpoly.ne_zero hint, hnormal.splits a, ?_⟩
    apply top_unique
    rw [← ha]
    apply IntermediateField.adjoin.mono
    intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    exact Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, minpoly.aeval K a⟩
  · rintro ⟨f, hf, hsplit⟩
    exact separableSplittingFieldGalois K L f hf hsplit

end D07.Ch14.SplittingCriterion
