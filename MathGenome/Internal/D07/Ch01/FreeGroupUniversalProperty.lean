import MathGenome.Internal.Specs.D07.Ch01.FreeGroupUniversalProperty
import MathGenome.Internal.D07.Ch01.FreeGroupUniversalPropertyReducedWords
import MathGenome.Internal.D07.Ch01.HomOnGenerators

/-!
# The free group on an arbitrary generator type

We use the canonical signed-word quotient already used by the upstream normal
form theorem. Mathlib's `FreeGroup.lift` evaluates signed words and descends to
this quotient because deleting an adjacent inverse pair preserves evaluation.
It is multiplicative by the ordered-product formula for concatenation.
Uniqueness follows from agreement on generators and generation of the free
group. The final existence theorem uses this same group for the universal
property and the unique reduced representatives, including empty generators.
-/

namespace D07.Ch01.FreeGroupUniversalProperty

open Specs.D07.Ch01.FreeGroupUniversalProperty

universe u v

theorem generators_generate : GeneratorsGenerate.{u} := by
  intro S
  exact FreeGroup.closure_range_of S

theorem universal_property : UniversalProperty.{u, v} := by
  intro S H _ f
  refine ⟨FreeGroup.lift f, fun s => FreeGroup.lift_apply_of, ?_⟩
  intro φ hφ
  apply MonoidHom.ext
  intro x
  apply HomOnGenerators.agree_on_generated (FreeGroup S) H φ (FreeGroup.lift f)
    (Set.range FreeGroup.of)
  · rintro _ ⟨s, rfl⟩
    exact (hφ s).trans FreeGroup.lift_apply_of.symm
  · rw [generators_generate S]
    exact Subgroup.mem_top x

theorem evaluation_on_words : EvaluationOnWords.{u, v} := by
  intro S H _ f w
  simpa only [Bool.cond_eq_ite] using (FreeGroup.lift_mk (f := f) (L := w))

theorem free_group_exists : FreeGroupExists.{u, v} := by
  intro S
  refine ⟨FreeGroup S, inferInstance, FreeGroup.of, FreeGroup.mk,
    universal_property S, FreeGroupUniversalPropertyReducedWords.signed_letters S,
    rfl, ?_, ?_, FreeGroupUniversalPropertyReducedWords.unique_reduced_representative S⟩
  · intro a b
    exact FreeGroup.mul_mk.symm
  · intro a
    exact FreeGroup.inv_mk.symm

theorem empty_generators : EmptyGenerators.{u} := by
  intro S _
  exact (FreeGroupUniversalPropertyReducedWords.empty_generators S).2

end D07.Ch01.FreeGroupUniversalProperty
