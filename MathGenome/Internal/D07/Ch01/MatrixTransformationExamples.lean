import MathGenome.Internal.D07.Ch01.ElementaryGroupLaws
import MathGenome.Internal.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.Specs.D07.Ch01.MatrixTransformationExamples

/-!
# Matrix and transformation groups

`K07.01.matrix_transformation_examples`. GL is the units of the matrix ring,
and SL is identified with the determinant kernel without changing its matrices.
The two opposite transvections used below work in every characteristic.
-/

namespace D07.Ch01.MatrixTransformationExamples

open Matrix

universe u v w

theorem matrix_associativity :
    Specs.D07.Ch01.MatrixTransformationExamples.MatrixAssociativity.{u, v} := by
  intro ι F _ _ _ A B C
  exact Matrix.mul_assoc A B C

theorem gl_membership :
    Specs.D07.Ch01.MatrixTransformationExamples.GLMembership.{u, v} := by
  intro ι F _ _ _ A
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨↑g⁻¹, g.val_inv, g.inv_val⟩
  · rintro ⟨B, hAB, hBA⟩
    exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

theorem gl_group_operations :
    Specs.D07.Ch01.MatrixTransformationExamples.GLGroupOperations.{u, v} := by
  intro ι F _ _ _
  refine ⟨GroupDefinition.group_laws _, rfl, fun _ _ => rfl,
    GeneralLinearGroup.coe_inv, fun A => (A⁻¹).isUnit, ?_⟩
  intro A B
  rw [ElementaryGroupLaws.product_inverse, GeneralLinearGroup.coe_mul,
    GeneralLinearGroup.coe_inv, GeneralLinearGroup.coe_inv]

theorem determinant_laws :
    Specs.D07.Ch01.MatrixTransformationExamples.DeterminantLaws.{u, v} := by
  intro ι F _ _ _
  refine ⟨Matrix.det_one, Matrix.det_mul, ?_⟩
  intro A
  simpa only [GeneralLinearGroup.val_det_apply, Units.val_inv_eq_inv_val] using
    congrArg Units.val ((GeneralLinearGroup.det : GeneralLinearGroup ι F →* Fˣ).map_inv A)

theorem determinant_one_closure :
    Specs.D07.Ch01.MatrixTransformationExamples.DeterminantOneClosure.{u, v} := by
  intro ι F _ _ _
  refine ⟨Matrix.det_one, ?_, ?_, ?_⟩
  · intro A B hA hB
    rw [Matrix.det_mul, hA, hB, one_mul]
  · intro A hA
    rw [Matrix.det_nonsing_inv, hA, Ring.inverse_one]
  · intro A hA
    exact (Matrix.isUnit_iff_isUnit_det A).2 (hA.symm ▸ isUnit_one)

theorem special_linear_subgroup :
    Specs.D07.Ch01.MatrixTransformationExamples.SpecialLinearSubgroup.{u, v} := by
  intro ι F _ _ _
  refine ⟨(GeneralLinearGroup.det : GeneralLinearGroup ι F →* Fˣ).ker, ?_,
    SpecialLinearGroup.toGLKerEquiv, fun _ => rfl⟩
  intro A
  change GeneralLinearGroup.det A = 1 ↔ _
  exact Units.ext_iff

/-- The `(i,i)` entries of the two products differ by one. This proof uses
only `1 ≠ 0`, so in particular does not exclude characteristic two. -/
theorem opposite_transvections_ne {ι : Type u} {F : Type v}
    [Fintype ι] [DecidableEq ι] [Field F] (i j : ι) (hij : i ≠ j) :
    transvection i j (1 : F) * transvection j i 1 ≠
      transvection j i 1 * transvection i j 1 := by
  intro h
  have he := congrArg (fun M : Matrix ι ι F => M i i) h
  rw [transvection_mul_apply_same,
    transvection_mul_apply_of_ne _ _ _ _ hij] at he
  simp [transvection, hij.symm] at he

theorem gl_noncommutative :
    Specs.D07.Ch01.MatrixTransformationExamples.GLNoncommutative.{v} := by
  intro F _ n hn
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  let A : SpecialLinearGroup (Fin n) F := SpecialLinearGroup.transvection hij 1
  let B : SpecialLinearGroup (Fin n) F := SpecialLinearGroup.transvection hij.symm 1
  refine ⟨SpecialLinearGroup.toGL A, SpecialLinearGroup.toGL B, ?_⟩
  intro h
  exact opposite_transvections_ne i j hij
    (congrArg (fun g : GeneralLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h)

theorem permutation_membership :
    Specs.D07.Ch01.MatrixTransformationExamples.PermutationMembership.{u} := by
  intro X f
  constructor
  · intro hf
    exact ⟨Equiv.ofBijective f hf, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.bijective

theorem permutation_group_operations :
    Specs.D07.Ch01.MatrixTransformationExamples.PermutationGroupOperations.{u} := by
  intro X
  exact ⟨GroupDefinition.group_laws _, fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

theorem empty_permutation :
    Specs.D07.Ch01.MatrixTransformationExamples.EmptyPermutation.{u} := by
  intro X _
  constructor
  · refine ⟨id, Function.bijective_id, ?_⟩
    intro f _
    exact funext fun x => isEmptyElim x
  · intro e
    have he : e = 1 := Equiv.ext fun x => isEmptyElim x
    exact ⟨he, by rw [he, inv_one]⟩

theorem isometry_family_subgroup :
    Specs.D07.Ch01.MatrixTransformationExamples.IsometryFamilySubgroup.{u} := by
  intro X _ s hIso h1 hmul hinv
  obtain ⟨H, hH⟩ :=
    (SubgroupDefinitionTest.subgroup_iff_closed (Equiv.Perm X) s).2 ⟨h1, hmul, hinv⟩
  refine ⟨H, hH, ?_⟩
  intro f
  exact hIso f.val (hH ▸ f.property)

theorem endomorphism_monoid :
    Specs.D07.Ch01.MatrixTransformationExamples.EndomorphismMonoid.{v, w} := by
  intro F V _ _ _
  exact ⟨mul_assoc, fun f => ⟨one_mul f, mul_one f⟩, fun _ _ _ => rfl, fun _ => rfl⟩

theorem zero_endomorphism_not_invertible :
    Specs.D07.Ch01.MatrixTransformationExamples.ZeroEndomorphismNotInvertible.{v, w} := by
  intro F V _ _ _ _
  rintro ⟨f, hf⟩
  exact zero_ne_one ((zero_mul f).symm.trans hf)

theorem no_endomorphism_group :
    Specs.D07.Ch01.MatrixTransformationExamples.NoEndomorphismGroup.{v, w} := by
  intro F V _ _ _ _
  rintro ⟨g, hg⟩
  apply zero_endomorphism_not_invertible F V
  refine ⟨g.inv 0, ?_⟩
  have h : g.toMonoid.mul 0 (g.inv 0) = g.toMonoid.one :=
    @mul_inv_cancel (Module.End F V) g 0
  rw [hg] at h
  exact h

end D07.Ch01.MatrixTransformationExamples
