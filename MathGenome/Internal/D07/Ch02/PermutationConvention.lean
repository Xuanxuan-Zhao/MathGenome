import MathGenome.Internal.D07.Ch01.MatrixTransformationExamples
import MathGenome.Internal.Specs.D07.Ch02.PermutationConvention

/-!
# Permutations and cycle notation

`K07.02.permutation_convention`: multiplication applies the right factor first.
The empty symmetric group and singleton cycles are included. The one-based
label correspondence explains the use of `Fin n` for the source's n symbols.
-/

namespace D07.Ch02.PermutationConvention

universe u

abbrev PermutationGroup (X : Type u) : Type u := Equiv.Perm X

abbrev SymmetricGroup (n : ℕ) : Type := PermutationGroup (Fin n)

/-- The permutation written as a cycle with the given distinct entries. -/
noncomputable def listedCycle (X : Type u) (l : List X) (_h : l.Nodup) :
    PermutationGroup X := by
  classical
  exact l.formPerm

theorem bijection_membership :
    Specs.D07.Ch02.PermutationConvention.BijectionMembership.{u} :=
  D07.Ch01.MatrixTransformationExamples.permutation_membership

theorem group_operations :
    Specs.D07.Ch02.PermutationConvention.GroupOperations.{u} :=
  D07.Ch01.MatrixTransformationExamples.permutation_group_operations

theorem finite_labels : Specs.D07.Ch02.PermutationConvention.FiniteLabels := by
  intro n
  refine ⟨{
    toFun := fun i => ⟨i.val + 1, by omega⟩
    invFun := fun k => ⟨k.val - 1, by omega⟩
    left_inv := ?_
    right_inv := ?_
  }, fun _ => rfl⟩
  · intro i
    apply Fin.ext
    simp
  · intro k
    apply Subtype.ext
    dsimp
    have := k.property
    omega

theorem empty_symmetric_group :
    Specs.D07.Ch02.PermutationConvention.EmptySymmetricGroup := by
  exact (D07.Ch01.MatrixTransformationExamples.empty_permutation (Fin 0)).2

theorem cycle_successor :
    Specs.D07.Ch02.PermutationConvention.CycleSuccessor.{u} := by
  classical
  intro X l h i hi
  exact List.formPerm_apply_lt_getElem l h i hi

theorem cycle_wraparound :
    Specs.D07.Ch02.PermutationConvention.CycleWraparound.{u} := by
  classical
  intro X a l _
  exact List.formPerm_apply_getLast a l

theorem cycle_fixes_outside :
    Specs.D07.Ch02.PermutationConvention.CycleFixesOutside.{u} := by
  classical
  intro X l _ x hx
  exact List.formPerm_apply_of_notMem hx

theorem singleton_cycle :
    Specs.D07.Ch02.PermutationConvention.SingletonCycle.{u} := by
  classical
  intro X x
  exact List.formPerm_singleton x

theorem omit_one_cycles :
    Specs.D07.Ch02.PermutationConvention.OmitOneCycles.{u} := by
  intro X L
  induction L with
  | nil => rfl
  | cons l L ih =>
    by_cases hl : l.val.length = 1
    · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
      have hc : Specs.D07.Ch02.PermutationConvention.cycleConstructorValue X l.val l.property =
          1 := by
        classical
        simp [Specs.D07.Ch02.PermutationConvention.cycleConstructorValue, hx]
      simp [hl, hc, ih]
    · simp [hl, ih]

theorem fixed_points_count :
    Specs.D07.Ch02.PermutationConvention.FixedPointsCount.{u} := by
  classical
  intro X _ σ
  have hfixed : Finset.univ.filter (fun x : X => σ x = x) = σ.supportᶜ := by
    ext x
    simp
  rw [hfixed]
  exact (Finset.card_add_card_compl σ.support).symm

end D07.Ch02.PermutationConvention
