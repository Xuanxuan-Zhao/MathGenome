import MathGenome.Internal.Specs.D05.M05.Orientation
import MathGenome.Internal.D05.M04.ChangeBasis
import MathGenome.Internal.D05.M05.DetProduct
import MathGenome.Internal.D05.M05.DetInvertible
import MathGenome.Internal.D05.M02.Basis
import Mathlib.Tactic.Linarith

/-! K05.05.orientation: the quotient of ordered real bases, including dimension zero. -/

noncomputable section

namespace D05.M05.Orientation

open Specs.D05.M04.ChangeBasis
open Specs.D05.M05.Orientation

abbrev sameOrientation : sameOrientation_type := sameOrientation_value
abbrev classes : classes_type := classes_value

theorem conversion_det_basis : Specs.D05.M05.Orientation.conversion_det_basis := by
  intro V _ _ n b c
  rw [DetDefinition.matrix_det_bridge]
  change (LinearMap.toMatrix c b LinearMap.id).det = b.det c
  rw [LinearMap.toMatrix_id_eq_basis_toMatrix]
  rfl

theorem conversion_det_self : Specs.D05.M05.Orientation.conversion_det_self := by
  intro V _ _ n b
  rw [conversion_det_basis, b.det_self]

theorem conversion_det_ne_zero : Specs.D05.M05.Orientation.conversion_det_ne_zero := by
  intro V _ _ n b c
  rw [conversion_det_basis]
  exact (b.isUnit_det c).ne_zero

theorem conversion_det_comp : Specs.D05.M05.Orientation.conversion_det_comp := by
  intro V _ _ n b c d
  rw [conversion_det_basis b c, conversion_det_basis c d, conversion_det_basis b d]
  exact b.det_mul_det c d

theorem conversion_det_inverse : Specs.D05.M05.Orientation.conversion_det_inverse := by
  intro V _ _ n b c
  have h := conversion_det_comp b c b
  rw [conversion_det_self] at h
  exact eq_inv_of_mul_eq_one_right h

theorem sameOrientation_equivalence : Specs.D05.M05.Orientation.sameOrientation_equivalence := by
  intro V _ _ n
  refine ⟨?_, ?_, ?_⟩
  · intro b
    change 0 < determinant (changeMatrix_value b b)
    rw [conversion_det_self]
    exact zero_lt_one
  · intro b c h
    change 0 < determinant (changeMatrix_value c b)
    rw [conversion_det_inverse]
    exact inv_pos.mpr h
  · intro b c d hbc hcd
    change 0 < determinant (changeMatrix_value b d)
    rw [← conversion_det_comp b c d]
    exact mul_pos hbc hcd

theorem class_eq_iff : Specs.D05.M05.Orientation.class_eq_iff := by
  intro V _ _ n b c
  exact (sameOrientation_equivalence n).quot_mk_eq_iff b c

theorem sign_dichotomy : Specs.D05.M05.Orientation.sign_dichotomy := by
  intro V _ _ n b c
  exact (conversion_det_ne_zero b c).lt_or_gt.symm

theorem different_iff_det_neg : Specs.D05.M05.Orientation.different_iff_det_neg := by
  intro V _ _ n b c
  rw [ne_eq, class_eq_iff]
  change ¬ 0 < determinant (changeMatrix_value b c) ↔ _
  exact ⟨fun h => (sign_dichotomy b c).resolve_left h, fun h => not_lt.mpr h.le⟩

theorem negate_one_apply : Specs.D05.M05.Orientation.negate_one_apply := by
  intro V _ _ n b i j
  by_cases h : j = i <;> simp [Module.Basis.unitsSMul_apply, h,
    Units.smul_def]

theorem negate_one_det : Specs.D05.M05.Orientation.negate_one_det := by
  intro V _ _ n b i
  rw [conversion_det_basis, Module.Basis.det_unitsSMul_self]
  have h : (fun j : Fin n => ((Function.update (1 : Fin n → ℝˣ) i (-1)) j : ℝ)) =
      Function.update (1 : Fin n → ℝ) i (-1) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem swap_det : Specs.D05.M05.Orientation.swap_det := by
  intro V _ _ n b i j hij
  rw [conversion_det_basis]
  have h : (b.reindex (Equiv.swap i j) : Fin n → V) = b ∘ Equiv.swap i j := by
    ext k
    simp [Module.Basis.reindex_apply]
  rw [h, b.det.map_perm]
  simp [Equiv.Perm.sign_swap hij, b.det_self]

theorem two_classes_representatives :
    Specs.D05.M05.Orientation.two_classes_representatives := by
  intro V _ _ n b i
  let c := b.unitsSMul (Function.update 1 i (-1))
  have hc : determinant (changeMatrix_value b c) = -1 := negate_one_det b i
  constructor
  · rw [different_iff_det_neg, hc]
    exact neg_one_lt_zero
  · intro o
    induction o using Quot.ind with
    | mk d =>
      rcases sign_dichotomy b d with h | h
      · exact Or.inl ((class_eq_iff b d).mpr h).symm
      · right
        apply ((class_eq_iff c d).mpr ?_).symm
        have hm := conversion_det_comp b c d
        rw [hc] at hm
        change 0 < determinant (changeMatrix_value c d)
        linarith

theorem exactly_two_classes : Specs.D05.M05.Orientation.exactly_two_classes := by
  intro V _ _ n b hn
  obtain ⟨hne, hall⟩ := two_classes_representatives b ⟨0, hn⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨_, _, hne, ?_⟩
  ext o
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact hall o

theorem zero_unique_basis : Specs.D05.M05.Orientation.zero_unique_basis := by
  intro V _ _ b c
  ext i
  exact Fin.elim0 i

theorem zero_one_class : Specs.D05.M05.Orientation.zero_one_class := by
  intro V _ _ b
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨classOf_value b, ?_⟩
  intro o
  induction o using Quot.ind with
  | mk c =>
    rw [zero_unique_basis c b]
    rfl

theorem dimension_class_count : Specs.D05.M05.Orientation.dimension_class_count := by
  intro V _ _ _
  by_cases h : Module.finrank ℝ V = 0
  · rw [ite_eq_left h]
    have b := Module.finBasis ℝ V
    rw [h] at b ⊢
    exact zero_one_class b
  · rw [ite_eq_right h]
    exact exactly_two_classes (Module.finBasis ℝ V) (Nat.pos_of_ne_zero h)

theorem conversion_map_det : Specs.D05.M05.Orientation.conversion_map_det := by
  intro V _ _ n b T
  rw [conversion_det_basis]
  change b.det (T.toLinearMap ∘ b) = _
  rw [b.det_comp, b.det_self, mul_one]

theorem preserves_iff_det_pos : Specs.D05.M05.Orientation.preserves_iff_det_pos := by
  intro V _ _ n b T
  rw [eq_comm, class_eq_iff]
  change 0 < determinant (changeMatrix_value b (b.map T)) ↔ _
  rw [conversion_map_det]

theorem reverses_iff_det_neg : Specs.D05.M05.Orientation.reverses_iff_det_neg := by
  intro V _ _ n b T
  rw [ne_comm, different_iff_det_neg, conversion_map_det]

theorem preserves_all_iff_det_pos : Specs.D05.M05.Orientation.preserves_all_iff_det_pos := by
  intro V _ _ n b T
  exact ⟨fun h => (preserves_iff_det_pos b T).mp (h b),
    fun h c => (preserves_iff_det_pos c T).mpr h⟩

theorem reverses_all_iff_det_neg : Specs.D05.M05.Orientation.reverses_all_iff_det_neg := by
  intro V _ _ n b T
  exact ⟨fun h => (reverses_iff_det_neg b T).mp (h b),
    fun h c => (reverses_iff_det_neg c T).mpr h⟩

end D05.M05.Orientation
