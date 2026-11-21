import MathGenome.Internal.Specs.D05.M12.BestApproximation.Conditional
import MathGenome.Internal.D05.M12.NormLaws
import MathGenome.Internal.D05.M12.OrthogonalComplement

/-! The conditional nearest-point criterion and uniqueness for arbitrary subspaces. -/

namespace D05.M12.BestApproximation.Conditional

theorem minimizes_iff_mem_orthogonal :
    Specs.D05.M12.BestApproximation.Conditional.minimizes_iff_mem_orthogonal := by
  intro F V _ _ _ U v u₀ hu₀
  have hbd : BddBelow (Set.range fun u : U => ‖v - u‖) :=
    ⟨0, by rintro _ ⟨u, rfl⟩; exact norm_nonneg _⟩
  have hmin : (∀ u ∈ U, ‖v - u₀‖ ≤ ‖v - u‖) ↔
      ‖v - u₀‖ = ⨅ u : U, ‖v - u‖ := by
    constructor
    · intro h
      exact le_antisymm (le_ciInf fun u => h u u.property)
        (ciInf_le hbd ⟨u₀, hu₀⟩)
    · intro h u hu
      rw [h]
      exact ciInf_le hbd ⟨u, hu⟩
  rw [hmin, U.norm_eq_iInf_iff_inner_eq_zero hu₀]
  constructor <;> intro h z hz
  · exact inner_eq_zero_symm.mp (h z hz)
  · exact inner_eq_zero_symm.mp (h z hz)

theorem minimizes_iff_firstInner_eq_zero :
    Specs.D05.M12.BestApproximation.Conditional.minimizes_iff_firstInner_eq_zero := by
  intro F V _ _ _ U v u₀ hu₀
  rw [minimizes_iff_mem_orthogonal U v u₀ hu₀,
    OrthogonalComplement.mem_orthogonalComplement (F := F)]

theorem squared_distance_decomposition :
    Specs.D05.M12.BestApproximation.Conditional.squared_distance_decomposition := by
  intro F V _ _ _ U v u₀ hu₀ hr u hu
  have hi : D05.firstInner (F := F) (v - u₀) (u₀ - u) = 0 :=
    hr (u₀ - u) (U.sub_mem hu₀ hu)
  have hp := NormLaws.firstInner_pythagoras (F := F) (v - u₀) (u₀ - u) hi
  simpa only [sub_add_sub_cancel] using hp

theorem minimizer_unique :
    Specs.D05.M12.BestApproximation.Conditional.minimizer_unique := by
  intro F V _ _ _ U v u₀ u₁ hu₀ hu₁ hm₀ hm₁
  have hr := (minimizes_iff_mem_orthogonal U v u₀ hu₀).mp hm₀
  have hp := squared_distance_decomposition U v u₀ hu₀ hr u₁ hu₁
  have heq : ‖v - u₀‖ = ‖v - u₁‖ := le_antisymm (hm₀ u₁ hu₁) (hm₁ u₀ hu₀)
  rw [heq] at hp
  have hz : ‖u₀ - u₁‖ = 0 := by nlinarith [sq_nonneg ‖u₀ - u₁‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem existsUnique_of_exists :
    Specs.D05.M12.BestApproximation.Conditional.existsUnique_of_exists := by
  intro F V _ _ _ U v hex
  obtain ⟨u₀, hu₀, hm₀⟩ := hex
  refine ⟨u₀, ⟨hu₀, hm₀⟩, ?_⟩
  rintro u₁ ⟨hu₁, hm₁⟩
  exact minimizer_unique U v u₁ u₀ hu₁ hu₀ hm₁ hm₀

theorem finite_dimensional_existsUnique :
    Specs.D05.M12.BestApproximation.Conditional.finite_dimensional_existsUnique := by
  intro F V _ _ _ U _ v
  apply existsUnique_of_exists U v
  obtain ⟨u₀, hu₀, hr⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal (K := U) v
  exact ⟨u₀, hu₀, (minimizes_iff_mem_orthogonal U v u₀ hu₀).mpr hr⟩

end D05.M12.BestApproximation.Conditional
