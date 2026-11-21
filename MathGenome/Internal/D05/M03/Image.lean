import MathGenome.Internal.Specs.D05.M03.Image
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.M03.LinearMap

/-! K05.03.image: the image subspace, its generators, and finite-image rank. -/

namespace D05.M03.Image

/-- The canonical image subspace, over the same field as the original map. -/
abbrev image (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) : Submodule K W :=
  LinearMap.range T

theorem mem_image : Specs.D05.M03.Image.mem_image := by
  intro K V W _ _ _ _ _ T y
  exact LinearMap.mem_range

theorem zero_mem_image : Specs.D05.M03.Image.zero_mem_image := by
  intro K V W _ _ _ _ _ T
  exact ⟨0, _root_.map_zero T⟩

theorem map_linear_combination : Specs.D05.M03.Image.map_linear_combination := by
  intro K V W _ _ _ _ _ T a b x z
  rw [T.map_add, T.map_smul, T.map_smul]

theorem image_closed_combination : Specs.D05.M03.Image.image_closed_combination := by
  intro K V W _ _ _ _ _ T a b y z hy hz
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨w, rfl⟩ := hz
  exact ⟨a • x + b • w, (map_linear_combination T a b x w).symm⟩

theorem image_subspace : Specs.D05.M03.Image.image_subspace := by
  intro K V W _ _ _ _ _ T
  exact ⟨T.range, rfl⟩

theorem span_image_eq : Specs.D05.M03.Image.span_image_eq := by
  intro K V W I _ _ _ _ _ T v hv
  have h := Submodule.map_span T (Set.range v)
  rw [hv, Submodule.map_top] at h
  simpa only [← Set.range_comp, Function.comp_def] using h.symm

theorem span_image_subtype_eq : Specs.D05.M03.Image.span_image_subtype_eq := by
  intro K V W I _ _ _ _ _ T v hv
  exact (Submodule.span_range_subtype_eq_top_iff T.range
    (fun i => LinearMap.mem_range_self T (v i))).mpr (span_image_eq T v hv)

/-- The paper defines natural-number rank when the image is finite-dimensional. -/
noncomputable abbrev rank (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range T)] : ℕ :=
  D05.M02.Dimension.dimension K (LinearMap.range T)

theorem rank_eq_card_image_basis : Specs.D05.M03.Image.rank_eq_card_image_basis := by
  intro K V W I _ _ _ _ _ T _ _ b
  exact D05.M02.Dimension.dimension_eq_card_basis b

end D05.M03.Image
