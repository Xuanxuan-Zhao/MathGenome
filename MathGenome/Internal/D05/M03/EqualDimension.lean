import MathGenome.Internal.Specs.D05.M03.EqualDimension
import MathGenome.Internal.D05.M03.Isomorphism
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M02.SubspaceDimension

/-! K05.03.equal_dimension: injectivity, surjectivity, and a linear inverse. -/

namespace D05.M03.EqualDimension

theorem equal_dimension : Specs.D05.M03.EqualDimension.equal_dimension := by
  intro K V W _ _ _ _ _ _ _ T hdim
  have h : Function.Injective T ↔ Function.Surjective T := by
    rw [D05.M03.InjectiveSurjective.injective_iff_kernel_eq_bot T,
      D05.M03.InjectiveSurjective.surjective_iff_image_eq_top T]
    have hrn := D05.M03.RankNullity.rank_nullity T
    have hrange :=
      (D05.M02.SubspaceDimension.subspace_dimension
        (LinearMap.range T) (Module.finrank K W) rfl).2.2.2
    constructor
    · intro hker
      rw [hker, finrank_bot, zero_add, hdim] at hrn
      exact hrange.mp hrn.symm
    · intro hr
      rw [hr, finrank_top, ← hdim] at hrn
      have hz : Module.finrank K (LinearMap.ker T) + Module.finrank K V =
          0 + Module.finrank K V := hrn.symm.trans (Nat.zero_add _).symm
      exact Submodule.finrank_eq_zero.mp (Nat.add_right_cancel hz)
  refine ⟨h, ?_, ?_⟩
  · constructor
    · intro hi
      exact (D05.M03.Isomorphism.isomorphism_iff_bijective T).mpr ⟨hi, h.mp hi⟩
    · intro he
      exact ((D05.M03.Isomorphism.isomorphism_iff_bijective T).mp he).1
  · constructor
    · intro hs
      exact D05.M03.Isomorphism.inverse_of_bijective T ⟨h.mpr hs, hs⟩
    · rintro ⟨S, ⟨_, hright⟩, _⟩ y
      refine ⟨S y, ?_⟩
      exact congrArg (fun f : W →ₗ[K] W => f y) hright

theorem zero_dimensional_unique :
    Specs.D05.M03.EqualDimension.zero_dimensional_unique := by
  intro K V W _ _ _ _ _ _ _ T hV hW
  have hzV := (D05.M02.Dimension.dimension_zero_iff_zero_space (K := K) (V := V)).mp hV
  have hzW := (D05.M02.Dimension.dimension_zero_iff_zero_space (K := K) (V := W)).mp hW
  constructor
  · intro S
    exact LinearMap.ext (fun x => (hzW (S x)).trans (hzW (T x)).symm)
  · have hi : Function.Injective T := fun x y _ => (hzV x).trans (hzV y).symm
    obtain ⟨e, he⟩ := (equal_dimension T (hV.trans hW.symm)).2.1.mp hi
    refine ⟨e, he, ?_⟩
    intro e' he'
    exact LinearEquiv.toLinearMap_injective (he'.trans he.symm)

end D05.M03.EqualDimension
