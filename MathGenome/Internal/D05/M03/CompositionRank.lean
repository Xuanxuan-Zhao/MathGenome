import MathGenome.Internal.Specs.D05.M03.CompositionRank
import MathGenome.Internal.D05.M03.Image
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M02.SubspaceDimension

/-! K05.03.composition_rank: finite-image rank bounds and equality cases. -/

namespace D05.M03.CompositionRank

theorem image_comp_eq_map : Specs.D05.M03.CompositionRank.image_comp_eq_map := by
  intro K U V W _ _ _ _ _ _ _ S T
  exact LinearMap.range_comp S T

theorem image_comp_le : Specs.D05.M03.CompositionRank.image_comp_le := by
  intro K U V W _ _ _ _ _ _ _ S T
  exact LinearMap.range_comp_le_range S T

theorem finite_image_comp_of_source :
    Specs.D05.M03.CompositionRank.finite_image_comp_of_source := by
  intro K U V W _ _ _ _ _ _ _ S T _
  rw [image_comp_eq_map S T]
  exact Module.Finite.map _ _

theorem finite_image_comp_of_target :
    Specs.D05.M03.CompositionRank.finite_image_comp_of_target := by
  intro K U V W _ _ _ _ _ _ _ S T _
  exact Submodule.finiteDimensional_of_le (image_comp_le S T)

theorem rank_comp_le_source : Specs.D05.M03.CompositionRank.rank_comp_le_source := by
  intro K U V W _ _ _ _ _ _ _ S T _
  rw [image_comp_eq_map S T]
  exact Submodule.finrank_map_le T S.range

theorem rank_comp_le_target : Specs.D05.M03.CompositionRank.rank_comp_le_target := by
  intro K U V W _ _ _ _ _ _ _ S T _
  exact Submodule.finrank_mono (image_comp_le S T)

theorem rank_comp_le : Specs.D05.M03.CompositionRank.rank_comp_le := by
  intro K U V W _ _ _ _ _ _ _ S T _ _
  exact le_min (rank_comp_le_source S T) (rank_comp_le_target S T)

theorem rank_comp_eq_of_injective :
    Specs.D05.M03.CompositionRank.rank_comp_eq_of_injective := by
  intro K U V W _ _ _ _ _ _ _ S T _ hT
  rw [image_comp_eq_map S T, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj (hT.comp Subtype.val_injective)

theorem rank_comp_eq_of_surjective :
    Specs.D05.M03.CompositionRank.rank_comp_eq_of_surjective := by
  intro K U V W _ _ _ _ _ _ _ S T _ hS
  rw [image_comp_eq_map S T, LinearMap.range_eq_top.mpr hS, Submodule.map_top]

theorem rank_comp_equiv_left : Specs.D05.M03.CompositionRank.rank_comp_equiv_left := by
  intro K U V W _ _ _ _ _ _ _ S e _
  exact rank_comp_eq_of_injective S e.toLinearMap e.injective

theorem rank_comp_equiv_right : Specs.D05.M03.CompositionRank.rank_comp_equiv_right := by
  intro K U V W _ _ _ _ _ _ _ e T _
  exact rank_comp_eq_of_surjective e.toLinearMap T e.surjective

end D05.M03.CompositionRank
