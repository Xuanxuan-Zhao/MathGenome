import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M03.Image
import MathGenome.Internal.Specs.D05.M03.InjectiveSurjective

/-! K05.03.injective_surjective: kernel and image criteria in arbitrary dimension. -/

namespace D05.M03.InjectiveSurjective

theorem injective_iff_kernel_eq_bot :
    Specs.D05.M03.InjectiveSurjective.injective_iff_kernel_eq_bot := by
  intro K V W _ _ _ _ _ T
  constructor
  · intro hinj
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    apply hinj
    exact (LinearMap.mem_ker.mp hx).trans (_root_.map_zero T).symm
  · intro hker u v huv
    have hmem : u - v ∈ LinearMap.ker T := by
      change T (u - v) = 0
      rw [_root_.map_sub, huv, sub_self]
    rw [hker] at hmem
    change u - v = 0 at hmem
    exact sub_eq_zero.mp hmem

theorem surjective_iff_image_eq_top :
    Specs.D05.M03.InjectiveSurjective.surjective_iff_image_eq_top := by
  intro K V W _ _ _ _ _ T
  constructor
  · intro hsurj
    apply top_unique
    intro y _
    exact (D05.M03.Image.mem_image T y).mpr (hsurj y)
  · intro himage y
    have hy : y ∈ LinearMap.range T := by
      rw [himage]
      exact Submodule.mem_top
    exact (D05.M03.Image.mem_image T y).mp hy

end D05.M03.InjectiveSurjective
