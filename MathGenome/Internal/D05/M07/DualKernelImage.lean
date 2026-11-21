import MathGenome.Internal.D05.M07.Annihilator
import MathGenome.Internal.D05.M07.DualMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import MathGenome.Internal.Specs.D05.M07.DualKernelImage

/-! K05.07.dual_kernel_image: kernel and image of algebraic pullback. -/

namespace D05.M07.DualKernelImage

/-- This is the pointwise vanishing identity, with no dimension assumption. -/
theorem ker_dualMap_eq_annihilator_range :
    Specs.D05.M07.DualKernelImage.ker_dualMap_eq_annihilator_range := by
  intro K V W _ _ _ _ _ T
  exact T.ker_dualMap_eq_dualAnnihilator_range

/-- Mathlib proves the reverse inclusion by factoring through the image and
extending a functional to W. Its extension uses a linear left inverse of the
image inclusion, constructed by extending a basis; no dimension count is used.
The library result holds even for arbitrary vector spaces with classical choice.
Here the hypotheses retain the finite-dimensional statement of the paper. -/
theorem range_dualMap_eq_annihilator_ker :
    Specs.D05.M07.DualKernelImage.range_dualMap_eq_annihilator_ker := by
  intro K V W _ _ _ _ _ _ _ T
  exact T.range_dualMap_eq_dualAnnihilator_ker

end D05.M07.DualKernelImage
