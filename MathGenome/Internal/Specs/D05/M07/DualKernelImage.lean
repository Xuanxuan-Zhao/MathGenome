import MathGenome.Internal.Specs.D05.M07.Annihilator
import MathGenome.Internal.Specs.D05.M07.DualMap

/-!
Independent statements for K05.07.dual_kernel_image (paper.tex:1042–1053).
The dual is the algebraic `Module.Dual`, and `dualMap` is precomposition over
the same field. Both equalities are in their stated ambient dual spaces.
Only the image equality assumes finite dimension, as in the manuscript.
-/

namespace Specs.D05.M07.DualKernelImage

/-- The kernel of pullback consists of functionals on W vanishing on im T. -/
def ker_dualMap_eq_annihilator_range : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    LinearMap.ker T.dualMap = (LinearMap.range T).dualAnnihilator

/-- In finite dimension, every functional on V vanishing on ker T is a pullback. -/
def range_dualMap_eq_annihilator_ker : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W),
    LinearMap.range T.dualMap = (LinearMap.ker T).dualAnnihilator

end Specs.D05.M07.DualKernelImage
