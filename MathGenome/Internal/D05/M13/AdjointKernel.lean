import MathGenome.Internal.Specs.D05.M13.AdjointKernel
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M12.OrthogonalDecomposition
import MathGenome.Internal.D05.M13.AdjointLaws

/-! K05.13.adjoint_kernel: kernels, images, orthogonal complements, and rank.
Mathlib's algebraic adjoint uses exactly the finite-dimensional hypotheses in
these Specs; its internal continuity/completeness bridges add no assumptions.
The orthogonality equalities are unaffected by swapping the inner-product slots.
-/

namespace D05.M13.AdjointKernel

theorem ker_adjoint : Specs.D05.M13.AdjointKernel.ker_adjoint := by
  intro F V W _ _ _ _ _ _ _ T
  exact (_root_.LinearMap.orthogonal_range T).symm

theorem range_adjoint : Specs.D05.M13.AdjointKernel.range_adjoint := by
  intro F V W _ _ _ _ _ _ _ T
  exact (_root_.LinearMap.orthogonal_ker T).symm

theorem rank_adjoint : Specs.D05.M13.AdjointKernel.rank_adjoint := by
  intro F V W _ _ _ _ _ _ _ T
  exact _root_.LinearMap.finrank_range_adjoint T

theorem ker_adjoint_comp_self : Specs.D05.M13.AdjointKernel.ker_adjoint_comp_self := by
  intro F V W _ _ _ _ _ _ _ T
  exact _root_.LinearMap.ker_adjoint_comp_self T

end D05.M13.AdjointKernel
