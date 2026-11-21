import MathGenome.Internal.Specs.D05.M08.EigenRoots
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M08.Minpoly
import MathGenome.Internal.D05.M09.Eigenspace
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! K05.08.eigen_roots: scalar roots and the nonzero kernel of `T - μ I`.
All statements include the zero-dimensional space and use the original field.
-/

noncomputable section

namespace D05.M08.EigenRoots

theorem kernel_iff_charpoly_root :
    Specs.D05.M08.EigenRoots.kernel_iff_charpoly_root := by
  intro K V _ _ _ _ T μ
  change LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ≠ ⊥ ↔
    T.charpoly.IsRoot μ
  rw [← D05.M09.Eigenspace.eigenspace_eq_kernel]
  exact Module.End.hasEigenvalue_iff_isRoot_charpoly T μ

theorem kernel_iff_minpoly_root :
    Specs.D05.M08.EigenRoots.kernel_iff_minpoly_root := by
  intro K V _ _ _ _ T μ
  change LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ≠ ⊥ ↔
    (minpoly K T).IsRoot μ
  rw [← D05.M09.Eigenspace.eigenspace_eq_kernel]
  exact Module.End.hasEigenvalue_iff_isRoot

theorem charpoly_root_iff_minpoly_root :
    Specs.D05.M08.EigenRoots.charpoly_root_iff_minpoly_root := by
  intro K V _ _ _ _ T μ
  exact (kernel_iff_charpoly_root T μ).symm.trans (kernel_iff_minpoly_root T μ)

theorem eigen_roots : Specs.D05.M08.EigenRoots.eigen_roots := by
  intro K V _ _ _ _ T μ
  exact ⟨kernel_iff_charpoly_root T μ, kernel_iff_minpoly_root T μ⟩

theorem zero_dimensional : Specs.D05.M08.EigenRoots.zero_dimensional := by
  intro K V _ _ _ _ T μ hdim
  have hc := Charpoly.zero_dimensional T hdim
  have hm := Minpoly.zero_dimension T hdim
  have hcr : (Specs.D05.M08.Charpoly.charpoly_value T).eval μ ≠ 0 := by
    rw [hc, Polynomial.eval_one]
    exact one_ne_zero
  refine ⟨hc, hm, ?_, hcr, ?_⟩
  · by_contra hker
    exact hcr ((kernel_iff_charpoly_root T μ).mp hker)
  · rw [hm, Polynomial.eval_one]
    exact one_ne_zero

end D05.M08.EigenRoots
