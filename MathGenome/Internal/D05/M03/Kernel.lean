import MathGenome.Internal.D05.M02.Subspace
import MathGenome.Internal.D05.M03.LinearMap
import MathGenome.Internal.Specs.D05.M03.Kernel

/-! K05.03.kernel: the zero fiber as a canonical subspace of the domain. -/

namespace D05.M03.Kernel

/-- The kernel is the canonical Mathlib submodule of the domain. -/
abbrev kernel (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) : Submodule K V :=
  LinearMap.ker T

theorem kernel_eq_set : Specs.D05.M03.Kernel.kernel_eq_set := by
  intro K V W _ _ _ _ _ T
  ext v
  exact LinearMap.mem_ker

theorem zero_mem_kernel : Specs.D05.M03.Kernel.zero_mem_kernel := by
  intro K V W _ _ _ _ _ T
  exact LinearMap.mem_ker.mpr (D05.M03.LinearMap.map_zero T)

theorem map_linear_combination : Specs.D05.M03.Kernel.map_linear_combination := by
  intro K V W _ _ _ _ _ T a b u v hu hv
  constructor
  · rw [T.map_add, T.map_smul, T.map_smul]
  · rw [LinearMap.mem_ker.mp hu, LinearMap.mem_ker.mp hv, smul_zero, smul_zero, zero_add]

theorem linear_combination_mem_kernel :
    Specs.D05.M03.Kernel.linear_combination_mem_kernel := by
  intro K V W _ _ _ _ _ T a b u v hu hv
  obtain ⟨hlinear, hzero⟩ := map_linear_combination T a b u v hu hv
  exact LinearMap.mem_ker.mpr (hlinear.trans hzero)

theorem kernel_is_subspace : Specs.D05.M03.Kernel.kernel_is_subspace := by
  intro K V W _ _ _ _ _ T
  apply (D05.M02.Subspace.subspace_iff_closed {v : V | T v = 0}).mpr
  refine ⟨D05.M03.LinearMap.map_zero T, ?_, ?_⟩
  · intro u v hu hv
    change T (u + v) = 0
    rw [T.map_add, hu, hv, zero_add]
  · intro a u hu
    change T (a • u) = 0
    rw [T.map_smul, hu, smul_zero]

end D05.M03.Kernel
