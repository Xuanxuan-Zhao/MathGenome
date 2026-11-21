import MathGenome.Internal.Specs.D07.Ch08.InjectiveKernel

/-! K07.08.injective_kernel: the zero-kernel test, using only additivity. -/

universe u v

namespace D07.Ch08.InjectiveKernel

theorem injective_iff_kernel_zero :
    Specs.D07.Ch08.InjectiveKernel.InjectiveIffKernelZero.{u, v} := by
  intro R S _ _ f
  constructor
  · intro hf
    apply Ideal.ext
    intro a
    rw [RingHom.mem_ker, Submodule.mem_bot]
    constructor
    · intro ha
      apply hf
      exact ha.trans (map_zero f).symm
    · rintro rfl
      exact map_zero f
  · intro hker a b hab
    have hmem : a - b ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, hab, sub_self]
    rw [hker, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem

end D07.Ch08.InjectiveKernel
