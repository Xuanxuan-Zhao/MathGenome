import MathGenome.Internal.Specs.D05.M10.Generalized
import MathGenome.Internal.D05.M09.Eigenspace
import MathGenome.Internal.D05.M10.KernelStabilization
import MathGenome.Internal.D05.M10.Nilpotent
import MathGenome.Internal.D05.M06.Invariant

/-! K05.10.generalized: the stabilized kernel and the nilpotent restriction. -/

noncomputable section

namespace D05.M10.Generalized

abbrev generalizedEigenspace := Specs.D05.M10.Generalized.generalizedEigenspace_value

abbrev isGeneralizedEigenvector := Specs.D05.M10.Generalized.isGeneralizedEigenvector_value

theorem eq_kernel : Specs.D05.M10.Generalized.eq_kernel := by
  intro K V _ _ _ _ T μ n hn
  subst n
  exact Module.End.genEigenspace_nat

theorem mem_iff : Specs.D05.M10.Generalized.mem_iff := by
  intro K V _ _ _ _ T μ x
  exact Module.End.mem_genEigenspace_nat

theorem stabilization : Specs.D05.M10.Generalized.stabilization := by
  intro K V _ _ _ _ T μ n m hn hm
  rw [eq_kernel T μ n hn]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact (KernelStabilization.kernel_stabilization (T - μ • 1) n hn j).symm

theorem eq_union : Specs.D05.M10.Generalized.eq_union := by
  intro K V _ _ _ _ T μ
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro hx
    exact ⟨Module.finrank K V, (mem_iff T μ x).mp hx⟩
  · rintro ⟨r, hr⟩
    apply (mem_iff T μ x).mpr
    exact Module.End.ker_pow_le_ker_pow_finrank (T - μ • 1) r hr

theorem eigenvector_iff_mem : Specs.D05.M10.Generalized.eigenvector_iff_mem := by
  intro K V _ _ _ _ T μ x
  constructor
  · rintro ⟨hx, r, _, hr⟩
    refine ⟨hx, (mem_iff T μ x).mpr ?_⟩
    exact Module.End.ker_pow_le_ker_pow_finrank (T - μ • 1) r hr
  · rintro ⟨hx, hmem⟩
    refine ⟨hx, Module.finrank K V + 1, Nat.succ_pos _, ?_⟩
    exact KernelStabilization.kernel_inclusion (T - μ • 1) _
      ((mem_iff T μ x).mp hmem)

theorem commutes_shift : Specs.D05.M10.Generalized.commutes_shift := by
  intro K V _ _ _ T μ
  exact Algebra.mul_sub_algebraMap_commutes T μ

theorem invariant : Specs.D05.M10.Generalized.invariant := by
  intro K V _ _ _ _ T μ
  exact Module.End.mapsTo_genEigenspace_of_comm (Commute.refl T) μ _

theorem shift_invariant : Specs.D05.M10.Generalized.shift_invariant := by
  intro K V _ _ _ _ T μ
  exact Module.End.mapsTo_genEigenspace_of_comm (commutes_shift T μ) μ _

theorem restriction_decomposition : Specs.D05.M10.Generalized.restriction_decomposition := by
  intro K V _ _ _ _ T μ hT hN
  ext x
  change T (x : V) = μ • (x : V) + (T (x : V) - μ • (x : V))
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem restriction_pow_dimension : Specs.D05.M10.Generalized.restriction_pow_dimension := by
  intro K V _ _ _ _ T μ hN
  change ∀ x ∈ T.genEigenspace μ (Module.finrank K V),
    (T - μ • (1 : Module.End K V)) x ∈ T.genEigenspace μ (Module.finrank K V) at hN
  change ((T - μ • (1 : Module.End K V)).restrict
    (p := T.genEigenspace μ (Module.finrank K V))
    (q := T.genEigenspace μ (Module.finrank K V)) hN) ^ Module.finrank K V = 0
  rw [Module.End.pow_restrict]
  ext x
  exact (mem_iff T μ (x : V)).mp x.property

theorem restriction_nilpotent : Specs.D05.M10.Generalized.restriction_nilpotent := by
  intro K V _ _ _ _ T μ hN
  exact ⟨Module.finrank K V, restriction_pow_dimension T μ hN⟩

theorem restriction_structure : Specs.D05.M10.Generalized.restriction_structure := by
  intro K V _ _ _ _ T μ
  refine ⟨invariant T μ, shift_invariant T μ,
    restriction_decomposition T μ (invariant T μ) (shift_invariant T μ), ?_⟩
  exact (Nilpotent.nilpotent_iff_positive_power _).mp
    (restriction_nilpotent T μ (shift_invariant T μ))

end D05.M10.Generalized
