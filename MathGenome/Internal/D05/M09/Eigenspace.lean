import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M03.MapAlgebra
import MathGenome.Internal.Specs.D05.M09.Eigenspace

/-! K05.09.eigenspace: eigenvectors are nonzero, including at the boundary cases. -/

namespace D05.M09.Eigenspace

/-- The eigenspace is the canonical subspace over the given field. -/
abbrev eigenspace (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K) : Submodule K V := T.eigenspace μ

/-- Use the canonical predicate, which excludes the zero vector. -/
abbrev hasEigenvector (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K) (x : V) : Prop := T.HasEigenvector μ x

/-- Use eigenvalues over the same field as the vector-space structure. -/
abbrev hasEigenvalue (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K) : Prop := T.HasEigenvalue μ

theorem eigenspace_eq_kernel : Specs.D05.M09.Eigenspace.eigenspace_eq_kernel := by
  intro K V _ _ _ T μ
  exact Module.End.eigenspace_def

theorem mem_eigenspace_iff : Specs.D05.M09.Eigenspace.mem_eigenspace_iff := by
  intro K V _ _ _ T μ x
  exact Module.End.mem_eigenspace_iff

theorem eigenspace_is_subspace : Specs.D05.M09.Eigenspace.eigenspace_is_subspace := by
  intro K V _ _ _ T μ
  exact D05.M03.Kernel.kernel_is_subspace (T - μ • LinearMap.id)

theorem hasEigenvector_iff : Specs.D05.M09.Eigenspace.hasEigenvector_iff := by
  intro K V _ _ _ T μ x
  rw [Module.End.hasEigenvector_iff, eigenspace_eq_kernel]

theorem hasEigenvalue_iff : Specs.D05.M09.Eigenspace.hasEigenvalue_iff := by
  intro K V _ _ _ T μ
  rw [Module.End.hasEigenvalue_iff, eigenspace_eq_kernel, Submodule.ne_bot_iff]

theorem no_eigenvalues_on_zero_space :
    Specs.D05.M09.Eigenspace.no_eigenvalues_on_zero_space := by
  intro K V _ _ _ _ T μ h
  obtain ⟨x, _, hx⟩ := (hasEigenvalue_iff T μ).mp h
  exact hx (Subsingleton.elim x 0)

theorem identity_hasEigenvalue_iff : Specs.D05.M09.Eigenspace.identity_hasEigenvalue_iff := by
  intro K V _ _ _ _ μ
  constructor
  · intro h
    obtain ⟨x, hx, hne⟩ := (hasEigenvalue_iff LinearMap.id μ).mp h
    have heq : x = μ • x := by
      simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.smul_apply, sub_eq_zero] using hx
    have hzero : (μ - 1) • x = 0 := by
      rw [sub_smul, one_smul, ← heq, sub_self]
    have hμ : μ - 1 = 0 := (smul_eq_zero.mp hzero).resolve_right hne
    exact sub_eq_zero.mp hμ
  · rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    apply (hasEigenvalue_iff LinearMap.id 1).mpr
    exact ⟨x, by simp, hx⟩

end D05.M09.Eigenspace
