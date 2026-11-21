import MathGenome.Internal.Specs.D05.M13.ComplexSpectral
import MathGenome.Internal.D05.M09.Existence
import MathGenome.Internal.D05.M13.NormalBasic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! The complex spectral theorem. We prove completeness of the mutually
orthogonal eigenspaces: their common orthogonal complement is invariant and
has no eigenvalue, so complex eigenvalue existence forces it to be zero.
Combining orthonormal bases of those eigenspaces gives the required basis.
This argument also applies when the ambient space is zero. -/

noncomputable section

namespace D05.M13.ComplexSpectral

open Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The orthogonal complement of any eigenspace is invariant for a normal map. -/
theorem invariant_orthogonal_eigenspace (T : Module.End ℂ V)
    (hT : D05.normalOperator T) (μ : ℂ) (x : V)
    (hx : x ∈ (T.eigenspace μ).orthogonal) :
    T x ∈ (T.eigenspace μ).orthogonal := by
  intro w hw
  have hw' := (D05.M13.NormalBasic.eigenvector_equation_iff T hT μ w).mp
    (mem_eigenspace_iff.mp hw)
  rw [← LinearMap.adjoint_inner_left, hw', inner_smul_left, hx w hw, mul_zero]

/-- No part of the space remains orthogonal to every eigenspace. -/
theorem orthogonal_iSup_eigenspaces_eq_bot (T : Module.End ℂ V)
    (hT : D05.normalOperator T) :
    (⨆ μ : ℂ, T.eigenspace μ).orthogonal = ⊥ := by
  let P := (⨆ μ : ℂ, T.eigenspace μ).orthogonal
  have hP : ∀ x ∈ P, T x ∈ P := by
    intro x hx
    dsimp only [P] at hx ⊢
    rw [← Submodule.iInf_orthogonal] at hx ⊢
    exact T.iInf_invariant (invariant_orthogonal_eigenspace T hT) x hx
  have hno : ∀ μ : ℂ, eigenspace (T.restrict hP) μ = ⊥ := by
    intro μ
    apply eigenspace_restrict_eq_bot hP
    exact ((Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ μ)).disjoint
  have hsub : Subsingleton P := by
    by_contra hn
    have : Nontrivial P := not_subsingleton_iff_nontrivial.mp hn
    obtain ⟨μ, hμ⟩ := D05.M09.Existence.complex_exists (T.restrict hP)
    exact hμ (hno μ)
  exact Submodule.eq_bot_of_subsingleton

/-- Bundled orthonormal eigenbasis, with its actual complex eigenvalues. -/
theorem exists_orthonormalBasis (T : Module.End ℂ V) (hT : D05.normalOperator T) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∃ μ : Fin (Module.finrank ℂ V) → ℂ, ∀ i, T (b i) = μ i • b i := by
  classical
  have ho : OrthogonalFamily ℂ (fun μ : T.Eigenvalues => T.eigenspace μ)
      (fun μ => (T.eigenspace μ).subtypeₗᵢ) := by
    intro μ ν hμν x y
    exact D05.M13.NormalBasic.eigenvectors_orthogonal T hT
      (ν : ℂ) (μ : ℂ) (fun h => hμν (Subtype.ext h.symm)) y x
      (mem_eigenspace_iff.mp y.property) (mem_eigenspace_iff.mp x.property)
  have hz : (⨆ μ : T.Eigenvalues, T.eigenspace μ).orthogonal = ⊥ := by
    change (⨆ μ : { μ // T.eigenspace μ ≠ ⊥ }, T.eigenspace μ).orthogonal = ⊥
    rw [iSup_ne_bot_subtype, orthogonal_iSup_eigenspaces_eq_bot T hT]
  have hi := ho.isInternal_iff.mpr hz
  refine ⟨hi.subordinateOrthonormalBasis rfl ho,
    fun i => ((hi.subordinateOrthonormalBasisIndex rfl i ho : T.Eigenvalues) : ℂ), ?_⟩
  intro i
  exact mem_eigenspace_iff.mp (hi.subordinateOrthonormalBasis_subordinate rfl i ho)

theorem normal_has_orthonormal_eigenbasis :
    Specs.D05.M13.ComplexSpectral.normal_has_orthonormal_eigenbasis := by
  intro V _ _ _ T hT
  obtain ⟨b, μ, hb⟩ := exists_orthonormalBasis T hT
  exact ⟨b.toBasis,
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal, μ, hb⟩

theorem orthonormal_eigenbasis_normal :
    Specs.D05.M13.ComplexSpectral.orthonormal_eigenbasis_normal := by
  intro V _ _ _ T b hb ⟨μ, hμ⟩
  classical
  have ho := (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mp hb
  have ha : ∀ i, LinearMap.adjoint T (b i) = starRingEnd ℂ (μ i) • b i := by
    intro i
    apply InnerProductSpace.ext_inner_left_basis b
    intro j
    rw [LinearMap.adjoint_inner_right, hμ j, inner_smul_left, inner_smul_right]
    by_cases h : i = j
    · subst j
      rfl
    · rw [ho.inner_eq_zero (Ne.symm h)]
      simp
  unfold D05.normalOperator
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, ha, hμ, map_smul, smul_smul]
  rw [mul_comm]

theorem complex_spectral : Specs.D05.M13.ComplexSpectral.complex_spectral := by
  intro V _ _ _ T
  constructor
  · rintro ⟨b, hb, hμ⟩
    exact orthonormal_eigenbasis_normal T b hb hμ
  · exact normal_has_orthonormal_eigenbasis T

end D05.M13.ComplexSpectral
