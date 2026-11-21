import MathGenome.Internal.Specs.D05.M13.SpectralProjections
import MathGenome.Internal.D05.M12.Projection
import MathGenome.Internal.D05.M13.AlgebraicProjections
import MathGenome.Internal.D05.M13.ComplexSpectral
import MathGenome.Internal.D05.M13.RealSpectral

/-! Orthogonal spectral projections, including the interpolation bridge.
The only spectral inputs are the upstream real and complex spectral theorems.
Equality of operators is checked on the eigenspaces they prove span V. -/
noncomputable section
namespace D05.M13.SpectralProjections
open scoped BigOperators

section General
variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

/-- Orthogonal projections have the same Kronecker-delta action on the
individual eigenspaces as the Lagrange polynomials. -/
theorem projection_action (T : Module.End F V) (hT : D05.normalOperator T)
    {r : ℕ} (a : Fin r → F) (ha : Function.Injective a)
    (i j : Fin r) (v : V) (hv : v ∈ T.eigenspace (a j)) :
    D05.orthogonalProjection (T.eigenspace (a i)) v = if i = j then v else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simpa using D05.M12.Projection.fixes_subspace (T.eigenspace (a i)) v hv
  · rw [ite_eq_right hij]
    have ho : v ∈ (T.eigenspace (a i)).orthogonal :=
      D05.M13.NormalBasic.eigenspaces_orthogonal T hT (a j) (a i)
        (fun h => hij (ha h).symm) hv
    exact (D05.M12.Projection.kernel_eq (T.eigenspace (a i)) ▸ ho :
      v ∈ (D05.orthogonalProjection (T.eigenspace (a i))).ker)

/-- This bridge is proved from normality and an eigenbasis, rather than
assuming an orthogonal decomposition or an interpolation certificate. -/
theorem projection_eq_interpolation (T : Module.End F V)
    (hT : D05.normalOperator T)
    (hd : Specs.D05.M09.Diagonalizable.diagonalizable_value F V T)
    {r : ℕ} (a : Fin r → F) (ha : Function.Injective a)
    (hfull : ∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) (i : Fin r) :
    D05.orthogonalProjection (T.eigenspace (a i)) =
      D05.M13.AlgebraicProjections.projection F V T r a i := by
  apply D05.M13.AlgebraicProjections.ext_on_eigenspaces hd hfull
  intro j v hv
  rw [projection_action T hT a ha i j v hv,
    D05.M13.AlgebraicProjections.action_on_eigenspace T a ha i j v hv]

/-- Assemble both sums from their actions on the spanning eigenspaces. -/
theorem resolution_of_normal_diagonalizable (T : Module.End F V)
    (hT : D05.normalOperator T)
    (hd : Specs.D05.M09.Diagonalizable.diagonalizable_value F V T)
    {r : ℕ} (a : Fin r → F) (ha : Function.Injective a)
    (hfull : ∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) :
    Specs.D05.M13.SpectralProjections.Resolution T a := by
  classical
  refine ⟨?_, ?_, projection_eq_interpolation T hT hd a ha hfull⟩
  · simp_rw [projection_eq_interpolation T hT hd a ha hfull]
    exact D05.M13.AlgebraicProjections.sum_projections T a ha hd hfull
  · apply D05.M13.AlgebraicProjections.ext_on_eigenspaces hd hfull
    intro j v hv
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      projection_action T hT a ha _ j v hv]
    simpa using (Module.End.mem_eigenspace_iff.mp hv).symm

end General

theorem projection_properties : Specs.D05.M13.SpectralProjections.projection_properties := by
  intro F V _ _ _ _ T μ
  refine ⟨D05.M12.Projection.range_eq _, D05.M12.Projection.kernel_eq _, ?_, ?_⟩
  · simpa only [pow_two, Module.End.mul_eq_comp] using D05.M12.Projection.idempotent (T.eigenspace μ)
  · exact D05.M13.Adjoint.adjoint_unique _ _
      (D05.M12.Projection.self_adjoint_identity (T.eigenspace μ))

theorem distinct_projections_mul : Specs.D05.M13.SpectralProjections.distinct_projections_mul := by
  intro F V _ _ _ _ T hT μ ν hμν
  ext v
  change D05.orthogonalProjection (T.eigenspace μ)
    (D05.orthogonalProjection (T.eigenspace ν) v) = 0
  have hr : D05.orthogonalProjection (T.eigenspace ν) v ∈ T.eigenspace ν := by
    exact ((D05.M12.Projection.component_characterization
      (T.eigenspace ν) v _).mp rfl).1
  have ho := D05.M13.NormalBasic.eigenspaces_orthogonal T hT ν μ (Ne.symm hμν) hr
  exact (D05.M12.Projection.kernel_eq (T.eigenspace μ) ▸ ho :
    D05.orthogonalProjection (T.eigenspace ν) v ∈
      (D05.orthogonalProjection (T.eigenspace μ)).ker)

theorem finite_spectrum : Specs.D05.M13.SpectralProjections.finite_spectrum := by
  intro F V _ _ _ _ T
  classical
  let e := (Fintype.equivFin T.Eigenvalues).symm
  refine ⟨Fintype.card T.Eigenvalues, fun i => (e i : F),
    Subtype.val_injective.comp e.injective, ?_⟩
  intro μ
  constructor
  · intro hμ
    exact ⟨e.symm ⟨μ, hμ⟩, congrArg (fun z : T.Eigenvalues => (z : F))
      (e.apply_symm_apply ⟨μ, hμ⟩)⟩
  · rintro ⟨i, rfl⟩
    exact (e i).property

theorem real_resolution : Specs.D05.M13.SpectralProjections.real_resolution := by
  intro V _ _ _ T hT r a ha hfull
  obtain ⟨b, _, μ, hb⟩ := D05.M13.RealSpectral.exists_orthonormal_eigenbasis T hT
  exact resolution_of_normal_diagonalizable T
    (D05.M13.SelfAdjoint.selfAdjoint_implies_normal T hT)
    ⟨Module.finrank ℝ V, b, μ, hb⟩ a ha hfull

theorem complex_resolution : Specs.D05.M13.SpectralProjections.complex_resolution := by
  intro V _ _ _ T hT r a ha hfull
  obtain ⟨b, _, μ, hb⟩ := D05.M13.ComplexSpectral.normal_has_orthonormal_eigenbasis T hT
  exact resolution_of_normal_diagonalizable T hT
    ⟨Module.finrank ℂ V, b, μ, hb⟩ a ha hfull

theorem real_exists_resolution : Specs.D05.M13.SpectralProjections.real_exists_resolution := by
  intro V _ _ _ T hT
  obtain ⟨r, a, ha, hfull⟩ := finite_spectrum T
  exact ⟨r, a, ha, hfull, real_resolution T hT a ha hfull⟩

theorem complex_exists_resolution : Specs.D05.M13.SpectralProjections.complex_exists_resolution := by
  intro V _ _ _ T hT
  obtain ⟨r, a, ha, hfull⟩ := finite_spectrum T
  exact ⟨r, a, ha, hfull, complex_resolution T hT a ha hfull⟩

theorem zero_space : Specs.D05.M13.SpectralProjections.zero_space := by
  intro F V _ _ _ _ _ T a
  refine ⟨fun μ => D05.M09.Eigenspace.no_eigenvalues_on_zero_space T μ, ?_, ?_, ?_⟩
  · ext v
    exact Subsingleton.elim _ _
  · ext v
    exact Subsingleton.elim _ _
  · intro i
    exact Fin.elim0 i

end D05.M13.SpectralProjections
