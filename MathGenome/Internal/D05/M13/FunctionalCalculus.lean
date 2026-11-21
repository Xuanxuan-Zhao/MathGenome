import MathGenome.Internal.Specs.D05.M13.FunctionalCalculus
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M13.AlgebraicProjections
import MathGenome.Internal.D05.M13.SpectralProjections

/-! Finite spectral functional calculus. Equality of operators is proved on
spanning eigenspaces; the input functions are defined on the finite scalar set,
not on a chosen eigenbasis or on the whole field. -/
noncomputable section
namespace D05.M13.FunctionalCalculus
open scoped BigOperators

abbrev functionalCalculus : Specs.D05.M13.FunctionalCalculus.functionalCalculus_type :=
  Specs.D05.M13.FunctionalCalculus.functionalCalculus_value

theorem finite_spectrum : Specs.D05.M13.FunctionalCalculus.finite_spectrum := by
  intro K V _ _ _ _ T
  classical
  let e := (Fintype.equivFin T.Eigenvalues).symm
  refine ⟨Fintype.card T.Eigenvalues, fun i => (e i : K),
    Subtype.val_injective.comp e.injective, ?_⟩
  intro μ
  constructor
  · intro hμ
    exact ⟨e.symm ⟨μ, hμ⟩, congrArg (fun z : T.Eigenvalues => (z : K))
      (e.apply_symm_apply ⟨μ, hμ⟩)⟩
  · rintro ⟨i, rfl⟩
    exact (e i).property

theorem action_on_eigenspace : Specs.D05.M13.FunctionalCalculus.action_on_eigenspace := by
  intro K V _ _ _ T r a ha f j v hv
  classical
  change (∑ i, f ⟨a i, ⟨i, rfl⟩⟩ •
    D05.M13.AlgebraicProjections.projection K V T r a i) v = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    D05.M13.AlgebraicProjections.action_on_eigenspace T a ha _ j v hv]
  simp

theorem map_zero : Specs.D05.M13.FunctionalCalculus.map_zero := by
  intro K V _ _ _ T r a
  simp [Specs.D05.M13.FunctionalCalculus.functionalCalculus_value]

theorem map_add : Specs.D05.M13.FunctionalCalculus.map_add := by
  intro K V _ _ _ T r a f g
  simp [Specs.D05.M13.FunctionalCalculus.functionalCalculus_value,
    add_smul, Finset.sum_add_distrib]

theorem map_smul : Specs.D05.M13.FunctionalCalculus.map_smul := by
  intro K V _ _ _ T r a s f
  simp [Specs.D05.M13.FunctionalCalculus.functionalCalculus_value,
    Finset.smul_sum, smul_smul]

theorem map_one : Specs.D05.M13.FunctionalCalculus.map_one := by
  intro K V _ _ _ _ T r a ha hd hfull
  simpa [functionalCalculus, Specs.D05.M13.FunctionalCalculus.functionalCalculus_value] using
    D05.M13.AlgebraicProjections.sum_projections T a ha hd hfull

theorem map_mul : Specs.D05.M13.FunctionalCalculus.map_mul := by
  intro K V _ _ _ _ T r a ha hd hfull f g
  apply D05.M13.AlgebraicProjections.ext_on_eigenspaces hd hfull
  intro j v hv
  simp [Module.End.mul_apply, _root_.map_smul,
    action_on_eigenspace T a ha _ j v hv, smul_smul, mul_comm]

theorem map_constant : Specs.D05.M13.FunctionalCalculus.map_constant := by
  intro K V _ _ _ _ T r a ha hd hfull s
  have hc : (fun _ : Set.range a => s) = s • (1 : Set.range a → K) := by
    ext μ
    simp
  rw [hc, map_smul T a s 1, map_one T a ha hd hfull]

theorem polynomial_agreement : Specs.D05.M13.FunctionalCalculus.polynomial_agreement := by
  intro K V _ _ _ _ T r a ha hd hfull p
  apply D05.M13.AlgebraicProjections.ext_on_eigenspaces hd hfull
  intro j v hv
  rw [action_on_eigenspace T a ha _ j v hv]
  exact (Module.End.aeval_apply_of_mem_apply_eq_smul
    (Module.End.mem_eigenspace_iff.mp hv)).symm

theorem interpolation_formula : Specs.D05.M13.FunctionalCalculus.interpolation_formula := by
  intro K V _ _ _ T r a f
  change _ = Polynomial.aeval T _
  rw [_root_.map_sum]
  simp only [_root_.map_smul,
    Specs.D05.M13.FunctionalCalculus.functionalCalculus_value,
    Specs.D05.M13.AlgebraicProjections.projection_value,
    Specs.D05.M08.Evaluation.evaluation_value]

theorem depends_only_spectrum : Specs.D05.M13.FunctionalCalculus.depends_only_spectrum := by
  intro K V _ _ _ _ T r a hfull f g hfg
  unfold Specs.D05.M13.FunctionalCalculus.functionalCalculus_value
  apply Finset.sum_congr rfl
  intro i _
  change f (a i) • _ = g (a i) • _
  exact congrArg (fun z : K => z •
    D05.M13.AlgebraicProjections.projection K V T r a i)
    (hfg (a i) ((hfull (a i)).mpr ⟨i, rfl⟩))

theorem enumeration_independent : Specs.D05.M13.FunctionalCalculus.enumeration_independent := by
  intro K V _ _ _ _ T r a ha hd hfull s b hb hfullb f
  apply D05.M13.AlgebraicProjections.ext_on_eigenspaces hd hfull
  intro i v hv
  have hev : T.HasEigenvalue (a i) := (hfull (a i)).mpr ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := (hfullb (a i)).mp hev
  rw [action_on_eigenspace T a ha _ i v hv,
    action_on_eigenspace T b hb _ j v (hj.symm ▸ hv)]
  apply congrArg (fun z : T.Eigenvalues => f z • v)
  exact Subtype.ext hj.symm

theorem empty_sum : Specs.D05.M13.FunctionalCalculus.empty_sum := by
  intro K V _ _ _ T a f
  exact Finset.sum_empty

theorem zero_space : Specs.D05.M13.FunctionalCalculus.zero_space := by
  intro K V _ _ _ _ T r a f
  constructor <;> ext v <;> exact Subsingleton.elim _ _

/-- The adjoint computation uses the proved orthogonal/interpolation bridge. -/
theorem adjoint_conjugate : Specs.D05.M13.FunctionalCalculus.adjoint_conjugate := by
  intro F V _ _ _ _ T hn hd r a ha hfull f
  have hp (i : Fin r) :
      LinearMap.adjoint (D05.M13.AlgebraicProjections.projection F V T r a i) =
        D05.M13.AlgebraicProjections.projection F V T r a i := by
    rw [← D05.M13.SpectralProjections.projection_eq_interpolation T hn hd a ha hfull i]
    exact (D05.M13.SpectralProjections.projection_properties T (a i)).2.2.2.symm
  unfold Specs.D05.M13.FunctionalCalculus.functionalCalculus_value
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smulₛₗ, hp i]
  rfl

theorem real_adjoint_conjugate : Specs.D05.M13.FunctionalCalculus.real_adjoint_conjugate := by
  intro V _ _ _ T hT r a ha hfull f
  obtain ⟨b, _, μ, hb⟩ := D05.M13.RealSpectral.exists_orthonormal_eigenbasis T hT
  exact adjoint_conjugate T
    (D05.M13.SelfAdjoint.selfAdjoint_implies_normal T hT)
    ⟨Module.finrank ℝ V, b, μ, hb⟩ a ha hfull f

theorem complex_adjoint_conjugate : Specs.D05.M13.FunctionalCalculus.complex_adjoint_conjugate := by
  intro V _ _ _ T hT r a ha hfull f
  obtain ⟨b, _, μ, hb⟩ := D05.M13.ComplexSpectral.normal_has_orthonormal_eigenbasis T hT
  exact adjoint_conjugate T hT ⟨Module.finrank ℂ V, b, μ, hb⟩ a ha hfull f

end D05.M13.FunctionalCalculus
