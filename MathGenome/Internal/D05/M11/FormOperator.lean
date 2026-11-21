import MathGenome.Internal.Specs.D05.M11.FormOperator
import MathGenome.Internal.D05.M11.Hermitian
import MathGenome.Internal.D05.M12.OnBasis
import MathGenome.Internal.D05.M12.Riesz
import MathGenome.Internal.D05.M13.Adjoint

/-! Representing forms by operators, in the paper's first-slot-linear convention.
The construction is the finite orthonormal-basis sum; uniqueness then removes
its dependence on the chosen basis. No spectral classification is used. -/
noncomputable section

namespace D05.M11.FormOperator

open Module
open scoped BigOperators

/-- Bundle the paper's explicit formula as a linear map. -/
def basisOperator {F V I : Type*} [RCLike F] [AddCommGroup V] [Module F V]
    [Fintype I] (e : Basis I F V) (B : Hermitian.sesquilinearForm F V) : V →ₗ[F] V :=
  ∑ j, (B.flip (e j)).smulRight (e j)

/-- Use one orthonormal basis to define the operator; `basis_independent`
proves that every other orthonormal basis yields the same map. -/
def formOperator {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (B : Hermitian.sesquilinearForm F V) : V →ₗ[F] V :=
  basisOperator (stdOrthonormalBasis F V).toBasis B

/-- Real bilinear forms are sesquilinear forms with trivial conjugation. -/
def realForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) : Hermitian.sesquilinearForm ℝ V := B

theorem basisOperator_apply : Specs.D05.M11.FormOperator.basisOperator_apply := by
  intro F V I _ _ _ _ e B u
  simp [Specs.D05.M11.FormOperator.basisOperator_value]

theorem representation_in_basis : Specs.D05.M11.FormOperator.representation_in_basis := by
  intro F V I _ _ _ _ e he B u v
  rw [basisOperator_apply]
  have hv := D05.M12.FourierParseval.fourier_expansion e he v
  calc
    D05.firstInner (F := F) (∑ j, B u (e j) • e j) v =
        ∑ j, B u (e j) * D05.firstInner (F := F) (e j) v := by
      simp only [D05.firstInner, inner_sum, inner_smul_right]
    _ = ∑ j, star (D05.firstInner (F := F) v (e j)) * B u (e j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [D05.M12.InnerProduct.firstInner_conjugate v (e j)]
      exact mul_comm _ _
    _ = B u (∑ j, D05.firstInner (F := F) v (e j) • e j) := by
      simp only [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
    _ = B u v := congrArg (B u) hv.symm

theorem representing_operator_unique :
    Specs.D05.M11.FormOperator.representing_operator_unique := by
  intro F V _ _ _ B A A' hA hA'
  ext u
  apply ext_inner_left F
  intro v
  exact (hA u v).trans (hA' u v).symm

theorem representation : Specs.D05.M11.FormOperator.representation := by
  intro F V _ _ _ _ B u v
  exact representation_in_basis (stdOrthonormalBasis F V).toBasis
    ((D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr
      (stdOrthonormalBasis F V).orthonormal) B u v

theorem exists_unique_representation :
    Specs.D05.M11.FormOperator.exists_unique_representation := by
  intro F V _ _ _ _ B
  exact ⟨formOperator B, representation B,
    fun A hA => representing_operator_unique B A _ hA (representation B)⟩

theorem basis_independent : Specs.D05.M11.FormOperator.basis_independent := by
  intro F V I J _ _ _ _ _ e f he hf B
  exact representing_operator_unique B _ _
    (representation_in_basis e he B) (representation_in_basis f hf B)

theorem formula_in_any_basis : Specs.D05.M11.FormOperator.formula_in_any_basis := by
  intro F V I _ _ _ _ _ e he B u
  have h := representing_operator_unique B _ _ (representation B)
    (representation_in_basis e he B)
  rw [LinearMap.congr_fun h u]
  exact basisOperator_apply e B u

theorem hermitian_iff_adjoint : Specs.D05.M11.FormOperator.hermitian_iff_adjoint := by
  intro F V _ _ _ _ B
  let A := Specs.D05.M11.FormOperator.formOperator_value B
  constructor
  · intro hB
    symm
    apply D05.M13.Adjoint.adjoint_unique A A
    intro u v
    calc
      D05.firstInner (F := F) (A u) v = B u v := representation B u v
      _ = star (B v u) := hB v u
      _ = star (D05.firstInner (F := F) (A v) u) :=
        congrArg star (representation B v u).symm
      _ = D05.firstInner (F := F) u (A v) :=
        (D05.M12.InnerProduct.firstInner_conjugate (A v) u).symm
  · intro hA u v
    calc
      B v u = D05.firstInner (F := F) (A v) u := (representation B v u).symm
      _ = D05.firstInner (F := F) v (A u) := by
        rw [D05.M13.Adjoint.adjoint_identity A v u]
        exact congrArg (D05.firstInner (F := F) v) (LinearMap.congr_fun hA u)
      _ = star (D05.firstInner (F := F) (A u) v) :=
        D05.M12.InnerProduct.firstInner_conjugate (A u) v
      _ = star (B u v) := congrArg star (representation B u v)

theorem hermitian_iff_selfAdjoint :
    Specs.D05.M11.FormOperator.hermitian_iff_selfAdjoint := by
  intro F V _ _ _ _ B
  exact hermitian_iff_adjoint B

theorem diagonal_identity : Specs.D05.M11.FormOperator.diagonal_identity := by
  intro F V _ _ _ _ B u
  exact (representation B u u).symm

theorem positive_definite_iff : Specs.D05.M11.FormOperator.positive_definite_iff := by
  intro F V _ _ _ _ B
  simp only [← hermitian_iff_adjoint B, representation B]

theorem positive_semidefinite_iff :
    Specs.D05.M11.FormOperator.positive_semidefinite_iff := by
  intro F V _ _ _ _ B
  simp only [← hermitian_iff_adjoint B, representation B]

theorem realForm_apply : Specs.D05.M11.FormOperator.realForm_apply := by
  intro V _ _ B u v
  rfl

theorem real_bilinear_representation :
    Specs.D05.M11.FormOperator.real_bilinear_representation := by
  intro V _ _ _ B
  exact exists_unique_representation (realForm B)

theorem real_symmetric_iff_adjoint :
    Specs.D05.M11.FormOperator.real_symmetric_iff_adjoint := by
  intro V _ _ _ B
  rw [← hermitian_iff_adjoint]
  exact ⟨fun h u v => h v u, fun h u v => h v u⟩

end D05.M11.FormOperator
