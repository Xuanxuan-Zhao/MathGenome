import MathGenome.Internal.Specs.D05.M13.SelfAdjointEigenvalues
import MathGenome.Internal.D05.M09.Eigenspace
import MathGenome.Internal.D05.M13.NormalBasic
import MathGenome.Internal.D05.M13.SelfAdjoint

/-! Eigenvalue reality, eigenspace orthogonality, and the normal map i·id.
The argument uses only elementary upstream normal identities, with no spectral theorem. -/

namespace D05.M13.SelfAdjointEigenvalues

/-- The normal adjoint-eigenvector identity and self-adjointness give two
scalar multiples of one nonzero vector. Cancel that vector. -/
theorem selfAdjoint_eigenvector_conj_eq :
    Specs.D05.M13.SelfAdjointEigenvalues.selfAdjoint_eigenvector_conj_eq := by
  intro F V _ _ _ _ T hT μ x hx
  have ha := (D05.M13.NormalBasic.eigenvector_equation_iff T
    (D05.M13.SelfAdjoint.selfAdjoint_implies_normal T hT) μ x).mp hx.apply_eq_smul
  change T = LinearMap.adjoint T at hT
  rw [← hT] at ha
  have hz : (μ - starRingEnd F μ) • x = 0 := by
    rw [sub_smul, ← hx.apply_eq_smul, ← ha, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hx.2)

/-- Equality with the complex conjugate forces the imaginary part to vanish. -/
theorem complex_eigenvalue_real :
    Specs.D05.M13.SelfAdjointEigenvalues.complex_eigenvalue_real := by
  intro V _ _ _ T hT μ hμ
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hc := selfAdjoint_eigenvector_conj_eq T hT μ x hx
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  refine ⟨μ.re, ?_⟩
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

/-- Self-adjoint maps are normal, so apply the elementary upstream theorem. -/
theorem selfAdjoint_eigenvectors_orthogonal :
    Specs.D05.M13.SelfAdjointEigenvalues.selfAdjoint_eigenvectors_orthogonal := by
  intro F V _ _ _ _ T hT
  exact D05.M13.NormalBasic.eigenvectors_orthogonal T
    (D05.M13.SelfAdjoint.selfAdjoint_implies_normal T hT)

theorem selfAdjoint_eigenspaces_orthogonal :
    Specs.D05.M13.SelfAdjointEigenvalues.selfAdjoint_eigenspaces_orthogonal := by
  intro F V _ _ _ _ T hT
  exact D05.M13.NormalBasic.eigenspaces_orthogonal T
    (D05.M13.SelfAdjoint.selfAdjoint_implies_normal T hT)

theorem normal_eigenspaces_orthogonal :
    Specs.D05.M13.SelfAdjointEigenvalues.normal_eigenspaces_orthogonal :=
  D05.M13.NormalBasic.eigenspaces_orthogonal

/-- The conjugate scalar cancels i in the inner product; -i supplies a preimage. -/
theorem imaginary_multiple_unitary :
    Specs.D05.M13.SelfAdjointEigenvalues.imaginary_multiple_unitary := by
  intro V _ _ _
  constructor
  · intro x y
    simp [D05.firstInner, inner_smul_left, inner_smul_right, ← mul_assoc]
  · intro y
    refine ⟨(-Complex.I) • y, ?_⟩
    simp [smul_smul]

theorem imaginary_multiple_normal :
    Specs.D05.M13.SelfAdjointEigenvalues.imaginary_multiple_normal := by
  intro V _ _ _
  exact D05.M13.Normal.unitary_normal _ (imaginary_multiple_unitary (V := V))

theorem imaginary_multiple_hasEigenvalue :
    Specs.D05.M13.SelfAdjointEigenvalues.imaginary_multiple_hasEigenvalue := by
  intro V _ _ _ _
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := x)
  exact ⟨Module.End.mem_eigenspace_iff.mpr (by simp), hx⟩

theorem imaginary_not_real :
    Specs.D05.M13.SelfAdjointEigenvalues.imaginary_not_real := by
  rintro ⟨r, hr⟩
  have hi := congrArg Complex.im hr
  simp at hi

theorem normal_nonreal_counterexample :
    Specs.D05.M13.SelfAdjointEigenvalues.normal_nonreal_counterexample := by
  intro V _ _ _ _
  exact ⟨Complex.I • LinearMap.id, imaginary_multiple_unitary,
    imaginary_multiple_normal, imaginary_multiple_hasEigenvalue, imaginary_not_real⟩

end D05.M13.SelfAdjointEigenvalues
