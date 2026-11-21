import MathGenome.Internal.Specs.D05.M13.RealSpectral
import MathGenome.Internal.D05.M13.SelfAdjoint
import MathGenome.Internal.D05.M12.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Hermitian

/-! The real spectral theorem, including the zero-dimensional case. -/

noncomputable section

namespace D05.M13.RealSpectral

theorem exists_orthonormal_eigenbasis :
    Specs.D05.M13.RealSpectral.exists_orthonormal_eigenbasis := by
  intro V _ _ _ T hT
  have hs := (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric T).mp hT
  let b := hs.eigenvectorBasis rfl
  refine ⟨b.toBasis,
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal,
    hs.eigenvalues rfl, ?_⟩
  intro i
  exact hs.apply_eigenvectorBasis rfl i

/-- In an orthonormal eigenbasis the real matrix is diagonal, hence Hermitian.
Transport its symmetry back to the original map and use the shared adjoint bridge. -/
theorem selfAdjoint_of_orthonormal_eigenbasis :
    Specs.D05.M13.RealSpectral.selfAdjoint_of_orthonormal_eigenbasis := by
  intro V _ _ _ ι _ T b hb he
  classical
  choose μ hμ using he
  let e := b.toOrthonormalBasis
    ((D05.M12.Orthonormal.orthonormal_iff_mathlib b).mp hb)
  have hmatrix : T.toMatrix b b = Matrix.diagonal μ := by
    ext i j
    by_cases hij : i = j <;>
      simp [LinearMap.toMatrix_apply, hμ, Matrix.diagonal_apply,
        Finsupp.single_apply, hij, eq_comm]
  apply (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric T).mpr
  apply (LinearMap.isHermitian_toMatrix_iff e).mp
  simpa only [e, Module.Basis.toBasis_toOrthonormalBasis, hmatrix] using
    Matrix.isHermitian_diagonal μ

theorem real_spectral : Specs.D05.M13.RealSpectral.real_spectral := by
  intro V _ _ _ T
  constructor
  · rintro ⟨b, hb, he⟩
    exact selfAdjoint_of_orthonormal_eigenbasis T b hb he
  · intro hT
    obtain ⟨b, hb, μ, he⟩ := exists_orthonormal_eigenbasis T hT
    exact ⟨b, hb, fun i => ⟨μ i, he i⟩⟩

end D05.M13.RealSpectral
