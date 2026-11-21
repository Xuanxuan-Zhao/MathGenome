import MathGenome.Internal.Specs.D05.M13.AdjointLaws
import MathGenome.Internal.D05.M04.Composition
import MathGenome.Internal.D05.M12.OnBasis
import MathGenome.Internal.D05.M13.Adjoint

/-! K05.13.adjoint_laws: algebra, orthonormal matrices, and inverses of adjoints. -/

noncomputable section

namespace D05.M13.AdjointLaws

theorem adjoint_add : Specs.D05.M13.AdjointLaws.adjoint_add := by
  intro F V W _ _ _ _ _ _ _ S T
  exact map_add _ S T

theorem adjoint_smul : Specs.D05.M13.AdjointLaws.adjoint_smul := by
  intro F V W _ _ _ _ _ _ _ a T
  exact map_smulₛₗ _ a T

theorem adjoint_comp : Specs.D05.M13.AdjointLaws.adjoint_comp := by
  intro F U V W _ _ _ _ _ _ _ _ _ _ S T
  exact _root_.LinearMap.adjoint_comp S T

theorem adjoint_adjoint : Specs.D05.M13.AdjointLaws.adjoint_adjoint := by
  intro F V W _ _ _ _ _ _ _ T
  exact _root_.LinearMap.adjoint_adjoint T

/-- Convert the given bases using the proved convention bridge. Their vectors
and coordinate maps are preserved by `toOrthonormalBasis`. -/
theorem matrix_adjoint : Specs.D05.M13.AdjointLaws.matrix_adjoint := by
  intro F V W _ _ _ _ _ _ _ n m b c hb hc T
  have hb' : Orthonormal F b := (D05.M12.Orthonormal.orthonormal_iff_mathlib b).mp hb
  have hc' : Orthonormal F c := (D05.M12.Orthonormal.orthonormal_iff_mathlib c).mp hc
  simpa only [Module.Basis.toBasis_toOrthonormalBasis,
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value] using
    _root_.LinearMap.toMatrix_adjoint (b.toOrthonormalBasis hb')
      (c.toOrthonormalBasis hc') T

theorem matrix_adjoint_entry : Specs.D05.M13.AdjointLaws.matrix_adjoint_entry := by
  intro F V W _ _ _ _ _ _ _ n m b c hb hc T i j
  rw [matrix_adjoint b c hb hc T]
  rfl

theorem adjoint_id : Specs.D05.M13.AdjointLaws.adjoint_id := by
  intro F V _ _ _ _
  exact _root_.LinearMap.adjoint_id

/-- Apply the adjoint operation to each of the original inverse identities. -/
theorem adjoint_inverse_identities :
    Specs.D05.M13.AdjointLaws.adjoint_inverse_identities := by
  intro F V W _ _ _ _ _ _ _ T S hST hTS
  constructor
  · rw [← adjoint_comp S T, hST, adjoint_id]
  · rw [← adjoint_comp T S, hTS, adjoint_id]

/-- Bundle those inverse maps as a linear equivalence to express the actual
inverse formula, with no assumption that the map preserves inner products. -/
theorem adjoint_inverse : Specs.D05.M13.AdjointLaws.adjoint_inverse := by
  intro F V W _ _ _ _ _ _ _ e
  have hST : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext v
    exact e.symm_apply_apply v
  have hTS : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext w
    exact e.apply_symm_apply w
  obtain ⟨h₁, h₂⟩ := adjoint_inverse_identities e.toLinearMap e.symm.toLinearMap hST hTS
  let eAdj : W ≃ₗ[F] V :=
    { _root_.LinearMap.adjoint e.toLinearMap with
      invFun := _root_.LinearMap.adjoint e.symm.toLinearMap
      left_inv := fun w => DFunLike.congr_fun h₂ w
      right_inv := fun v => DFunLike.congr_fun h₁ v }
  exact ⟨eAdj, rfl, rfl⟩

end D05.M13.AdjointLaws
