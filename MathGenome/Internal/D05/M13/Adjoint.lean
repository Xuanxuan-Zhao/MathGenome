import MathGenome.Internal.Specs.D05.M13.Adjoint
import MathGenome.Internal.D05.M03.LinearMap
import MathGenome.Internal.D05.M12.Riesz

/-! K05.13.adjoint: the canonical adjoint, in the first-slot-linear convention. -/

noncomputable section

namespace D05.M13.Adjoint

/-- The adjoint is a linear map in the reverse direction. -/
def adjoint {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) : W →ₗ[F] V := _root_.LinearMap.adjoint T

/-- Swapping Mathlib's inner-product arguments gives exactly the paper identity. -/
theorem adjoint_identity : Specs.D05.M13.Adjoint.adjoint_identity := by
  intro F V W _ _ _ _ _ _ _ T v w
  exact (_root_.LinearMap.adjoint_inner_left T v w).symm

/-- Pointwise uniqueness is uniqueness of the Riesz representing vector of
`v ↦ firstInner (T v) w`, a functional on the original domain. -/
theorem adjoint_unique : Specs.D05.M13.Adjoint.adjoint_unique := by
  intro F V W _ _ _ _ _ _ _ T S hS
  ext w
  apply D05.M12.Riesz.representing_vector_unique ((innerₛₗ F w).comp T)
  · intro v
    exact hS v w
  · intro v
    exact adjoint_identity T v w

theorem exists_unique_adjoint :
    Specs.D05.M13.Adjoint.exists_unique_adjoint := by
  intro F V W _ _ _ _ _ _ _ T
  exact ⟨adjoint T, adjoint_identity T, fun S hS => adjoint_unique T S hS⟩

theorem adjoint_linear : Specs.D05.M13.Adjoint.adjoint_linear := by
  intro F V W _ _ _ _ _ _ _ T a b w₁ w₂
  simp only [map_add, map_smul]

theorem zero_domain : Specs.D05.M13.Adjoint.zero_domain := by
  intro F V W _ _ _ _ _ _ _ _ T
  ext w
  exact Subsingleton.elim _ _

theorem zero_codomain : Specs.D05.M13.Adjoint.zero_codomain := by
  intro F V W _ _ _ _ _ _ _ _ T
  ext w
  have hw : w = 0 := Subsingleton.elim _ _
  simp [hw]

end D05.M13.Adjoint
