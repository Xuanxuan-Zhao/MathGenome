import MathGenome.Internal.Specs.D05.M14.SingularValues
import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-! Independent specification of paper.tex:2459–2470.
The absolute value is the real norm over either real or complex scalars.
The square root is the nonnegative real square root: `re` extracts the real
Gram determinant, whose reality and nonnegativity are stated explicitly below.
The shared finite list contains every singular value, including zero occurrences.
No invertibility or positive-dimension hypothesis is imposed on the main identity.
-/

namespace Specs.D05.M14.Svd.Determinant

universe u v

def det_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    (LinearMap.adjoint T).det = starRingEnd F T.det

def det_gram : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    ((LinearMap.adjoint T).comp T).det = ((‖T.det‖ ^ 2 : ℝ) : F)

def gram_det_real_nonneg : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    (RCLike.re ((LinearMap.adjoint T).comp T).det : F) = ((LinearMap.adjoint T).comp T).det ∧
    0 ≤ RCLike.re ((LinearMap.adjoint T).comp T).det

def norm_det_eq_sqrt : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    ‖T.det‖ = Real.sqrt (RCLike.re ((LinearMap.adjoint T).comp T).det)

def norm_det_eq_prod : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    ‖T.det‖ = (_root_.D05.singularValues T).prod

def determinant_identity : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    ‖T.det‖ = Real.sqrt (RCLike.re ((LinearMap.adjoint T).comp T).det) ∧
    Real.sqrt (RCLike.re ((LinearMap.adjoint T).comp T).det) = (_root_.D05.singularValues T).prod

def singular_case : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    ¬Function.Injective T →
    0 ∈ _root_.D05.singularValues T ∧ T.det = 0 ∧
    Real.sqrt (RCLike.re ((LinearMap.adjoint T).comp T).det) = 0 ∧
    (_root_.D05.singularValues T).prod = 0

def zero_dim_case : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    Module.finrank F V = 0 →
    T.det = 1 ∧ _root_.D05.singularValues T = [] ∧
    Real.sqrt (RCLike.re ((LinearMap.adjoint T).comp T).det) = 1 ∧
    (_root_.D05.singularValues T).prod = 1

def coordinate_determinant : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    ∀ {n : ℕ} (b : Module.Basis (Fin n) F V),
    ‖_root_.D05.M05.determinant (T.toMatrix b b)‖ = (_root_.D05.singularValues T).prod

/-- Discarding zeros cannot give the determinant formula for singular maps,
even when the positive list is empty (its product is one). -/
def positive_only_not_eq : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    ¬Function.Injective T →
    (_root_.D05.positiveSingularValues T).prod ≠ ‖T.det‖

end Specs.D05.M14.Svd.Determinant
