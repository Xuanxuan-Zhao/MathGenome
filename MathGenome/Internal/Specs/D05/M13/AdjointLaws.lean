import MathGenome.Internal.Specs.D05.M13.Adjoint
import MathGenome.Internal.Specs.D05.M12.OnBasis
import MathGenome.Internal.Specs.D05.M04.Composition

/-!
Independent specifications for K05.13.adjoint_laws, paper.tex:2088–2101.
The canonical adjoint and matrix construction are those of the upstream Specs.
The paper uses `D05.firstInner u v = inner F v u`; its orthonormal predicate
is retained for the chosen ordered bases. All spaces may have dimension zero,
and domain and codomain dimensions are independent. No completeness or
invertibility assumption is imposed on the algebraic or matrix laws.
-/

noncomputable section

namespace Specs.D05.M13.AdjointLaws

universe u v w x

/-- Addition of maps with common domain and codomain. -/
def adjoint_add : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ S T : V →ₗ[F] W,
    _root_.LinearMap.adjoint (S + T) =
      _root_.LinearMap.adjoint S + _root_.LinearMap.adjoint T

/-- Scalar multiplication conjugates the scalar. -/
def adjoint_smul : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ (a : F) (T : V →ₗ[F] W),
    _root_.LinearMap.adjoint (a • T) =
      starRingEnd F a • _root_.LinearMap.adjoint T

/-- Composition reverses order, for three arbitrary compatible spaces. -/
def adjoint_comp : Prop :=
  ∀ {F : Type u} {U : Type v} {V : Type w} {W : Type x} [RCLike F]
    [NormedAddCommGroup U] [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F U] [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F U] [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ (S : V →ₗ[F] W) (T : U →ₗ[F] V),
    _root_.LinearMap.adjoint (S.comp T) =
      (_root_.LinearMap.adjoint T).comp (_root_.LinearMap.adjoint S)

/-- Taking adjoints twice returns the original map. -/
def adjoint_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ T : V →ₗ[F] W,
    _root_.LinearMap.adjoint (_root_.LinearMap.adjoint T) = T

/-- In any two orthonormal ordered bases the matrix is conjugate transpose. -/
def matrix_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ {n m : ℕ} (b : Module.Basis (Fin n) F V) (c : Module.Basis (Fin m) F W),
    _root_.D05.orthonormalFamily (F := F) b →
    _root_.D05.orthonormalFamily (F := F) c →
  ∀ T : V →ₗ[F] W,
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value c b (_root_.LinearMap.adjoint T) =
      Matrix.conjTranspose (Specs.D05.M04.MatrixOfMap.matrixOfMap_value b c T)

/-- The adjoint entry at row j, column i is the conjugate of the original (i,j) entry. -/
def matrix_adjoint_entry : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ {n m : ℕ} (b : Module.Basis (Fin n) F V) (c : Module.Basis (Fin m) F W),
    _root_.D05.orthonormalFamily (F := F) b →
    _root_.D05.orthonormalFamily (F := F) c →
  ∀ (T : V →ₗ[F] W) (i : Fin m) (j : Fin n),
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value c b (_root_.LinearMap.adjoint T) j i =
      starRingEnd F (Specs.D05.M04.MatrixOfMap.matrixOfMap_value b c T i j)

/-- The identity map is its own adjoint, including on the zero space. -/
def adjoint_id : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  _root_.LinearMap.adjoint (LinearMap.id : V →ₗ[F] V) = LinearMap.id

/-- Adjoints of two-sided inverse maps are two-sided inverses in reverse order. -/
def adjoint_inverse_identities : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ (T : V →ₗ[F] W) (S : W →ₗ[F] V),
    S.comp T = LinearMap.id → T.comp S = LinearMap.id →
    (_root_.LinearMap.adjoint T).comp (_root_.LinearMap.adjoint S) = LinearMap.id ∧
    (_root_.LinearMap.adjoint S).comp (_root_.LinearMap.adjoint T) = LinearMap.id

/-- The adjoint of an isomorphism is an isomorphism, whose inverse is the adjoint of the inverse. -/
def adjoint_inverse : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ e : V ≃ₗ[F] W, ∃ eAdj : W ≃ₗ[F] V,
    eAdj.toLinearMap = _root_.LinearMap.adjoint e.toLinearMap ∧
    _root_.LinearMap.adjoint e.symm.toLinearMap = eAdj.symm.toLinearMap

end Specs.D05.M13.AdjointLaws
