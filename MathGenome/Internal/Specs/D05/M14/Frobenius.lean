import MathGenome.Internal.Specs.D05.M14.OperatorNorm
import MathGenome.Internal.Specs.D05.M04.Trace

/-! K05.14.frobenius, paper.tex:2588–2600.
All spaces may have dimension zero. The canonical column-sum definition is
bridged to every orthonormal matrix representation. Trace identities are in F,
with an explicit real-to-F coercion, not merely equality of real parts.
-/
noncomputable section
namespace D05
variable {F V W : Type*} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- Frobenius norm, initially using the columns in a chosen standard ONB. -/
def frobeniusNorm (T : V →ₗ[F] W) : ℝ :=
  Real.sqrt (∑ j, ‖T (stdOrthonormalBasis F V j)‖ ^ 2)
end D05

namespace Specs.D05.M14.Frobenius
universe u v w i j i' j'

def frobeniusNorm_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {F : Type u} → {V : Type v} → {W : Type w} → [RCLike F] →
  [NormedAddCommGroup V] → [NormedAddCommGroup W] →
  [InnerProductSpace F V] → [InnerProductSpace F W] →
  [FiniteDimensional F V] → [FiniteDimensional F W] → (V →ₗ[F] W) → ℝ

def frobeniusNorm_value : frobeniusNorm_type.{u,v,w} :=
  fun {F} {V} {W} _ _ _ _ _ _ _ T =>
    Real.sqrt (∑ j, ‖T (stdOrthonormalBasis F V j)‖ ^ 2)

def nonneg : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W), 0 ≤ _root_.D05.frobeniusNorm T

def squared_basis_sum : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] {I : Type i} [Fintype I] (T : V →ₗ[F] W)
    (e : OrthonormalBasis I F V),
    _root_.D05.frobeniusNorm T ^ 2 = ∑ j, ‖T (e j)‖ ^ 2

def matrix_formula : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) {I : Type i} {J : Type j} [Fintype I] [Fintype J]
    (e : OrthonormalBasis I F V) (f : OrthonormalBasis J F W),
    _root_.D05.frobeniusNorm T ^ 2 =
      ∑ a, ∑ b, ‖LinearMap.toMatrix e.toBasis f.toBasis T a b‖ ^ 2

def basis_independent : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) {I : Type i} {J : Type j} [Fintype I] [Fintype J]
    (e : OrthonormalBasis I F V) (f : OrthonormalBasis J F W)
    {I' : Type i'} {J' : Type j'} [Fintype I'] [Fintype J']
    (e' : OrthonormalBasis I' F V) (f' : OrthonormalBasis J' F W),
    (∑ a, ∑ b, ‖LinearMap.toMatrix e.toBasis f.toBasis T a b‖ ^ 2) =
      ∑ a, ∑ b, ‖LinearMap.toMatrix e'.toBasis f'.toBasis T a b‖ ^ 2

def eq_matrix_sqrt : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) {I : Type i} {J : Type j} [Fintype I] [Fintype J]
    (e : OrthonormalBasis I F V) (f : OrthonormalBasis J F W),
    _root_.D05.frobeniusNorm T =
      Real.sqrt (∑ a, ∑ b, ‖LinearMap.toMatrix e.toBasis f.toBasis T a b‖ ^ 2)

def column_trace : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] {I : Type i} [Fintype I] (T : V →ₗ[F] W)
    (e : OrthonormalBasis I F V),
    LinearMap.trace F V ((LinearMap.adjoint T).comp T) =
      ((∑ j, ‖T (e j)‖ ^ 2 : ℝ) : F)

def trace_identity : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ((_root_.D05.frobeniusNorm T ^ 2 : ℝ) : F) =
      LinearMap.trace F V ((LinearMap.adjoint T).comp T)

def singular_sum : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.frobeniusNorm T ^ 2 =
      ∑ i : Fin (Module.finrank F (LinearMap.range T)), T.singularValues i ^ 2

def positive_list_sum : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.frobeniusNorm T ^ 2 =
      ((_root_.D05.positiveSingularValues T).map (fun s => s ^ 2)).sum

def operator_le : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.operatorNorm T ≤ _root_.D05.frobeniusNorm T

def le_sqrt_rank_mul_operator : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.frobeniusNorm T ≤
      Real.sqrt (Module.finrank F (LinearMap.range T) : ℝ) * _root_.D05.operatorNorm T

def zero_map : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] , _root_.D05.frobeniusNorm (0 : V →ₗ[F] W) = 0

def rank_zero : Prop := by
  classical
  exact ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W), Module.finrank F (LinearMap.range T) = 0 →
    _root_.D05.operatorNorm T = 0 ∧ _root_.D05.frobeniusNorm T = 0

end Specs.D05.M14.Frobenius
