import MathGenome.Internal.Specs.D05.M13.Normal
import MathGenome.Internal.Specs.D05.M06.Invariant
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Independent statements for the subspace part of K05.13.normal_reducing,
paper.tex:2193–2207. The commutant/graph consequence belongs to the later stage.
Normality, invariance and restrictions are the canonical upstream objects.
The adjoint uses the already proved firstInner(u,v) = inner F v u convention.
All dimensions, including those of either summand, may be zero. -/

noncomputable section
namespace Specs.D05.M13.NormalReducing.Subspace
universe u v

/-- The upper-left normality equation and the trace/sum-of-squares argument
for an arbitrary orthonormal upper-triangular block matrix. -/
def block_trace_vanishing : Prop :=
  ∀ {F : Type u} [RCLike F] {m n : Type v} [Fintype m] [Fintype n],
  ∀ (A : Matrix m m F) (B : Matrix m n F) (C : Matrix n n F),
    let X := Matrix.fromBlocks A B 0 C
    X * X.conjTranspose = X.conjTranspose * X →
      A * A.conjTranspose + B * B.conjTranspose = A.conjTranspose * A ∧
      (B * B.conjTranspose).trace = 0 ∧
      (∑ i, ∑ j, ‖B i j‖ ^ 2) = 0 ∧ B = 0

/-- An invariant subspace of a finite-dimensional normal map is adjoint invariant. -/
def adjoint_invariant : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : V →ₗ[F] V) (M : Submodule F V),
    _root_.D05.normalOperator T →
    Specs.D05.M06.Invariant.invariant_value F V M T →
    Specs.D05.M06.Invariant.invariant_value F V M (LinearMap.adjoint T)

/-- Full reduction, the two restricted normality assertions, and the concrete
identification of their adjoints with the restrictions of the ambient adjoint. -/
def invariant_and_normal_restrictions : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : V →ₗ[F] V) (M : Submodule F V),
    _root_.D05.normalOperator T →
  ∀ hM : Specs.D05.M06.Invariant.invariant_value F V M T,
    ∃ hMa : Specs.D05.M06.Invariant.invariant_value F V M (LinearMap.adjoint T),
    ∃ hP : Specs.D05.M06.Invariant.invariant_value F V M.orthogonal T,
    ∃ hPa : Specs.D05.M06.Invariant.invariant_value F V M.orthogonal
      (LinearMap.adjoint T),
      _root_.D05.normalOperator (Specs.D05.M06.Invariant.restriction_value F V M T hM) ∧
      _root_.D05.normalOperator
        (Specs.D05.M06.Invariant.restriction_value F V M.orthogonal T hP) ∧
      _root_.D05.normalOperator
        (Specs.D05.M06.Invariant.restriction_value F V M (LinearMap.adjoint T) hMa) ∧
      _root_.D05.normalOperator
        (Specs.D05.M06.Invariant.restriction_value F V M.orthogonal
          (LinearMap.adjoint T) hPa) ∧
      LinearMap.adjoint (Specs.D05.M06.Invariant.restriction_value F V M T hM) =
        Specs.D05.M06.Invariant.restriction_value F V M (LinearMap.adjoint T) hMa ∧
      LinearMap.adjoint
        (Specs.D05.M06.Invariant.restriction_value F V M.orthogonal T hP) =
        Specs.D05.M06.Invariant.restriction_value F V M.orthogonal
          (LinearMap.adjoint T) hPa

end Specs.D05.M13.NormalReducing.Subspace
