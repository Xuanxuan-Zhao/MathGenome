import MathGenome.Internal.Specs.D05.M13.SelfAdjoint

/-!
Independent statements for K05.13.self_adjoint, paper.tex:2126–2139.
The shared convention is `D05.firstInner u v = inner F v u`.
The first test requires self-adjointness over either real or complex scalars;
the two unrestricted tests are specifically complex. All statements allow the
zero space. Realness means membership in the image of ℝ → ℂ, with no positivity.
-/

namespace Specs.D05.M13.SelfAdjoint.DiagonalTests

universe u v

def selfAdjoint_zero_of_diagonal_zero : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (D : V →ₗ[F] V),
    _root_.D05.selfAdjoint D →
    (∀ v, _root_.D05.firstInner (F := F) (D v) v = 0) → D = 0

def complex_diagonal_zero_iff : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    (∀ v, _root_.D05.firstInner (F := ℂ) (T v) v = 0) ↔ T = 0

def complex_diagonal_real_iff : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    (∀ v, ∃ r : ℝ, _root_.D05.firstInner (F := ℂ) (T v) v = (r : ℂ)) ↔
      _root_.D05.selfAdjoint T

/-- The very same rotation fixed upstream has identically zero diagonal. -/
def rotation_diagonal_zero : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 2),
    _root_.D05.firstInner (F := ℝ) (_root_.D05.planeRotation v) v = 0

/-- Thus the unrestricted complex zero test has no unrestricted real analogue. -/
def real_zero_diagonal_counterexample : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
    T ≠ 0 ∧ (∀ v, _root_.D05.firstInner (F := ℝ) (T v) v = 0)

end Specs.D05.M13.SelfAdjoint.DiagonalTests
