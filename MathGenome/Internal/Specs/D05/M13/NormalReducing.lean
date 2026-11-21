import MathGenome.Internal.Specs.D05.M13.NormalReducing.Subspace
import MathGenome.Internal.Specs.D05.M13.NormalReducing.Graph

/-! Independent specifications for K05.13.normal_reducing, paper.tex:2193–2207.
The scalar field is real or complex (`RCLike`), and the ambient space is finite
 dimensional, including dimension zero. Normality, the adjoint, invariance and
 restriction reuse the canonical upstream definitions. In particular the adjoint
 is the one for firstInner x y = inner F y x. No spectral assumption is added. -/

noncomputable section
namespace Specs.D05.M13.NormalReducing
universe u v

/-- Every invariant subspace reduces a finite-dimensional normal operator. -/
def invariant_subspace_reduces : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : V →ₗ[F] V) (M : Submodule F V),
    _root_.D05.normalOperator T →
    Specs.D05.M06.Invariant.invariant_value F V M T →
      Specs.D05.M06.Invariant.invariant_value F V M T.adjoint ∧
      Specs.D05.M06.Invariant.invariant_value F V M.orthogonal T ∧
      Specs.D05.M06.Invariant.invariant_value F V M.orthogonal T.adjoint

/-- The normal restrictions and their adjoints, as in the proof's block
 diagonal conclusion. The witnesses assert invariance, not normality. -/
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


/-- The full commutant conclusion, for an arbitrary linear endomorphism S. -/
def commutes_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T S : V →ₗ[F] V),
    _root_.D05.normalOperator T → S.comp T = T.comp S →
      S.comp T.adjoint = T.adjoint.comp S

/-- The two assertions in the displayed source theorem, together. -/
def normal_reducing : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T →
      (∀ M : Submodule F V,
        Specs.D05.M06.Invariant.invariant_value F V M T →
          Specs.D05.M06.Invariant.invariant_value F V M T.adjoint ∧
          Specs.D05.M06.Invariant.invariant_value F V M.orthogonal T ∧
          Specs.D05.M06.Invariant.invariant_value F V M.orthogonal T.adjoint) ∧
      (∀ S : V →ₗ[F] V, S.comp T = T.comp S →
        S.comp T.adjoint = T.adjoint.comp S)

end Specs.D05.M13.NormalReducing
