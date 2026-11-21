import MathGenome.Internal.Specs.D05.M13.Unitary
import MathGenome.Internal.Specs.D05.M14.Positive

/-! K05.14.polar, paper.tex:2602–2609. The positive factor is the unique
positive square root of the actual Gram operator. Statements about an arbitrary
such root avoid introducing a second choice-dependent square-root operation.
`IsUnitaryMap` means unitary over ℂ and orthogonal over ℝ. All dimensions,
including zero, are allowed. Invertibility is expressed as linear bijectivity. -/

namespace Specs.D05.M14.Polar

def exists_polar : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    ∃ P U : Module.End F V, _root_.D05.positiveSemidefinite P ∧
      P ^ 2 = (LinearMap.adjoint T) * T ∧ _root_.D05.IsUnitaryMap U ∧ U * P = T

/-- In particular this applies to the square root constructed in PositiveRoot. -/
def factor_for_positive_root : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T P : Module.End F V),
    _root_.D05.positiveSemidefinite P → P ^ 2 = (LinearMap.adjoint T) * T →
      ∃ U : Module.End F V, _root_.D05.IsUnitaryMap U ∧ U * P = T

def unitary_factor_unique : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T P : Module.End F V),
    Function.Bijective T → _root_.D05.positiveSemidefinite P →
    P ^ 2 = (LinearMap.adjoint T) * T → ∀ U₁ U₂ : Module.End F V,
    _root_.D05.IsUnitaryMap U₁ → _root_.D05.IsUnitaryMap U₂ →
    U₁ * P = T → U₂ * P = T → U₁ = U₂

def existsUnique_unitary_factor : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T P : Module.End F V),
    Function.Bijective T → _root_.D05.positiveSemidefinite P →
    P ^ 2 = (LinearMap.adjoint T) * T →
      ∃! U : Module.End F V, _root_.D05.IsUnitaryMap U ∧ U * P = T

/-- The root is invertible and the unitary factor is T composed with its inverse. -/
def invertible_formula : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T P U : Module.End F V),
    Function.Bijective T → _root_.D05.IsUnitaryMap U → U * P = T →
      ∃ e : V ≃ₗ[F] V, e.toLinearMap = P ∧ U = T * e.symm.toLinearMap

/-- Every singular endomorphism admits two distinct completions for the same
positive root. No nonzero-space premise is needed: singularity implies it. -/
def singular_nonunique : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T P : Module.End F V),
    ¬ Function.Bijective T → _root_.D05.positiveSemidefinite P →
    P ^ 2 = (LinearMap.adjoint T) * T →
      ∃ U₁ U₂ : Module.End F V, _root_.D05.IsUnitaryMap U₁ ∧
        _root_.D05.IsUnitaryMap U₂ ∧ U₁ * P = T ∧ U₂ * P = T ∧ U₁ ≠ U₂

/-- Explicitly records the boundary mentioned in the proof: the unique
endomorphism of a zero space is invertible and has one unitary factor. -/
def zero_space : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] [Subsingleton V]
    (T P : Module.End F V), Function.Bijective T ∧
      ∃! U : Module.End F V, _root_.D05.IsUnitaryMap U ∧ U * P = T

end Specs.D05.M14.Polar
