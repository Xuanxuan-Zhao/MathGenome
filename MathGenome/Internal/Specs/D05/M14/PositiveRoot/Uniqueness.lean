import MathGenome.Internal.Specs.D05.M14.PositiveSpectrum

/-! Independent statements for the uniqueness stage of K05.14.positive_root,
paper.tex:2425–2433. Positivity is the shared semidefinite predicate, including
self-adjointness. Squares are products in the ordinary endomorphism algebra.
There is no preferred-root definition or nonzero-dimension assumption. -/

namespace Specs.D05.M14.PositiveRoot.Uniqueness

open Module.End

universe u v

/-- Every square root commutes with its square, without a positivity assumption. -/
def root_commutes : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T R : Module.End F V),
    R ^ 2 = T → R * T = T * R

/-- Commutation preserves every eigenspace, including the zero eigenspace. -/
def root_preserves_eigenspace : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T R : Module.End F V),
    R ^ 2 = T → ∀ (μ : F) (x : V),
      x ∈ T.eigenspace μ → R x ∈ T.eigenspace μ

/-- On the entire eigenspace, not just on selected eigenvectors, a positive
square root acts by the nonnegative real square root. Eigenvalues of positive
T are real by the upstream spectral characterization. Empty eigenspaces are allowed. -/
def root_on_eigenspace : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T R : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite R →
    R ^ 2 = T → ∀ (a : ℝ) (x : V), x ∈ T.eigenspace (a : F) →
      R x = (Real.sqrt a : F) • x

/-- The same conclusion quantified over all scalar-field eigenspaces. The
real part records the canonical identification of a positive eigenvalue with ℝ. -/
def root_on_scalar_eigenspace : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T R : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite R →
    R ^ 2 = T → ∀ (μ : F) (x : V), x ∈ T.eigenspace μ →
      R x = (Real.sqrt (RCLike.re μ) : F) • x

/-- Any eigenvalue of the actual restriction is sqrt a. The invariant-subspace
proof is arbitrary; its existence is supplied by root_preserves_eigenspace. -/
def restricted_eigenvalues : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T R : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite R →
    R ^ 2 = T → ∀ (a : ℝ)
      (hinv : ∀ x ∈ T.eigenspace (a : F), R x ∈ T.eigenspace (a : F)) (μ : F),
      Module.End.HasEigenvalue (R.restrict hinv) μ → μ = (Real.sqrt a : F)

/-- The zero eigenvalue case entails no division by an eigenvalue. -/
def root_vanishes_on_kernel : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T R : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite R →
    R ^ 2 = T → ∀ x : V, T x = 0 → R x = 0

/-- Uniqueness among positive square roots, with neither root preselected. -/
def positive_roots_unique : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T R S : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite R →
    _root_.D05.positiveSemidefinite S → R ^ 2 = T → S ^ 2 = T → R = S

end Specs.D05.M14.PositiveRoot.Uniqueness
