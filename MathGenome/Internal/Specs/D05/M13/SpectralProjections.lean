import MathGenome.Internal.Specs.D05.M12.Projection
import MathGenome.Internal.Specs.D05.M13.AlgebraicProjections
import MathGenome.Internal.Specs.D05.M13.ComplexSpectral
import MathGenome.Internal.Specs.D05.M13.RealSpectral

/-! Independent specifications for K05.13.spectral_projections,
paper.tex:2264–2271. We reuse the canonical orthogonal projection of M12
and the literal interpolation-polynomial evaluation of M13. The finite list
is injective and contains exactly the eigenvalues, without multiplicities.
The existence statements construct such lists; no eigenbasis, splitting,
nonzero-space, or decomposition premise is added to the spectral hypotheses.
All inner products and adjoints use the established paper convention. -/
noncomputable section
namespace Specs.D05.M13.SpectralProjections
open scoped BigOperators

/-- The two decompositions and the equality with the interpolation polynomials.
This is a conclusion predicate, never an assumed decomposition certificate. -/
def Resolution {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V) {r : ℕ} (a : Fin r → F) : Prop :=
  (∑ i, _root_.D05.orthogonalProjection (T.eigenspace (a i))) = LinearMap.id ∧
  (∑ i, a i • _root_.D05.orthogonalProjection (T.eigenspace (a i))) = T ∧
  ∀ i, _root_.D05.orthogonalProjection (T.eigenspace (a i)) =
    Specs.D05.M13.AlgebraicProjections.projection_value F V T r a i

/-- An orthogonal eigenspace projection has the specified range and kernel,
is idempotent, and is self-adjoint. This requires no spectral hypothesis. -/
def projection_properties : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V) (μ : F),
    let P := _root_.D05.orthogonalProjection (T.eigenspace μ)
    P.range = T.eigenspace μ ∧ P.ker = (T.eigenspace μ).orthogonal ∧
      P ^ 2 = P ∧ _root_.D05.selfAdjoint P

/-- Distinct spectral projections annihilate one another, as maps. -/
def distinct_projections_mul : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V), _root_.D05.normalOperator T →
    ∀ μ ν : F, μ ≠ ν →
      _root_.D05.orthogonalProjection (T.eigenspace μ) *
        _root_.D05.orthogonalProjection (T.eigenspace ν) = 0

/-- No finite enumeration is an extra existence assumption. -/
def finite_spectrum : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    ∃ (r : ℕ) (a : Fin r → F), Function.Injective a ∧
      ∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ

def real_resolution : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : Module.End ℝ V), _root_.D05.selfAdjoint T →
    ∀ {r : ℕ} (a : Fin r → ℝ), Function.Injective a →
      (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) → Resolution T a

def complex_resolution : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V), _root_.D05.normalOperator T →
    ∀ {r : ℕ} (a : Fin r → ℂ), Function.Injective a →
      (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) → Resolution T a

/-- Existence of the complete real orthogonal spectral resolution. -/
def real_exists_resolution : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : Module.End ℝ V), _root_.D05.selfAdjoint T →
    ∃ (r : ℕ) (a : Fin r → ℝ), Function.Injective a ∧
      (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) ∧ Resolution T a

/-- Existence of the complete complex orthogonal spectral resolution. -/
def complex_exists_resolution : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V), _root_.D05.normalOperator T →
    ∃ (r : ℕ) (a : Fin r → ℂ), Function.Injective a ∧
      (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) ∧ Resolution T a

/-- On the zero space the spectrum is empty, and both displayed sums are
empty. The identity and T are also zero. -/
def zero_space : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] [Subsingleton V]
    (T : Module.End F V) (a : Fin 0 → F),
    (∀ μ, ¬ T.HasEigenvalue μ) ∧ Resolution T a

end Specs.D05.M13.SpectralProjections
