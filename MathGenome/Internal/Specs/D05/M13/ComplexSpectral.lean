import MathGenome.Internal.Specs.D05.M13.Normal
import MathGenome.Internal.Specs.D05.M12.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Independent statements for K05.13.complex_spectral, paper.tex:2209–2215.
The normality predicate, adjoint and first-slot-linear orthonormality predicate
are the shared canonical objects. The basis has exactly dim V entries; each
entry satisfies its eigenvector equation. No positive-dimension, completeness,
splitting, or eigenvalue-existence hypothesis is imposed.
-/

namespace Specs.D05.M13.ComplexSpectral

universe u

def normal_has_orthonormal_eigenbasis : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    _root_.D05.normalOperator T →
      ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
        _root_.D05.orthonormalFamily (F := ℂ) b ∧
          ∃ μ : Fin (Module.finrank ℂ V) → ℂ, ∀ i, T (b i) = μ i • b i

def orthonormal_eigenbasis_normal : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V)
    (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V),
    _root_.D05.orthonormalFamily (F := ℂ) b →
      (∃ μ : Fin (Module.finrank ℂ V) → ℂ, ∀ i, T (b i) = μ i • b i) →
        _root_.D05.normalOperator T

/-- The complete equivalence, including the empty basis when V = 0. -/
def complex_spectral : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    (∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
      _root_.D05.orthonormalFamily (F := ℂ) b ∧
        ∃ μ : Fin (Module.finrank ℂ V) → ℂ, ∀ i, T (b i) = μ i • b i) ↔
      _root_.D05.normalOperator T

end Specs.D05.M13.ComplexSpectral
