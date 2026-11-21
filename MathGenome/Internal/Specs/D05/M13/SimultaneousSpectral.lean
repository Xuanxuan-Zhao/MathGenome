import MathGenome.Internal.Specs.D05.M13.Normal
import MathGenome.Internal.Specs.D05.M12.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent statements for K05.13.simultaneous_spectral, paper.tex:2284–2294.
Families have an arbitrary index type, with no finiteness or nonemptiness
assumption. The basis is indexed by `Fin (finrank F V)`, including dimension
zero. Orthonormality uses the canonical first-slot-linear convention.
The last two statements cover the real normal, real diagonalizable extension.
Here diagonalizability is expressed by an actual algebraic eigenbasis.
The joint-projection/algebra supplement has separate planned ownership. -/

namespace Specs.D05.M13.SimultaneousSpectral
universe u v

def real_common_orthonormal_eigenbasis : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type v} (T : ι → Module.End ℝ V),
    (∀ i, _root_.D05.selfAdjoint (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      _root_.D05.orthonormalFamily (F := ℝ) b ∧
      ∃ μ : ι → Fin (Module.finrank ℝ V) → ℝ,
        ∀ i k, T i (b k) = μ i k • b k

def complex_common_orthonormal_eigenbasis : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {ι : Type v} (T : ι → Module.End ℂ V),
    (∀ i, _root_.D05.normalOperator (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
      _root_.D05.orthonormalFamily (F := ℂ) b ∧
      ∃ μ : ι → Fin (Module.finrank ℂ V) → ℂ,
        ∀ i k, T i (b k) = μ i k • b k

def real_normal_diagonalizable_selfAdjoint : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : Module.End ℝ V),
    _root_.D05.normalOperator T →
    (∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∃ μ : Fin (Module.finrank ℝ V) → ℝ, ∀ k, T (b k) = μ k • b k) →
    _root_.D05.selfAdjoint T

def real_normal_diagonalizable_common_basis : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type v} (T : ι → Module.End ℝ V),
    (∀ i, _root_.D05.normalOperator (T i)) →
    (∀ i, ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∃ μ : Fin (Module.finrank ℝ V) → ℝ, ∀ k, T i (b k) = μ k • b k) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      _root_.D05.orthonormalFamily (F := ℝ) b ∧
      ∃ μ : ι → Fin (Module.finrank ℝ V) → ℝ,
        ∀ i k, T i (b k) = μ i k • b k

end Specs.D05.M13.SimultaneousSpectral
