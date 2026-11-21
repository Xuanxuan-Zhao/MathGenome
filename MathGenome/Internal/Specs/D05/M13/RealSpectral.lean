import MathGenome.Internal.Specs.D05.M13.SelfAdjoint
import MathGenome.Internal.Specs.D05.M12.Orthonormal

/-!
Independent statements for K05.13.real_spectral, paper.tex:2217–2225.
The basis is an actual algebraic basis with the shared first-slot-linear
orthonormality predicate. Eigenvalues are real. No nonzero-space or
completeness hypothesis is imposed; `Fin (finrank ℝ V)` is empty in dimension zero.
-/

namespace Specs.D05.M13.RealSpectral

universe v w

/-- Sufficiency, with all eigenvalues and eigenvector equations supplied. -/
def exists_orthonormal_eigenbasis : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : Module.End ℝ V),
    _root_.D05.selfAdjoint T →
      ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
        _root_.D05.orthonormalFamily (F := ℝ) b ∧
          ∃ μ : Fin (Module.finrank ℝ V) → ℝ, ∀ i, T (b i) = μ i • b i

/-- Necessity for any finite indexing type, with no prescribed ordering. -/
def selfAdjoint_of_orthonormal_eigenbasis : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type w} [Fintype ι]
    (T : Module.End ℝ V) (b : Module.Basis ι ℝ V),
    _root_.D05.orthonormalFamily (F := ℝ) b →
      (∀ i, ∃ μ : ℝ, T (b i) = μ • b i) → _root_.D05.selfAdjoint T

/-- The real spectral theorem, in the source's iff direction. -/
def real_spectral : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : Module.End ℝ V),
    (∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      _root_.D05.orthonormalFamily (F := ℝ) b ∧
        ∀ i, ∃ μ : ℝ, T (b i) = μ • b i) ↔ _root_.D05.selfAdjoint T

end Specs.D05.M13.RealSpectral
