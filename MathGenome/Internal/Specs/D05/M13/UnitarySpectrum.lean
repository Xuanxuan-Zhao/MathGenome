import MathGenome.Internal.Specs.D05.M13.ComplexSpectral
import MathGenome.Internal.Specs.D05.M13.Unitary
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Independent statements for paper.tex:2313–2320. The Cayley transform
supplement is separately allocated to `13.unitary_spectrum.cayley`.
Eigenvalues mean scalars admitting a nonzero eigenvector. In ℂ, vanishing
imaginary part expresses exactly membership in ℝ. All dimensions, including
zero, are permitted; no chosen eigenbasis is a hypothesis. -/

noncomputable section

namespace Specs.D05.M13.UnitarySpectrum

open Module.End

universe u

def selfAdjoint_iff_real_eigenvalues : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    _root_.D05.normalOperator T →
      (_root_.D05.selfAdjoint T ↔ ∀ μ : ℂ, T.HasEigenvalue μ → μ.im = 0)

def unitary_iff_norm_eigenvalues : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    _root_.D05.normalOperator T →
      (_root_.D05.IsUnitaryMap T ↔ ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ = 1)

/-- The specific Jordan matrix in the text witnesses failure of both tests
without normality. Its columns fail orthonormality, as witnessed by their
nonzero inner product. The same matrix has only eigenvalue 1. -/
def jordan_counterexample : Prop :=
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]
  let J : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) := Matrix.toEuclideanLin A
  (∀ μ : ℂ, J.HasEigenvalue μ ↔ μ = 1) ∧
    (∀ μ : ℂ, J.HasEigenvalue μ → μ.im = 0 ∧ ‖μ‖ = 1) ∧
    A.transpose ≠ A ∧
    ¬ _root_.D05.selfAdjoint J ∧
    ¬ _root_.D05.IsUnitaryMap J ∧
    inner ℂ (WithLp.toLp 2 (fun i => A i 0) : EuclideanSpace ℂ (Fin 2))
      (WithLp.toLp 2 (fun i => A i 1)) ≠ 0

end Specs.D05.M13.UnitarySpectrum
