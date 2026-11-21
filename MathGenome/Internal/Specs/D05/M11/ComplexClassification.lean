import MathGenome.Internal.Specs.D05.M11.DiagonalCongruence
import MathGenome.Internal.Specs.D05.M11.Nondegenerate
import MathGenome.Internal.Specs.D05.Foundations.ComplexRoots
import Mathlib.LinearAlgebra.Matrix.Block

/-! K05.11.complex_classification, paper.tex:1710–1711.
These are complex bilinear forms: neither slot involves conjugation.
The normal form has an identity block of size equal to the first-slot-map rank,
and a zero block of the remaining dimension. No nondegeneracy or positive
ambient-dimension assumption is made. -/
namespace Specs.D05.M11.ComplexClassification

open Module Matrix
open Specs.D05.M11.Nondegenerate

/-- Ordered block basis, with all nonzero directions first. -/
def normal_form : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V), B.IsSymm →
    ∃ b : Basis (Fin (rank_value B) ⊕ Fin (finrank ℂ V - rank_value B)) ℂ V,
      B.toMatrix b = Matrix.fromBlocks 1 0 0 0

/-- Rank is invariant under the actual bilinear matrix congruence. -/
def rank_congruence : Prop :=
  ∀ {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℂ), IsUnit P →
    (Pᵀ * A * P).rank = A.rank

/-- On a fixed finite-dimensional space, an invertible change in both input
slots exists exactly when the two symmetric forms have the same rank. -/
def congruent_iff_rank : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B C : LinearMap.BilinForm ℂ V), B.IsSymm → C.IsSymm →
    ((∃ e : V ≃ₗ[ℂ] V, ∀ x y, C (e x) (e y) = B x y) ↔
      rank_value B = rank_value C)

/-- The corresponding classification stated directly for square symmetric
matrices of the same shape, using transpose rather than conjugate transpose. -/
def matrix_congruent_iff_rank : Prop :=
  ∀ {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ), Aᵀ = A → Cᵀ = C →
    ((∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P ∧ Pᵀ * A * P = C) ↔
      A.rank = C.rank)

end Specs.D05.M11.ComplexClassification
