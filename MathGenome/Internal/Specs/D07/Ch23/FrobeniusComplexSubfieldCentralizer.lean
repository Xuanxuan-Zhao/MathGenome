import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Algebraic.Basic

/-!
Independent statements for the first two paragraphs of Frobenius's proof,
paper.tex:7485–7501. `Algebra ℝ D` specifies a central unital embedding
(the map is injective because ℝ is a field and D is nonzero).
No finite-dimensionality or commutativity of D is imposed.
-/

universe u

namespace Specs.D07.Ch23.FrobeniusComplexSubfieldCentralizer

/-- Every element has its genuine monic irreducible real minimal polynomial,
which annihilates it and has degree at most two. -/
def RealMinimalPolynomialDegree : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    (∀ x : D, IsAlgebraic ℝ x) → ∀ x : D,
    (minpoly ℝ x).Monic ∧ Irreducible (minpoly ℝ x) ∧
    Polynomial.aeval x (minpoly ℝ x) = 0 ∧ (minpoly ℝ x).natDegree ≤ 2

/-- A nonscalar element forces a copy of the ordinary complex field inside D,
with ordinary I mapped to an element squaring to -1. -/
def ComplexEmbeddingExists : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    (∀ x : D, IsAlgebraic ℝ x) →
    (∃ x : D, x ∉ Set.range (algebraMap ℝ D)) →
    ∃ (i : D) (φ : ℂ →ₐ[ℝ] D),
      i ^ 2 = -1 ∧ φ Complex.I = i ∧ Function.Injective φ

/-- The centralizer of the selected imaginary unit is exactly the embedded
complex field. The embedding is allowed to be any real algebra homomorphism. -/
def ComplexCentralizerImage : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    (∀ x : D, IsAlgebraic ℝ x) →
    ∀ (φ : ℂ →ₐ[ℝ] D) (y : D),
      y * φ Complex.I = φ Complex.I * y ↔ y ∈ Set.range φ

end Specs.D07.Ch23.FrobeniusComplexSubfieldCentralizer
