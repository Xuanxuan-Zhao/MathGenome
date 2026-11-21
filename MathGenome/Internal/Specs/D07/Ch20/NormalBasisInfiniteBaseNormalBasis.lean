import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! Independent types for the infinite-base part of K07.20.normal_basis,
`paper.tex:5975–5988`. Coefficients of every determinant polynomial are in
L. Evaluation points, and only evaluation points, are required to lie in K.
The group law is composition: the determinant uses σ * τ, without an inverse.
-/

universe u v w
noncomputable section

namespace Specs.D07.Ch20.NormalBasisInfiniteBaseNormalBasis

open MvPolynomial
open scoped Classical

/-- The source's group determinant, with one independent variable per group element. -/
def groupDeterminant (G : Type w) [Group G] [Fintype G] [DecidableEq G]
    (L : Type v) [Field L] : MvPolynomial G L :=
  Matrix.det (Matrix.of fun σ τ : G => (X (σ * τ) : MvPolynomial G L))

/-- The embedding-coordinate matrix for a basis indexed by the Galois group. -/
def embeddingMatrix {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (L ≃ₐ[K] L) K L) : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L :=
  Matrix.of fun σ j => σ (b j)

/-- Substitution of linear forms, with the original coefficient field fixed. -/
def coordinateSubstitution {L : Type v} [Field L] {ι : Type w} [Fintype ι]
    (A : Matrix ι ι L) : MvPolynomial ι L →ₐ[L] MvPolynomial ι L :=
  aeval fun i => ∑ j, C (A i j) * X j

def GroupDeterminantNonzero : Prop :=
  ∀ (G : Type w) [Group G] [Fintype G] [DecidableEq G]
    (L : Type v) [Field L], groupDeterminant G L ≠ 0

def EmbeddingMatrixNonsingular : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (b : Module.Basis (L ≃ₐ[K] L) K L), (embeddingMatrix b).det ≠ 0

/-- Invertibility is an actual algebra equivalence with the specified action
on all polynomials, rather than a certificate assumed in a later theorem. -/
def EmbeddingSubstitutionInvertible : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (b : Module.Basis (L ≃ₐ[K] L) K L),
    ∃ e : MvPolynomial (L ≃ₐ[K] L) L ≃ₐ[L] MvPolynomial (L ≃ₐ[K] L) L,
      ∀ p, e p = coordinateSubstitution (embeddingMatrix b) p

def SubstitutedDeterminantNonzero : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (b : Module.Basis (L ≃ₐ[K] L) K L),
    coordinateSubstitution (embeddingMatrix b) (groupDeterminant (L ≃ₐ[K] L) L) ≠ 0

/-- The polynomial has coefficients in L, which need not equal K. No
separability, normality, or finite degree is needed for this auxiliary fact. -/
def PolynomialNonvanishing : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Infinite K]
    (ι : Type w) (p : MvPolynomial ι L), p ≠ 0 →
      ∃ x : ι → K, eval (algebraMap K L ∘ x) p ≠ 0

/-- Every starting basis admits K-coordinates at which the substituted group
determinant is nonzero, and the constructed sum has its conjugates as a basis. -/
def NormalBasisFromCoordinates : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Infinite K]
    (b : Module.Basis (L ≃ₐ[K] L) K L),
    ∃ x : (L ≃ₐ[K] L) → K,
      eval (algebraMap K L ∘ x)
        (coordinateSubstitution (embeddingMatrix b) (groupDeterminant (L ≃ₐ[K] L) L)) ≠ 0 ∧
      ∃ B : Module.Basis (L ≃ₐ[K] L) K L,
        ∀ σ, B σ = σ (∑ j, x j • b j)

def NormalBasisExists : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Infinite K],
    ∃ a : L, ∃ B : Module.Basis (L ≃ₐ[K] L) K L, ∀ σ, B σ = σ a

end Specs.D07.Ch20.NormalBasisInfiniteBaseNormalBasis
