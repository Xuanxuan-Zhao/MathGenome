import MathGenome.Internal.Specs.D05.M02.BasisExtension
import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M09.Eigenspace
import MathGenome.Internal.Specs.D05.M05.TriangularBlock
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Independent specification of K05.09.multiplicities, paper.tex:1283–1286.
All multiplicities and all matrix entries are over the named field. There is no
splitting assumption. Sum indices put the eigenspace basis before the added
vectors, and allow either block to have size zero. -/

noncomputable section
namespace Specs.D05.M09.Multiplicities

universe u v

def algebraicMultiplicity_type :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → Module.End K V → K → ℕ

def algebraicMultiplicity_value : algebraicMultiplicity_type.{u,v} :=
  fun T μ => (Specs.D05.M08.Charpoly.charpoly_value T).rootMultiplicity μ

def geometricMultiplicity_type :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → Module.End K V → K → ℕ

def geometricMultiplicity_value : geometricMultiplicity_type.{u,v} :=
  fun {K} {_} _ _ _ _ T μ => Module.finrank K (T.eigenspace μ)

/-- The root multiplicity really is the exponent of the linear factor:
its powers divide the nonzero characteristic polynomial precisely up to it. -/
def exponent_characterization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) (μ : K) (k : ℕ),
    k ≤ algebraicMultiplicity_value T μ ↔
      (Polynomial.X - Polynomial.C μ) ^ k ∣ Specs.D05.M08.Charpoly.charpoly_value T

/-- Every chosen eigenspace basis extends to a basis with the displayed matrix
and characteristic polynomial factorization. The matrix C and its determinant
factor are over K and need not have any roots in K. -/
def basis_block_factorization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) (μ : K)
    (e : Module.Basis (Fin (Module.finrank K (T.eigenspace μ))) K (T.eigenspace μ)),
    ∃ (s : ℕ)
      (b : Module.Basis (Fin (Module.finrank K (T.eigenspace μ)) ⊕ Fin s) K V)
      (B : Matrix (Fin (Module.finrank K (T.eigenspace μ))) (Fin s) K)
      (C : Matrix (Fin s) (Fin s) K),
      (∀ i, b (Sum.inl i) = (e i : V)) ∧
      LinearMap.toMatrix b b T = Matrix.fromBlocks (μ • 1) B 0 C ∧
      Specs.D05.M08.Charpoly.charpoly_value T =
        (Polynomial.X - Polynomial.C μ) ^ Module.finrank K (T.eigenspace μ) *
          D05.M05.determinant
          (Matrix.scalar (Fin s) (Polynomial.X : Polynomial K) - C.map Polynomial.C)

def geometric_le_algebraic : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) (μ : K),
    geometricMultiplicity_value T μ ≤ algebraicMultiplicity_value T μ

def geometric_pos_of_hasEigenvalue : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) (μ : K),
    T.HasEigenvalue μ → 1 ≤ geometricMultiplicity_value T μ

end Specs.D05.M09.Multiplicities
