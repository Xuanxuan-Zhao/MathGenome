import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M09.Diagonalizable

/-!
Independent specifications for K05.09.distinct_roots, paper.tex:1296–1297.
The hypothesis lists `dim V` distinct roots in the original field, with no
separate splitting, characteristic, or positive-dimension assumption.
The identity example includes both repeated-root divisibility and failure of
the sufficient condition. The characteristic polynomial and diagonalizability
are the canonical objects of the prerequisite specifications.
-/

namespace Specs.D05.M09.DistinctRoots

noncomputable section

/-- The roots can be realized, in their given order, by an eigenbasis. -/
def eigenbasis_of_distinct_roots : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V)
    (μ : Fin (Module.finrank K V) → K),
    Function.Injective μ →
    (∀ i, (Specs.D05.M08.Charpoly.charpoly_value T).eval (μ i) = 0) →
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ i, T.HasEigenvector (μ i) (b i)

/-- Having `dim V` distinct roots over K suffices for diagonalization over K. -/
def distinct_roots_diagonalizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (∃ μ : Fin (Module.finrank K V) → K,
      Function.Injective μ ∧
        ∀ i, (Specs.D05.M08.Charpoly.charpoly_value T).eval (μ i) = 0) →
    Diagonalizable.diagonalizable_value K V T

/-- The identity is diagonalizable in every finite dimension. -/
def identity_diagonalizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    Diagonalizable.diagonalizable_value K V (LinearMap.id : Module.End K V)

/-- In dimension at least two the identity disproves necessity. The square
divisor states that 1 is a repeated root, including in positive characteristic. -/
def identity_counterexample : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], 2 ≤ Module.finrank K V →
    Diagonalizable.diagonalizable_value K V (LinearMap.id : Module.End K V) ∧
    Specs.D05.M08.Charpoly.charpoly_value (LinearMap.id : Module.End K V) =
      (Polynomial.X - Polynomial.C (1 : K)) ^ Module.finrank K V ∧
    (Polynomial.X - Polynomial.C (1 : K)) ^ 2 ∣
      Specs.D05.M08.Charpoly.charpoly_value (LinearMap.id : Module.End K V) ∧
    ¬ (∃ μ : Fin (Module.finrank K V) → K,
      Function.Injective μ ∧
        ∀ i, (Specs.D05.M08.Charpoly.charpoly_value (LinearMap.id : Module.End K V)).eval (μ i) = 0)

end

end Specs.D05.M09.DistinctRoots
