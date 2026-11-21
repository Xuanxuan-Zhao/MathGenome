import MathGenome.Internal.Specs.D05.M06.InvariantDecomposition
import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M08.Minpoly
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Content

/-!
Independent statements for K05.08.block_polynomials (paper.tex:1193–1198).
The summands are the actual subspaces of V, with the upstream unique-expression
predicate for an internal direct sum and the upstream restriction of T. Scalars
are an arbitrary field. Every formula includes the zero space and empty family.
The LCM is Mathlib's normalized polynomial LCM, whose monicity is proved below.
-/
noncomputable section

namespace Specs.D05.M08.BlockPolynomials

open scoped BigOperators
open Specs.D05.M06.DirectSum (UniqueDecomposition)
open Specs.D05.M06.Invariant (invariant_value restriction_value)
open Specs.D05.M08.Charpoly (charpoly_value)
open Specs.D05.M08.Minpoly (minimalPolynomial_value)
open Specs.D05.M08.Evaluation (evaluation_value)

/-- Concatenating arbitrary finite ordered bases gives a basis of V, and the
matrix in that actual basis has exactly the restriction matrices as blocks. -/
def block_diagonal_matrix : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (U : ι → Submodule K V) (hU : UniqueDecomposition U)
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T)
    (n : ι → ℕ) (b : ∀ i, Module.Basis (Fin (n i)) K (U i)),
    ∃ B : Module.Basis (Σ i, Fin (n i)) K V,
      (∀ i j, B ⟨i, j⟩ = (b i j : V)) ∧
      LinearMap.toMatrix B B T =
        Matrix.blockDiagonal' (fun i =>
          LinearMap.toMatrix (b i) (b i) (restriction_value K V (U i) T (hT i)))

/-- Product formula, with no splitting or characteristic restriction. -/
def charpoly_product : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (U : ι → Submodule K V) (hU : UniqueDecomposition U)
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T),
    charpoly_value T = ∏ i, charpoly_value (restriction_value K V (U i) T (hT i))

/-- Evaluation commutes with inclusion of an invariant subspace. This assertion
needs neither directness nor finite dimension. -/
def evaluation_on_summand : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : Module.End K V) (hT : invariant_value K V U T)
    (p : Polynomial K) (u : U),
    (evaluation_value K U (restriction_value K V U T hT) p u : V) =
      evaluation_value K V T p (u : V)

/-- An operator polynomial vanishes exactly when it vanishes on every block. -/
def evaluation_zero_iff : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V) (hU : UniqueDecomposition U)
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T) (p : Polynomial K),
    evaluation_value K V T p = 0 ↔
      ∀ i, evaluation_value K (U i) (restriction_value K V (U i) T (hT i)) p = 0

/-- Each restriction's minimal polynomial gives exactly its annihilators. -/
def annihilates_iff_all_divide : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (U : ι → Submodule K V) (hU : UniqueDecomposition U)
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T) (p : Polynomial K),
    evaluation_value K V T p = 0 ↔
      ∀ i, minimalPolynomial_value K (U i) (restriction_value K V (U i) T (hT i)) ∣ p

/-- Normalization is monic, including for the empty family. -/
def lcm_monic : Prop := by
  classical
  exact ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (U : ι → Submodule K V) (T : Module.End K V)
    (hT : ∀ i, invariant_value K V (U i) T),
    (Finset.univ.lcm fun i =>
      minimalPolynomial_value K (U i) (restriction_value K V (U i) T (hT i))).Monic

/-- The monic LCM has precisely the same multiples as the annihilator ideal. -/
def annihilates_iff_lcm_divides : Prop := by
  classical
  exact ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (U : ι → Submodule K V) (hU : UniqueDecomposition U)
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T) (p : Polynomial K),
    evaluation_value K V T p = 0 ↔
      (Finset.univ.lcm fun i =>
        minimalPolynomial_value K (U i) (restriction_value K V (U i) T (hT i))) ∣ p

/-- Equality of monic polynomials, not merely association or divisibility. -/
def minpoly_lcm : Prop := by
  classical
  exact ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (U : ι → Submodule K V) (hU : UniqueDecomposition U)
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T),
    minimalPolynomial_value K V T = Finset.univ.lcm fun i =>
      minimalPolynomial_value K (U i) (restriction_value K V (U i) T (hT i))

/-- In an empty decomposition both invariant polynomials and both empty
operations equal 1. No nonzero-vector-space assumption is used. -/
def empty_decomposition : Prop := by
  classical
  exact ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] [IsEmpty ι]
    (U : ι → Submodule K V) (hU : UniqueDecomposition U)
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T),
    charpoly_value T = 1 ∧ minimalPolynomial_value K V T = 1 ∧
      (∏ i, charpoly_value (restriction_value K V (U i) T (hT i))) = 1 ∧
      (Finset.univ.lcm fun i =>
        minimalPolynomial_value K (U i) (restriction_value K V (U i) T (hT i))) = 1

end Specs.D05.M08.BlockPolynomials
