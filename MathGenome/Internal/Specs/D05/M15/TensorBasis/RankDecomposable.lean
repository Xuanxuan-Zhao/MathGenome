import MathGenome.Internal.Specs.D05.M15.TensorBasis
import MathGenome.Internal.Specs.D05.M15.TensorDualHom
import MathGenome.Internal.Specs.D05.M07.Biddual
import MathGenome.Internal.Specs.D05.M04.RankBridge
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Statements for the rank-and-decomposable-tensors paragraph, paper.tex:2730–2733.
All duals and tensor products are algebraic. Every assertion about numerical rank
has both factors finite dimensional, over an arbitrary field, including zero spaces.
The canonical map is defined by evaluation, not by an assumed decomposition.
-/
namespace Specs.D05.M15.TensorBasis.RankDecomposable

open scoped TensorProduct

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Contract the first vector factor against an algebraic functional. -/
abbrev associatedMap : (V ⊗[K] W) →ₗ[K] (Module.Dual K V →ₗ[K] W) :=
  (TensorDualHom.phi K (Module.Dual K V) W).comp
    (TensorProduct.map (Module.Dual.eval K V) (LinearMap.id : W →ₗ[K] W))

/-- Numerical rank of the canonical map; no minimization is built into this definition. -/
noncomputable def tensorRank (z : V ⊗[K] W) : ℕ :=
  Module.finrank K (LinearMap.range (associatedMap z))

/-- The actual coefficient array in the product basis, with the first index a row. -/
noncomputable def coefficientMatrix {n m : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (z : V ⊗[K] W) : Matrix (Fin n) (Fin m) K :=
  fun i j => (e.tensorProduct f).repr z (i, j)

/-- Length r means an indexed sum of exactly r elementary tensors; repetitions
and zero factors are allowed. In particular length zero is the empty sum. -/
def HasLength (z : V ⊗[K] W) (r : ℕ) : Prop :=
  ∃ (v : Fin r → V) (w : Fin r → W), z = ∑ i, v i ⊗ₜ[K] w i

def associated_tmul : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (v : V) (w : W) (φ : Module.Dual K V),
    associatedMap (v ⊗ₜ[K] w) φ = φ v • w

def associated_sum : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (r : ℕ) (v : Fin r → V) (w : Fin r → W)
    (φ : Module.Dual K V),
    associatedMap (∑ i, v i ⊗ₜ[K] w i) φ = ∑ i, φ (v i) • w i

def matrix_formula : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    {n m : ℕ} (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (z : V ⊗[K] W),
    LinearMap.toMatrix e.dualBasis f (associatedMap z) = (coefficientMatrix e f z).transpose

def rank_matrix : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    {n m : ℕ} (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (z : V ⊗[K] W), tensorRank z = (coefficientMatrix e f z).rank

def range_containment : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (r : ℕ) (v : Fin r → V) (w : Fin r → W),
    LinearMap.range (associatedMap (∑ i, v i ⊗ₜ[K] w i)) ≤
      Submodule.span K (Set.range w)

def rank_bound : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W) (r : ℕ), HasLength z r → tensorRank z ≤ r

def minimal_independent : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W) (r : ℕ) (v : Fin r → V) (w : Fin r → W),
    z = ∑ i, v i ⊗ₜ[K] w i → r = tensorRank z →
    LinearIndependent K v ∧ LinearIndependent K w

def exists_minimal_expression : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W),
    ∃ (v : Fin (tensorRank z) → V) (w : Fin (tensorRank z) → W),
      z = ∑ i, v i ⊗ₜ[K] w i ∧ LinearIndependent K v ∧ LinearIndependent K w

/-- This asserts the minimum, rather than defining tensor rank to be that minimum. -/
def least_length : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W), IsLeast {r : ℕ | HasLength z r} (tensorRank z)

def rank_zero_iff : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W), tensorRank z = 0 ↔ z = 0

def decomposable_iff : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W), (∃ (v : V) (w : W), z = v ⊗ₜ[K] w) ↔ tensorRank z ≤ 1

end Specs.D05.M15.TensorBasis.RankDecomposable
