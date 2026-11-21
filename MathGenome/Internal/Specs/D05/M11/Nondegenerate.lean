import MathGenome.Internal.Specs.D05.M11.Radicals
import MathGenome.Internal.Specs.D05.M03.RankNullity
import MathGenome.Internal.Specs.D05.M04.RankBridge
import MathGenome.Internal.Specs.D05.M04.InverseMatrix
import Mathlib.LinearAlgebra.Dual.Basis

/-! K05.11.nondegenerate, paper.tex:1652–1658. Rank is the dimension of the
image of the first-slot map into the algebraic dual. No symmetry, positivity,
characteristic, or positive-dimension hypothesis is imposed. The separately
allocated one-sided-complement supplement is not part of these statements.
For unequal pairing spaces, left and right separation are distinct predicates.
-/
namespace Specs.D05.M11.Nondegenerate

open Module Matrix
open Specs.D05.M11.Radicals Specs.D05.M11.FormMatrix

universe u v

def rank_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → LinearMap.BilinForm K V → ℕ

noncomputable def rank_value : rank_type.{u, v} :=
  fun {K} {V} _ _ _ _ B => M03.Image.rank_value K V (Module.Dual K V) B

def nondegenerate_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    LinearMap.BilinForm K V → Prop

def nondegenerate_value : nondegenerate_type.{u, v} := fun B => LinearMap.Nondegenerate B

/-- The first-slot map has the transpose form matrix in the primal/dual bases. -/
def toDual_matrix : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    LinearMap.toMatrix b b.dualBasis B = (formMatrix_value b B)ᵀ

def rank_eq_transpose_rank : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Basis (Fin n) K V)
    (B : LinearMap.BilinForm K V), rank_value B = (formMatrix_value b B)ᵀ.rank

def rank_eq_matrix_rank : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Basis (Fin n) K V)
    (B : LinearMap.BilinForm K V), rank_value B = (formMatrix_value b B).rank

def basis_independent_rank : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n m : ℕ}
    (b : Basis (Fin n) K V) (c : Basis (Fin m) K V) (B : LinearMap.BilinForm K V),
    (formMatrix_value b B).rank = (formMatrix_value c B).rank

def rank_flip : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V), rank_value B.flip = rank_value B

def rank_nullity_left : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    Module.finrank K V = Module.finrank K (leftRadical_value B) + rank_value B

def rank_nullity_right : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    Module.finrank K V = Module.finrank K (rightRadical_value B) + rank_value B

def rank_eq_sub_left : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    rank_value B = Module.finrank K V - Module.finrank K (leftRadical_value B)

def rank_eq_sub_right : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    rank_value B = Module.finrank K V - Module.finrank K (rightRadical_value B)

def radical_dimensions : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    Module.finrank K (leftRadical_value B) = Module.finrank K (rightRadical_value B)

def rank_eq_dim_iff_left : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    rank_value B = Module.finrank K V ↔ leftRadical_value B = ⊥

def left_iff_right : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    leftRadical_value B = ⊥ ↔ rightRadical_value B = ⊥

/-- Square matrix criteria include the empty matrix. -/
def matrix_full_rank_iff_ker_bot : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    A.rank = n ↔ LinearMap.ker A.mulVecLin = ⊥

def matrix_ker_bot_iff_isUnit : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    LinearMap.ker A.mulVecLin = ⊥ ↔ IsUnit A

/-- Explicitly connect the algebraic unit predicate with a two-sided inverse. -/
def matrix_isUnit_iff_inverse : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    IsUnit A ↔ ∃ C : Matrix (Fin n) (Fin n) K, C * A = 1 ∧ A * C = 1

def left_iff_matrix_isUnit : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    leftRadical_value B = ⊥ ↔ IsUnit (formMatrix_value b B)

/-- This definition uses both sides, so is also meaningful without finite dimension. -/
def nondegenerate_iff_radicals : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V),
    nondegenerate_value B ↔ leftRadical_value B = ⊥ ∧ rightRadical_value B = ⊥

def nondegenerate_iff_left : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    nondegenerate_value B ↔ leftRadical_value B = ⊥

def nondegenerate_iff_right : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    nondegenerate_value B ↔ rightRadical_value B = ⊥

def nondegenerate_iff_rank : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    nondegenerate_value B ↔ rank_value B = Module.finrank K V

def nondegenerate_iff_matrix : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    nondegenerate_value B ↔ IsUnit (formMatrix_value b B)

/-- Left and right separation for pairings have different source spaces. -/
def pairing_left_iff : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (B : V →ₗ[K] W →ₗ[K] K),
    B.SeparatingLeft ↔ LinearMap.ker B = ⊥

def pairing_right_iff : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (B : V →ₗ[K] W →ₗ[K] K),
    B.SeparatingRight ↔ LinearMap.ker B.flip = ⊥

/-- Equivalence for different finite spaces requires an explicit dimension equality. -/
def pairing_equal_dimensions : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (B : V →ₗ[K] W →ₗ[K] K), Module.finrank K V = Module.finrank K W →
    (B.SeparatingLeft ↔ B.SeparatingRight)

end Specs.D05.M11.Nondegenerate
