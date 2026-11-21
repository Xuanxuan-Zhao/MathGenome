import Mathlib.Algebra.Lie.Classical
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-! LA-D08, even orthogonal case (source lines 1930–1983).
The matrix indices are the ordered hyperbolic coordinates, first + and then −.
The parameter space is all diagonal Cartan coordinates, not a chosen regular subset.
Root spaces below are subspaces of the ambient matrices, with the defining
orthogonal equation included. Thus no semisimplicity certificate is assumed.
-/
namespace Specs.LieAlgebrasAndRepresentations.ClassicalRootsD
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
abbrev Idx (n : ℕ) := Fin n ⊕ Fin n
abbrev Mat (n : ℕ) := Matrix (Idx n) (Idx n) ℂ
abbrev Params (n : ℕ) := Fin n → ℂ
abbrev Dual (n : ℕ) := Module.Dual ℂ (Params n)
abbrev algebra (n : ℕ) := LieAlgebra.Orthogonal.typeD (Fin n) ℂ

def epsilon (n : ℕ) (i : Fin n) : Dual n := LinearMap.proj i

def diagonal (n : ℕ) (t : Params n) : Mat n :=
  Matrix.diagonal (Sum.elim t (-t))

def aVector (n : ℕ) (i j : Fin n) : Mat n :=
  Matrix.single (Sum.inl i) (Sum.inl j) 1 -
  Matrix.single (Sum.inr j) (Sum.inr i) 1

def bVector (n : ℕ) (i j : Fin n) : Mat n :=
  Matrix.single (Sum.inl i) (Sum.inr j) 1 -
  Matrix.single (Sum.inl j) (Sum.inr i) 1

def cVector (n : ℕ) (i j : Fin n) : Mat n :=
  Matrix.single (Sum.inr i) (Sum.inl j) 1 -
  Matrix.single (Sum.inr j) (Sum.inl i) 1

def rowWeight {n : ℕ} (a : Idx n) : Dual n := Sum.elim (epsilon n) (fun i => -epsilon n i) a

/-- The literal simultaneous eigenspace for every diagonal Cartan element. -/
def weightSpace (n : ℕ) (α : Dual n) : Submodule ℂ (Mat n) where
  carrier := {X | X ∈ algebra n ∧ ∀ t, diagonal n t * X - X * diagonal n t = α t • X}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    refine ⟨(algebra n).add_mem hX.1 hY.1, fun t => ?_⟩
    simp only [mul_add, add_mul, smul_add]
    rw [show diagonal n t * X + diagonal n t * Y - (X * diagonal n t + Y * diagonal n t) =
      (diagonal n t * X - X * diagonal n t) + (diagonal n t * Y - Y * diagonal n t) by abel]
    rw [hX.2, hY.2]
  smul_mem' := by
    intro a X hX
    refine ⟨(algebra n).smul_mem a hX.1, fun t => ?_⟩
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hX.2]
    exact smul_comm a (α t) X

def roots (n : ℕ) : Set (Dual n) := {α | α ≠ 0 ∧ weightSpace n α ≠ ⊥}

/-- Zero Cartan summand followed by the nonzero root summands. -/
def summand (n : ℕ) : Option (roots n) → Submodule ℂ (Mat n)
  | none => weightSpace n 0
  | some α => weightSpace n α.val

/-- Matrices displayed in the root-space calculation, including diagonal A-generators
when the weight is zero. Degenerate skew generators with i=j are just zero. -/
def generators (n : ℕ) (α : Dual n) : Set (Mat n) :=
  {X | ∃ i j, α = epsilon n i - epsilon n j ∧ X = aVector n i j} ∪
  {X | ∃ i j, α = epsilon n i + epsilon n j ∧ X = bVector n i j} ∪
  {X | ∃ i j, α = -(epsilon n i + epsilon n j) ∧ X = cVector n i j}

/-- Euclidean coordinates (used with the complex bilinear extension of the dot product). -/
def coordinate (n : ℕ) (i : Fin n) : Params n := Pi.single i 1

def dot (n : ℕ) (a b : Params n) : ℂ := ∑ i, a i * b i

noncomputable def coroot (n : ℕ) (a : Params n) : Mat n := diagonal n ((2 / dot n a a) • a)

/-! Independent expected theorem types. -/

def mem_algebra_type : Prop :=
  ∀ {n : ℕ} (X : Mat n),
  X ∈ algebra n ↔
    (∀ i j, X (Sum.inr i) (Sum.inr j) = -X (Sum.inl j) (Sum.inl i)) ∧
    (∀ i j, X (Sum.inl i) (Sum.inr j) = -X (Sum.inl j) (Sum.inr i)) ∧
    (∀ i j, X (Sum.inr i) (Sum.inl j) = -X (Sum.inr j) (Sum.inl i))

def diagonal_mem_type : Prop :=
  ∀ {n : ℕ} (t : Params n),
  diagonal n t ∈ algebra n

def aVector_mem_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  aVector n i j ∈ algebra n

def bVector_mem_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  bVector n i j ∈ algebra n

def cVector_mem_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  cVector n i j ∈ algebra n

def skew_diagonal_type : Prop :=
  ∀ {n : ℕ} {X : Mat n} (hX : X ∈ algebra n) (i : Fin n),
  X (Sum.inl i) (Sum.inr i) = 0 ∧ X (Sum.inr i) (Sum.inl i) = 0

def rowWeight_apply_type : Prop :=
  ∀ {n : ℕ} (a : Idx n) (t : Params n),
  rowWeight a t = Sum.elim t (-t) a

def diagonal_bracket_entry_type : Prop :=
  ∀ {n : ℕ} (t : Params n) (X : Mat n) (a b : Idx n),
  (diagonal n t * X - X * diagonal n t) a b =
      (rowWeight a t - rowWeight b t) * X a b

def mem_weightSpace_type : Prop :=
  ∀ {n : ℕ} (α : Dual n) (X : Mat n),
  X ∈ weightSpace n α ↔ X ∈ algebra n ∧
      ∀ a b, X a b ≠ 0 → α = rowWeight a - rowWeight b

def aVector_weight_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  aVector n i j ∈ weightSpace n (epsilon n i - epsilon n j)

def bVector_weight_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  bVector n i j ∈ weightSpace n (epsilon n i + epsilon n j)

def cVector_weight_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  cVector n i j ∈ weightSpace n (-(epsilon n i + epsilon n j))

def epsilon_coordinate_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  epsilon n i (coordinate n j) = if j = i then 1 else 0

def epsilon_injective_type : Prop :=
  ∀ {n : ℕ},
  Function.Injective (epsilon n)

def epsilon_ne_neg_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  epsilon n i ≠ -epsilon n j

def rowWeight_injective_type : Prop :=
  ∀ {n : ℕ},
  Function.Injective (@rowWeight n)

def diagonal_injective_type : Prop :=
  ∀ {n : ℕ},
  Function.Injective (diagonal n)

def zero_space_type : Prop :=
  ∀ {n : ℕ} (X : Mat n),
  X ∈ weightSpace n 0 ↔ ∃ t, X = diagonal n t

def difference_ne_zero_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  epsilon n i - epsilon n j ≠ 0

def sum_ne_zero_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  epsilon n i + epsilon n j ≠ 0

def aVector_ne_zero_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  aVector n i j ≠ 0

def bVector_ne_zero_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  bVector n i j ≠ 0

def cVector_ne_zero_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  cVector n i j ≠ 0

def roots_iff_type : Prop :=
  ∀ {n : ℕ} (α : Dual n),
  α ∈ roots n ↔
    ∃ i j : Fin n, i ≠ j ∧
      (α = epsilon n i - epsilon n j ∨ α = epsilon n i + epsilon n j ∨
       α = -(epsilon n i + epsilon n j))

def expansion_type : Prop :=
  ∀ {n : ℕ} (X : Mat n) (hX : X ∈ algebra n),
  X = (∑ i, ∑ j, X (Sum.inl i) (Sum.inl j) • aVector n i j) +
      (1 / 2 : ℂ) • (∑ i, ∑ j, X (Sum.inl i) (Sum.inr j) • bVector n i j) +
      (1 / 2 : ℂ) • (∑ i, ∑ j, X (Sum.inr i) (Sum.inl j) • cVector n i j)

def weightSpace_eq_span_type : Prop :=
  ∀ {n : ℕ} (α : Dual n),
  weightSpace n α = Submodule.span ℂ (generators n α)

def difference_space_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  weightSpace n (epsilon n i - epsilon n j) = Submodule.span ℂ {aVector n i j}

def bVector_self_type : Prop :=
  ∀ {n : ℕ} (i : Fin n),
  bVector n i i = 0

def cVector_self_type : Prop :=
  ∀ {n : ℕ} (i : Fin n),
  cVector n i i = 0

def bVector_swap_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  bVector n j i = -bVector n i j

def cVector_swap_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  cVector n j i = -cVector n i j

def sum_space_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  weightSpace n (epsilon n i + epsilon n j) = Submodule.span ℂ {bVector n i j}

def neg_sum_space_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  weightSpace n (-(epsilon n i + epsilon n j)) = Submodule.span ℂ {cVector n i j}

def iSup_weightSpace_type : Prop :=
  ∀ {n : ℕ},
  (⨆ α : Dual n, weightSpace n α) = (algebra n).toSubmodule

def weightSpace_independent_type : Prop :=
  ∀ {n : ℕ},
  iSupIndep (weightSpace n)

def root_decomposition_type : Prop :=
  ∀ {n : ℕ},
  iSupIndep (summand n) ∧
    (⨆ a : Option (roots n), summand n a) = (algebra n).toSubmodule

def normalizer_is_diagonal_type : Prop :=
  ∀ {n : ℕ} (X : Mat n) (hX : X ∈ algebra n),
  (∀ t, ∃ u, diagonal n t * X - X * diagonal n t = diagonal n u) ↔
      ∃ t, X = diagonal n t

def root_space_finrank_type : Prop :=
  ∀ {n : ℕ} (α : Dual n) (ha : α ∈ roots n),
  Module.finrank ℂ (weightSpace n α) = 1

def roots_ordered_type : Prop :=
  ∀ {n : ℕ} (α : Dual n),
  α ∈ roots n ↔
    ∃ i j : Fin n, i < j ∧
      (α = epsilon n i - epsilon n j ∨ α = -(epsilon n i - epsilon n j) ∨
       α = epsilon n i + epsilon n j ∨ α = -(epsilon n i + epsilon n j))

def dot_coordinate_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n),
  dot n (coordinate n i) (coordinate n j) = if i = j then 1 else 0

def root_lengths_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  dot n (coordinate n i - coordinate n j) (coordinate n i - coordinate n j) = 2 ∧
    dot n (coordinate n i + coordinate n j) (coordinate n i + coordinate n j) = 2

def coroots_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  coroot n (coordinate n i - coordinate n j) = diagonal n (coordinate n i - coordinate n j) ∧
    coroot n (coordinate n i + coordinate n j) = diagonal n (coordinate n i + coordinate n j)

def negative_coroot_type : Prop :=
  ∀ {n : ℕ} (a : Params n),
  coroot n (-a) = -coroot n a

def diagonal_add_type : Prop :=
  ∀ {n : ℕ} (t u : Params n),
  diagonal n (t + u) = diagonal n t + diagonal n u

def diagonal_sub_type : Prop :=
  ∀ {n : ℕ} (t u : Params n),
  diagonal n (t - u) = diagonal n t - diagonal n u

def diagonal_coordinate_type : Prop :=
  ∀ {n : ℕ} (i : Fin n),
  diagonal n (coordinate n i) = aVector n i i

def difference_bracket_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  aVector n i j * aVector n j i - aVector n j i * aVector n i j =
      coroot n (coordinate n i - coordinate n j)

def sum_bracket_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  bVector n i j * (-cVector n i j) - (-cVector n i j) * bVector n i j =
      coroot n (coordinate n i + coordinate n j)

def weight_dot_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (t : Params n),
  (epsilon n i - epsilon n j) t = dot n (coordinate n i - coordinate n j) t ∧
    (epsilon n i + epsilon n j) t = dot n (coordinate n i + coordinate n j) t

def neg_sum_bracket_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  cVector n i j * (-bVector n i j) - (-bVector n i j) * cVector n i j =
      coroot n (-(coordinate n i + coordinate n j))

def difference_triple_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  let e := aVector n i j
    let f := aVector n j i
    let h := coroot n (coordinate n i - coordinate n j)
    e * f - f * e = h ∧ h * e - e * h = (2 : ℂ) • e ∧
      h * f - f * h = (-2 : ℂ) • f

def sum_triple_type : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j),
  let e := bVector n i j
    let f := -cVector n i j
    let h := coroot n (coordinate n i + coordinate n j)
    e * f - f * e = h ∧ h * e - e * h = (2 : ℂ) • e ∧
      h * f - f * h = (-2 : ℂ) • f

def d1_scalar_type : Prop :=
  ∀ (X : algebra 1),
  (X : Mat 1) = (X : Mat 1) (Sum.inl 0) (Sum.inl 0) • aVector 1 0 0

def d1_abelian_type : Prop :=
  IsLieAbelian (algebra 1)

def d1_not_semisimple_type : Prop :=
  ¬ Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ (algebra 1)

end Specs.LieAlgebrasAndRepresentations.ClassicalRootsD
