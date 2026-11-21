import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Directed.Foundations
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Independent statement of paper.tex W23 (749–791), using the original-arc
walk and path types from the shared foundation. The finite-support sums
below are finite sums: the implementation proves finiteness of the path
types without any extra assumption, and hence of all family types.
No acyclicity or cancellation certificate is assumed in these definitions.
-/

open scoped BigOperators

universe u v r

namespace FiniteCombinatorics.Directed.LGV

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable (G : Digraph V A)

/-- Sum over all vertex-simple paths, retaining original arc identities. -/
noncomputable def pathWeightSum {R : Type r} [CommRing R] (w : A → R) (x y : V) : R :=
  ∑ᶠ p : Spec.path G x y, Spec.weight w p.val

/-- The path matrix has source index first and target index second. -/
noncomputable def pathMatrix {R : Type r} [CommRing R] (w : A → R)
    {n : ℕ} (a b : Fin n → V) : Matrix (Fin n) (Fin n) R :=
  fun i j => pathWeightSum G w (a i) (b j)

/-- A family for a specified endpoint permutation; empty paths are included. -/
def Family {n : ℕ} (a b : Fin n → V) (σ : Equiv.Perm (Fin n)) :=
  ∀ i : Fin n, Spec.path G (a i) (b (σ i))

/-- Vertex disjointness counts both endpoints, also for a length-zero path. -/
def VertexDisjoint {n : ℕ} {a b : Fin n → V} {σ : Equiv.Perm (Fin n)}
    (P : Family G a b σ) : Prop :=
  ∀ i j, i ≠ j → List.Disjoint (Spec.vertices (P i).val) (Spec.vertices (P j).val)

/-- All arc weights in the family, with multiplicity. -/
noncomputable def familyWeight {R : Type r} [CommRing R] (w : A → R)
    {n : ℕ} {a b : Fin n → V} {σ : Equiv.Perm (Fin n)} (P : Family G a b σ) : R :=
  ∏ i, Spec.weight w (P i).val

/-- Signed sum over permutations and their vertex-disjoint families. -/
noncomputable def signedSum {R : Type r} [CommRing R] (w : A → R)
    {n : ℕ} (a b : Fin n → V) : R :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
    ∑ᶠ P : {P : Family G a b σ // VertexDisjoint G P}, familyWeight G w P.val

/-- Unsigned sum over the disjoint families for the identity matching. -/
noncomputable def unsignedSum {R : Type r} [CommRing R] (w : A → R)
    {n : ℕ} (a b : Fin n → V) : R :=
  ∑ᶠ P : {P : Family G a b 1 // VertexDisjoint G P}, familyWeight G w P.val

/-- Determinant expansion before intersecting families cancel. -/
noncomputable def allSignedSum {R : Type r} [CommRing R] (w : A → R)
    {n : ℕ} (a b : Fin n → V) : R :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
    ∑ᶠ P : Family G a b σ, familyWeight G w P

/-- The part removed by the sign-reversing tail-switch involution. -/
noncomputable def intersectingSignedSum {R : Type r} [CommRing R] (w : A → R)
    {n : ℕ} (a b : Fin n → V) : R :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
    ∑ᶠ P : {P : Family G a b σ // ¬ VertexDisjoint G P}, familyWeight G w P.val

end FiniteCombinatorics.Directed.LGV

set_option linter.unusedVariables false
namespace FiniteCombinatorics.Directed.LGVSpec

/-- The full signed identity; the two injective endpoint lists may overlap. -/
def lgv : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (hG : Spec.acyclic G) {R : Type r} [CommRing R]
  (w : A → R) {n : ℕ} (a b : Fin n → V)
  (ha : Function.Injective a) (hb : Function.Injective b),
  Matrix.det (LGV.pathMatrix G w a b) = LGV.signedSum G w a b

/-- The unsigned specialization, with precisely the endpoint compatibility condition. -/
def lgv_unsigned : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (hG : Spec.acyclic G) {R : Type r} [CommRing R]
  (w : A → R) {n : ℕ} (a b : Fin n → V)
  (ha : Function.Injective a) (hb : Function.Injective b)
  (hmatch : ∀ (σ : Equiv.Perm (Fin n)) (P : LGV.Family G a b σ),
    LGV.VertexDisjoint G P → σ = 1),
  Matrix.det (LGV.pathMatrix G w a b) = LGV.unsignedSum G w a b

/-- Path types are finite without a DAG assumption (paths are vertex-simple). -/
def finitePath : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (x y : V), Finite (Spec.path G x y)

/-- Expansion of determinant and of each product of path sums. -/
def determinant_expansion : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) {R : Type r} [CommRing R] (w : A → R)
  {n : ℕ} (a b : Fin n → V),
  Matrix.det (LGV.pathMatrix G w a b) = LGV.allSignedSum G w a b

/-- Empty determinant and empty disjoint family have weight one. -/
def empty_case : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) {R : Type r} [CommRing R] (w : A → R) (a b : Fin 0 → V),
  Matrix.det (LGV.pathMatrix G w a b) = 1 ∧
    LGV.signedSum G w a b = 1 ∧ LGV.unsignedSum G w a b = 1

end FiniteCombinatorics.Directed.LGVSpec
