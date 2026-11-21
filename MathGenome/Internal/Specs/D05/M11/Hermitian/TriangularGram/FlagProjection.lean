import MathGenome.Internal.Specs.D05.M11.Nondegenerate.OneSidedComplements
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The flag-projection stage of K05.11.hermitian, paper.tex:1748–1753.
The basis has indices 0,...,n-1; stage k consists of the first k basis vectors.
The index j therefore uses stage j before subtracting the projection of e j.
The form is linear in its first slot and conjugate-linear in its second. Over
R conjugation is the identity. No Hermitian symmetry or positivity is assumed.
A finite basis supplies finite dimension, including the empty basis.
-/
noncomputable section
namespace Specs.D05.M11.Hermitian.TriangularGram.FlagProjection

open Module

variable {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}

/-- W_k is the span of precisely the first k vectors, including k=0 and k=n. -/
def flag (e : Basis (Fin n) K V) (k : Fin (n + 1)) : Submodule K V :=
  Submodule.span K (Set.range (fun i : Fin k.val =>
    e (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)))

/-- The actual leading submatrix of the previously fixed form matrix H_ij=B(e_i,e_j). -/
def leadingMatrix (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V) (k : Fin (n + 1)) :
    Matrix (Fin k.val) (Fin k.val) K :=
  (Specs.D05.M11.Hermitian.formMatrix_value e B).submatrix
    (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))

/-- Only positive stages are hypotheses; the empty determinant will be proved to be 1. -/
def LeadingNonzero (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V) : Prop :=
  ∀ k : Fin (n + 1), 0 < k.val → (leadingMatrix e B k).det ≠ 0

/-- The three properties that uniquely specify an algebraic projection. -/
def IsFlagProjection (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V)
    (k : Fin (n + 1)) (E : Module.End K V) : Prop :=
  E ^ 2 = E ∧ E.range = flag e k ∧ E.ker = (flag e k).orthogonalBilin B

/-- Full uniqueness in the coset of e_j, not merely uniqueness among chosen bases. -/
def IsRepresentative (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V)
    (j : Fin n) (v : V) : Prop :=
  v - e j ∈ flag e j.castSucc ∧
  (∀ w ∈ flag e j.castSucc, B w v = 0) ∧
  ∀ u : V, u - e j ∈ flag e j.castSucc →
    (∀ w ∈ flag e j.castSucc, B w u = 0) → u = v

def empty_flag : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V),
    flag e 0 = ⊥ ∧
      ∀ B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V,
        (leadingMatrix e B 0).det = 1

def restriction_nondegenerate : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V),
    LeadingNonzero e B → ∀ k : Fin (n + 1),
      (B.domRestrict₁₂ (flag e k) (flag e k)).Nondegenerate

def flag_direct_sum : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V),
    LeadingNonzero e B → ∀ k : Fin (n + 1),
      IsCompl (flag e k) ((flag e k).orthogonalBilin B) ∧
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then (flag e k).orthogonalBilin B else flag e k)

/-- Once a projection is given, all three geometric properties follow from its
image, kernel, and idempotence. This statement adds no form hypotheses. -/
def projection_properties : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V)
    (k : Fin (n + 1)) (E : Module.End K V),
    IsFlagProjection e B k E →
      (∀ v, E v ∈ flag e k) ∧
      (∀ w ∈ flag e k, E w = w) ∧
      (∀ v, v - E v ∈ (flag e k).orthogonalBilin B)

def representative_unique : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V)
    (j : Fin n) (E : Module.End K V),
    IsFlagProjection e B j.castSucc E → IsRepresentative e B j (e j - E (e j))

/-- Simultaneous existence of all flag projections, their uniqueness using only
idempotence/image/kernel, the value E_0=0, and the full representative conclusion.
In particular, projection existence is a conclusion of the determinant hypothesis.
When n=0 the family has just its zero stage and there are no representatives. -/
def flag_projections : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V)
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value K V),
    LeadingNonzero e B →
    ∃ E : Fin (n + 1) → Module.End K V,
      (∀ k, IsFlagProjection e B k (E k) ∧
        ∀ F : Module.End K V, IsFlagProjection e B k F → F = E k) ∧
      (∀ k, (∀ v, E k v ∈ flag e k) ∧
        (∀ w ∈ flag e k, E k w = w) ∧
        (∀ v, v - E k v ∈ (flag e k).orthogonalBilin B)) ∧
      E 0 = 0 ∧
      ∀ j : Fin n, IsRepresentative e B j (e j - E j.castSucc (e j))

end Specs.D05.M11.Hermitian.TriangularGram.FlagProjection
