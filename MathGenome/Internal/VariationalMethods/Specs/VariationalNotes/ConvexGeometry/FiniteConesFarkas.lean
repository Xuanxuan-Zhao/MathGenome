import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Independent statements for paper.tex, §v01-09, Lemma
`lem:finitely-generated-closed` and Theorem `thm:farkas`.
Finite index types may be empty. The basis statements also apply to a subspace,
by taking E to be that subspace with its induced module structure. -/

open Set
noncomputable section
universe u v w
namespace VariationalNotes.ConvexGeometry.Specs

def finite_conicHull_eq : Prop :=
  ∀ {ι : Type u} [Fintype ι] {E : Type v} [AddCommGroup E] [Module ℝ E]
    (a : ι → E), conicHull (range a) =
      {z | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∑ i, c i • a i) = z}

def finite_conicHull_isClosed : Prop :=
  ∀ {ι : Type u} [Fintype ι] {E : Type v} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E] (a : ι → E),
    IsClosed (conicHull (range a))

def farkas_alternative : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ),
    Xor (∃ x : n → ℝ, 0 ≤ x ∧ A.mulVec x = b)
      (∃ y : m → ℝ, 0 ≤ A.transpose.mulVec y ∧ dotProduct b y < 0)

/-- The same coefficients solve the vector equation and its coordinate matrix equation. -/
def basis_conic_feasibility : Prop :=
  ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {E : Type w} [AddCommGroup E] [Module ℝ E]
    (e : Module.Basis κ ℝ E) (a : ι → E) (b : E),
    (∃ x : ι → ℝ, 0 ≤ x ∧ (∑ i, x i • a i) = b) ↔
    (∃ x : ι → ℝ, 0 ≤ x ∧
      Matrix.mulVec (fun k i => e.repr (a i) k) x = fun k => e.repr b k)

/-- Farkas in any chosen basis, in particular a basis of a subspace. -/
def farkas_in_basis : Prop :=
  ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {E : Type w} [AddCommGroup E] [Module ℝ E]
    (e : Module.Basis κ ℝ E) (a : ι → E) (b : E),
    Xor (∃ x : ι → ℝ, 0 ≤ x ∧ (∑ i, x i • a i) = b)
      (∃ y : κ → ℝ,
        0 ≤ Matrix.mulVec (Matrix.transpose (fun k i => e.repr (a i) k)) y ∧
        dotProduct (fun k => e.repr b k) y < 0)

end VariationalNotes.ConvexGeometry.Specs
