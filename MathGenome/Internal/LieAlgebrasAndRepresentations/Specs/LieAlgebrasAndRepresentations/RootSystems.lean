import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Relation

/-! Canonical Euclidean subset interface for LA-E01. All sets of roots in this
chapter use this interface, including the empty root system in the zero space.
Rank-two classification is allocated separately to LA-E01-RankTwo. -/
namespace LieAlgebrasAndRepresentations

open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coroot vector, with the source's normalization. -/
noncomputable def coroot (a : E) : E := (2 / inner ℝ a a) • a

/-- Orthogonal reflection in the hyperplane perpendicular to `a`. -/
noncomputable def rootReflection (a b : E) : E :=
  b - (2 * inner ℝ b a / inner ℝ a a) • a

/-- The root axioms that do not require spanning the entire ambient space. -/
structure RootAxioms (R : Set E) : Prop where
  finite : R.Finite
  nonzero : ∀ a ∈ R, a ≠ 0
  reflection_mem : ∀ a ∈ R, ∀ b ∈ R, rootReflection a b ∈ R
  integral : ∀ a ∈ R, ∀ b ∈ R, ∃ z : ℤ,
    2 * inner ℝ b a / inner ℝ a a = (z : ℝ)
  reduced : ∀ a ∈ R, ∀ b ∈ R,
    b ∈ Submodule.span ℝ ({a} : Set E) → b = a ∨ b = -a

/-- Finite, reduced, crystallographic root systems. Finiteness and spanning
imply finite dimensionality, so no additional ambient dimension hypothesis is needed. -/
structure IsRootSystem (R : Set E) : Prop extends RootAxioms R where
  span_eq_top : Submodule.span ℝ R = ⊤

/-- One canonical bundled interface, usable by all subsequent constructions. -/
structure RootSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  roots : Set E
  isRootSystem : IsRootSystem roots

/-- Roots joined by a finite chain of nonorthogonal roots. -/
def RootConnected (R : Set E) : E → E → Prop :=
  Relation.EqvGen (fun a b => a ∈ R ∧ b ∈ R ∧ inner ℝ a b ≠ 0)

/-- Irreducibility means nonemptiness and connectedness of the
nonorthogonality graph. Its equivalence with the absence of an orthogonal
partition is a separate theorem below. -/
def IsIrreducible (R : Set E) : Prop :=
  R.Nonempty ∧ ∀ a ∈ R, ∀ b ∈ R, RootConnected R a b

/-- A decomposition is an unordered collection of nonempty irreducible root
systems in their own real spans, covering all roots and mutually orthogonal.
`RootAxioms` on a block together with its span is precisely a root system in
that span; the implementation also supplies the explicit subtype construction. -/
structure IsOrthogonalDecomposition (R : Set E) (C : Set (Set E)) : Prop where
  finite : C.Finite
  cover : ⋃₀ C = R
  axioms : ∀ A ∈ C, RootAxioms A
  irreducible : ∀ A ∈ C, IsIrreducible A
  orthogonal : ∀ A ∈ C, ∀ B ∈ C, A ≠ B →
    ∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = 0

namespace RootSystemSpecs

universe u

/-- Type of the public bundled-interface alias. -/
def rootSystemType : Type (u + 1) :=
  (E : Type u) → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] → Type u

/-- The public interface is the canonical structure above, with no additional data. -/
def rootSystemValue : rootSystemType := @RootSystem

/-- Direct subset formulation of the three displayed axioms in res:E01. -/
def sourceAxiomsType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ R : Set E, IsRootSystem R ↔
  R.Finite ∧ Submodule.span ℝ R = ⊤ ∧ (0 : E) ∉ R ∧
  (∀ a ∈ R, rootReflection a '' R = R) ∧
  (∀ a ∈ R, ∀ b ∈ R, ∃ z : ℤ, 2 * inner ℝ b a / inner ℝ a a = (z : ℝ)) ∧
  (∀ a ∈ R, R ∩ (Submodule.span ℝ ({a} : Set E) : Set E) = {a, -a})

def dualType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R →
  IsRootSystem (coroot '' R)

def doubleDualType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), coroot '' (coroot '' R) = R

def reflectionImageType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), RootAxioms R →
  ∀ a ∈ R, rootReflection a '' R = R

def emptyType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ [Subsingleton E], IsRootSystem (∅ : Set E)

def irreducibleType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E),
  (∀ a ∈ R, a ≠ 0) →
  (IsIrreducible R ↔ R.Nonempty ∧
    ∀ A B : Set E, A ∪ B = R →
      (∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = 0) → A = ∅ ∨ B = ∅)

def decompositionType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R →
  ∃! C : Set (Set E), IsOrthogonalDecomposition R C

def componentSystemType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (A : Set E), RootAxioms A →
  IsRootSystem {a : Submodule.span ℝ A | (a : E) ∈ A}

def componentIrreducibleType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (A : Set E), RootAxioms A → IsIrreducible A →
  IsIrreducible {a : Submodule.span ℝ A | (a : E) ∈ A}

def componentSpanType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R →
  ∀ C, IsOrthogonalDecomposition R C →
    (⨆ A : C, Submodule.span ℝ (A : Set E)) = ⊤ ∧
    ∀ A ∈ C, ∀ B ∈ C, A ≠ B →
      ∀ a ∈ Submodule.span ℝ A, ∀ b ∈ Submodule.span ℝ B,
        inner ℝ a b = 0

def internalSumType : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R →
  ∀ C, IsOrthogonalDecomposition R C →
    DirectSum.IsInternal (fun A : C => Submodule.span ℝ (A : Set E))

end RootSystemSpecs
end LieAlgebrasAndRepresentations
