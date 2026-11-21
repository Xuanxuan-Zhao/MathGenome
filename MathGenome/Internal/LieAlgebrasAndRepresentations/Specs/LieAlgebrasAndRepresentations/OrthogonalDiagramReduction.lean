import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalCoordinateRoots
import Mathlib.Algebra.Lie.Classical

/-! The outer classes of orthogonal involutions, from the orthogonal proof of
LA-J07 and the actual matrix root data of LA-D08. -/

namespace Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction

open AutomorphismDecomposition PolarRealStructures
open LieAlgebrasAndRepresentations.RealForms

universe u v

/-- Put a bracket-preserving linear equivalence in the automorphism group of LA-J01. -/
def toAut {L : Type u} [LieRing L] [LieAlgebra ℂ L] (a : L ≃ₗ⁅ℂ⁆ L) : Aut L :=
  ⟨a.toLinearEquiv, a.map_lie⟩

def toAutType :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L], (L ≃ₗ⁅ℂ⁆ L) → Aut L

/-- Any outer quotient with finitely many classes has the same image on the
compact automorphisms as on all complex automorphisms. -/
def compactRepresentativesType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), IsCompact ω →
    ∀ {G : Type v} [Group G] [Finite G] (q : Aut L →* G)
      (a : L ≃ₗ⁅ℂ⁆ L),
      ∃ b : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω b ∧ q (toAut b) = q (toAut a)

section Diagrams

open LieAlgebrasAndRepresentations.ClassicalCoordinates
open _root_.LieAlgebrasAndRepresentations (dynkinDiagram)

/-- The oriented B path and the D fork, with the vertex numbering of the
coordinate simple systems. -/
def bDiagramTrivialType : Prop :=
  ∀ (n : ℕ) (p : Equiv.Perm (Fin n)),
    (∀ i j, (dynkinDiagram (simpleB n)).edges (p i) (p j) =
      (dynkinDiagram (simpleB n)).edges i j) →
    (∀ i j, (dynkinDiagram (simpleB n)).arrow (p i) (p j) ↔
      (dynkinDiagram (simpleB n)).arrow i j) → p = 1

def forkGroup (n : ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {p | ∀ i j, forkAdjacent (p i) (p j) ↔ forkAdjacent i j}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' h k := fun i j => (h _ _).trans (k i j)
  inv_mem' {p} h := fun i j => by simpa using (h (p.symm i) (p.symm j)).symm

def forkGroupType :=
  ∀ n : ℕ, Subgroup (Equiv.Perm (Fin n))

def forkGroupIsoType : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    Nonempty (forkGroup n ≃* Equiv.Perm (Fin (if n = 4 then 3 else 2)))

end Diagrams

open Matrix LieAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

variable (ι : Type u) [Fintype ι] [DecidableEq ι]

abbrev so := Orthogonal.so ι ℂ

/-- The negative unit on one real coordinate and the identity on the others. -/
def reflectionMatrix (j : ι) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => if i = j then -1 else 1)

def reflectionMatrixType :=
  ∀ (ι : Type u) [DecidableEq ι], ι → Matrix ι ι ℝ

def reflectionMatrixSpec : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (j : ι),
    let A := reflectionMatrix ι j
    Aᵀ * A = 1 ∧ A.det = -1

def ActsByReflection (j : ι) (a : so ι ≃ₗ⁅ℂ⁆ so ι) : Prop :=
  let A := Complex.ofRealHom.mapMatrix (reflectionMatrix ι j)
  ∀ X : so ι, (a X : Matrix ι ι ℂ) = A * (X : Matrix ι ι ℂ) * Aᵀ

def reflectionExistsType : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (j : ι),
    ∃ a : so ι ≃ₗ⁅ℂ⁆ so ι, ActsByReflection ι j a

def IsCoefficientConjugation (ω : Conjugation (so ι)) : Prop :=
  ∀ (X : so ι) (i j : ι), ((ω.map X : so ι) : Matrix ι ι ℂ) i j = star (X.val i j)

def reflectionCommutesType : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (j : ι)
    (a : so ι ≃ₗ⁅ℂ⁆ so ι), ActsByReflection ι j a →
    ∀ (ω : Conjugation (so ι)), IsCoefficientConjugation ι ω → Intertwines ω ω a

/-- Finite quotient of the actual group of Lie automorphisms by inner exponentials.
There is one outer class in type B, a two-element group in type D outside
rank four, and the full symmetric group on three letters in rank four. -/
def outerQuotientType : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι],
    SolvableRadical.IsSemisimple_value ℂ (so ι) →
    (∃ n : ℕ, 1 ≤ n ∧ Fintype.card ι = 2*n+1) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Fintype.card ι = 2*n) →
    ∃ h : (inner (so ι)).Normal,
      letI := h
      (∀ n : ℕ, 1 ≤ n → Fintype.card ι = 2*n+1 →
        Subsingleton (Aut (so ι) ⧸ inner (so ι))) ∧
      (∀ n : ℕ, 3 ≤ n → n ≠ 4 → Fintype.card ι = 2*n →
        Nonempty ((Aut (so ι) ⧸ inner (so ι)) ≃* Equiv.Perm (Fin 2))) ∧
      (Fintype.card ι = 8 →
        Nonempty ((Aut (so ι) ⧸ inner (so ι)) ≃* Equiv.Perm (Fin 3))) ∧
      (∀ n : ℕ, 3 ≤ n → Fintype.card ι = 2*n →
        ∀ j (a : so ι ≃ₗ⁅ℂ⁆ so ι), ActsByReflection ι j a →
        QuotientGroup.mk (s := inner (so ι)) (toAut a) ≠ 1 ∧
          (QuotientGroup.mk (s := inner (so ι)) (toAut a)) ^ 2 = 1)

/-- The two possible classes after conjugation by an automorphism of the
compact form. Membership in the inner subgroup expresses equality of classes. -/
def ReducesToReflection (ω : Conjugation (so ι)) (j : ι)
    (a : so ι ≃ₗ⁅ℂ⁆ so ι) : Prop :=
  ∃ (b r : so ι ≃ₗ⁅ℂ⁆ so ι), Intertwines ω ω b ∧ ActsByReflection ι j r ∧
    let g := toAut b * toAut a * (toAut b)⁻¹
    g ∈ inner (so ι) ∨ g * (toAut r)⁻¹ ∈ inner (so ι)

/-- The reduction applies to every outer class of order dividing two.
In particular it applies before choosing an involutive lift of that class. -/
def outerClassReductionType : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι],
    SolvableRadical.IsSemisimple_value ℂ (so ι) →
    (Fintype.card ι = 3 ∨ 5 ≤ Fintype.card ι) →
    ∀ (ω : Conjugation (so ι)), IsCoefficientConjugation ι ω → IsCompact ω →
    ∀ (normal : (inner (so ι)).Normal),
      letI := normal
      ∀ (a : so ι ≃ₗ⁅ℂ⁆ so ι),
        (QuotientGroup.mk (s := inner (so ι)) (toAut a)) ^ 2 = 1 →
        ∀ j : ι, ReducesToReflection ι ω j a

/-- A compact-preserving change of coordinates moves every involution's
outer class into the two classes represented by orthogonal conjugation. -/
def involutionReductionType : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι],
    SolvableRadical.IsSemisimple_value ℂ (so ι) →
    (Fintype.card ι = 3 ∨ 5 ≤ Fintype.card ι) →
    ∀ (ω : Conjugation (so ι)), IsCoefficientConjugation ι ω → IsCompact ω →
    ∀ (a : so ι ≃ₗ⁅ℂ⁆ so ι), Function.Involutive a →
    ∀ j : ι, ReducesToReflection ι ω j a

end Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction
