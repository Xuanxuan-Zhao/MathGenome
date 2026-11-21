import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreFiniteType
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.DirectSum

/-! LA-F03, notes/005, theorem and proof at lines 2648–2715.
The section assumes the Cartan matrix of a finite reduced root system.
The graph below is the underlying Dynkin graph: an off-diagonal Cartan
entry is nonzero exactly when the corresponding vertices are adjacent.
The quotient indexes actual connected components, including no components
when the diagram is empty. No simplicity certificate is part of the data.
-/
noncomputable section
namespace LieAlgebrasAndRepresentations.Serre
universe u
variable {ι : Type u} [DecidableEq ι]

/-- Connectivity in the underlying graph of the integer Cartan matrix. -/
def MatrixConnected (A : Matrix ι ι ℤ) : ι → ι → Prop :=
  Relation.EqvGen (fun i j => i ≠ j ∧ A i j ≠ 0)

/-- The actual connected components, not an arbitrary decomposition index. -/
abbrev Component (A : Matrix ι ι ℤ) :=
  Quotient (Relation.EqvGen.setoid (fun i j => i ≠ j ∧ A i j ≠ 0))

def componentOf (A : Matrix ι ι ℤ) (i : ι) : Component A := Quotient.mk _ i

def componentVertices (A : Matrix ι ι ℤ) (c : Component A) : Set ι :=
  {i | componentOf A i = c}

/-- The Cartan matrix restricted to the vertices of one connected component. -/
def componentMatrix (A : Matrix ι ι ℤ) (c : Component A) :
    Matrix (componentVertices A c) (componentVertices A c) ℤ :=
  fun i j => A i.val j.val

end LieAlgebrasAndRepresentations.Serre

namespace Specs.LieAlgebrasAndRepresentations.SerreSimplicity
open _root_.LieAlgebrasAndRepresentations
open _root_.LieAlgebrasAndRepresentations.Serre
open scoped DirectSum
universe u v

/-- Simplicity includes nonabelianness. Connected diagrams are nonempty. -/
def simpleExpected : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι],
  ∀ (R : Set E), IsRootSystem R → ∀ z, RootRegular R z →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R z b →
  ∀ A : Matrix ι ι ℤ, (∀ i j, (A i j : ℝ) = cartanMatrix b i j) →
    (∀ i j, MatrixConnected A i j) → LieAlgebra.IsSimple ℂ (Algebra A)

/-- Every component factor is the Serre algebra of its restricted matrix,
and is nonabelian simple, with no hypotheses on the number of components. -/
def componentSimpleExpected : Prop := by
  classical
  exact ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι],
    ∀ (R : Set E), IsRootSystem R → ∀ z, RootRegular R z →
    ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R z b →
    ∀ A : Matrix ι ι ℤ, (∀ i j, (A i j : ℝ) = cartanMatrix b i j) →
      ∀ c : Component A, LieAlgebra.IsSimple ℂ (Algebra (componentMatrix A c))

/-- The isomorphism is the actual sum of the component inclusions: its values
on all three generator families are prescribed. The finite-type hypotheses
are those of the source; the empty diagram is included. -/
def componentSumExpected : Prop := by
  classical
  exact ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι],
    ∀ (R : Set E), IsRootSystem R → ∀ z, RootRegular R z →
    ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R z b →
    ∀ A : Matrix ι ι ℤ, (∀ i j, (A i j : ℝ) = cartanMatrix b i j) →
      ∃ φ : (⨁ c : Component A, Algebra (componentMatrix A c)) ≃ₗ⁅ℂ⁆ Algebra A,
        ∀ (c : Component A) (i : componentVertices A c),
          φ (DirectSum.lof ℂ _ _ c (e (componentMatrix A c) i)) = e A i.val ∧
          φ (DirectSum.lof ℂ _ _ c (f (componentMatrix A c) i)) = f A i.val ∧
          φ (DirectSum.lof ℂ _ _ c (h (componentMatrix A c) i)) = h A i.val

/-- The algebra of the empty diagram is the zero algebra. -/
def emptyExpected : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] [IsEmpty ι] (A : Matrix ι ι ℤ),
    Subsingleton (Algebra A)

end Specs.LieAlgebrasAndRepresentations.SerreSimplicity
