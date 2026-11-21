import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DynkinExhaustion
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreSimplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsB
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsD

/-! LA-F04, notes/005, lines 2739–2761. Types are represented by the actual
Serre quotients for the standard oriented Cartan matrices from LA-E05.
The classical comparisons use the literal matrix algebras of LA-D08. -/

namespace Specs.LieAlgebrasAndRepresentations.ComplexClassification

open _root_.LieAlgebrasAndRepresentations
open scoped DirectSum
universe u v

/-- The algebra of a listed type, indexed by its standard ordered Cartan matrix. -/
abbrev Model (t : FiniteDynkinType) := Serre.Algebra t.cartan

/-- The allowed equivalence of labels on the restricted list. -/
def SameType (t s : FiniteDynkinType) : Prop :=
  t = s ∨
    (t = .B 2 (by decide) ∧ s = .C 2 (by decide)) ∨
    (t = .C 2 (by decide) ∧ s = .B 2 (by decide))

/-- Every listed diagram yields an actual finite-dimensional nonabelian simple
complex Lie algebra. -/
def modelsSimpleType : Prop :=
  ∀ t : FiniteDynkinType, FiniteDimensional ℂ (Model t) ∧ LieAlgebra.IsSimple ℂ (Model t)

/-- Every nonabelian finite-dimensional simple complex Lie algebra occurs. -/
def simpleClassificationType : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.IsSimple ℂ L],
    ∃ t : FiniteDynkinType, Nonempty (Model t ≃ₗ⁅ℂ⁆ L)

/-- The only duplication in the restricted list is the rank-two B/C case. -/
def modelUniquenessType : Prop :=
  ∀ t s : FiniteDynkinType, Nonempty (Model t ≃ₗ⁅ℂ⁆ Model s) ↔ SameType t s

/-- The simple summands can be indexed by the actual atomic ideals, with the
factor inclusions supplied by their individual isomorphisms. -/
def semisimpleClassificationType : Prop := by
  classical
  exact ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    let S := {I : LieIdeal ℂ L | IsAtom I}
    S.Finite ∧
    ∃ (t : S → FiniteDynkinType) (f : ∀ I : S, Model (t I) ≃ₗ⁅ℂ⁆ I.val)
      (g : (⨁ I : S, Model (t I)) ≃ₗ⁅ℂ⁆ L),
      ∀ (I : S) (x : Model (t I)),
        g (DirectSum.of (fun J : S => Model (t J)) I x) = (f I x : L)

/-- Every isomorphism between sums gives a bijection of factors with their
types preserved, up to B₂/C₂. -/
def semisimpleUniquenessType : Prop :=
  ∀ {ι : Type u} {κ : Type v} [Finite ι] [Finite κ]
    (t : ι → FiniteDynkinType) (s : κ → FiniteDynkinType),
    Nonempty ((⨁ i, Model (t i)) ≃ₗ⁅ℂ⁆ (⨁ j, Model (s j))) →
    ∃ e : ι ≃ κ, ∀ i, SameType (t i) (s (e i))

/-- The trivial algebra has precisely the empty family of simple factors. -/
def emptyClassificationType : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    (IsEmpty {I : LieIdeal ℂ L | IsAtom I} ↔ Subsingleton L)

def classicalAType : Prop :=
  ∀ n (hn : 1 ≤ n), Nonempty (Model (.A n hn) ≃ₗ⁅ℂ⁆ ClassicalRootsA.sl n)

def classicalBType : Prop :=
  ∀ n (hn : 2 ≤ n), Nonempty (Model (.B n hn) ≃ₗ⁅ℂ⁆ ClassicalRootsB.algebra n)

def classicalCType : Prop :=
  ∀ n (hn : 2 ≤ n), Nonempty (Model (.C n hn) ≃ₗ⁅ℂ⁆ ClassicalRootsC.sp n)

def classicalDType : Prop :=
  ∀ n (hn : 4 ≤ n), Nonempty (Model (.D n hn) ≃ₗ⁅ℂ⁆ ClassicalRootsD.algebra n)

end Specs.LieAlgebrasAndRepresentations.ComplexClassification
