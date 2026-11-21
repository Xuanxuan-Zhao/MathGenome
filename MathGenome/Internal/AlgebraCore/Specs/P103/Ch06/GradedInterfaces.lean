import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Adjoin.Basic

/-!
The integer indexing is also used for nonnegative gradings: negative algebra
pieces vanish. Thus the same module convention applies to associated graded
modules, by extending their nonnegative grading by zero.
-/
namespace P103.Graded

/-- A commutative algebra graded in nonnegative degrees. Its base ring is
literally its degree-zero piece, with Mathlib's induced ring and algebra. -/
structure NonnegativeGrading (A : Type*) [CommRing A] where
  piece : ℤ → AddSubgroup A
  grading : GradedRing piece
  negative : ∀ j : ℤ, j < 0 → piece j = ⊥

attribute [instance] NonnegativeGrading.grading

/-- An internal, possibly unbounded, integer grading of an A-module.
Finiteness is the ordinary `Module.Finite A M`, not assumed homogeneous data. -/
structure ModuleGrading {A : Type*} [CommRing A] (G : NonnegativeGrading A)
    (M : Type*) [AddCommGroup M] [Module A M] where
  piece : ℤ → AddSubgroup M
  decomposition : DirectSum.Decomposition piece
  compatible : SetLike.GradedSMul G.piece piece

attribute [instance] ModuleGrading.decomposition ModuleGrading.compatible

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- B = A₀, including its inherited ring structure. -/
abbrev Base (G : NonnegativeGrading A) := G.piece 0

/-- Degree preserving A-linear maps. -/
structure Hom (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (V : ModuleGrading G N) extends M →ₗ[A] N where
  degree_preserving : ∀ j m, m ∈ U.piece j → toLinearMap m ∈ V.piece j

end P103.Graded

namespace Specs.P103.Graded
open _root_.P103.Graded
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Standard means finitely many degree-one algebra generators over A₀. -/
def standardType := NonnegativeGrading A → Prop
def standardValue : standardType (A := A) := fun G =>
  ∃ s : Finset A, (∀ a ∈ s, a ∈ G.piece 1) ∧
    Algebra.adjoin (Base G) (s : Set A) = ⊤

/-- A finite family may be empty, and its degrees may be negative. -/
def homogeneousGeneratorsType (G : NonnegativeGrading A) (U : ModuleGrading G M) : Prop :=
  ∃ s : Finset M, Submodule.span A (s : Set M) = ⊤ ∧
    ∀ m ∈ s, ∃ j : ℤ, m ∈ U.piece j

def boundedBelowType (G : NonnegativeGrading A) (U : ModuleGrading G M) : Prop :=
  ∃ b : ℤ, ∀ j : ℤ, j < b → U.piece j = ⊥

/-- M(-1) has the same underlying module and piece j equal to M_(j-1). -/
def shiftPieceType (G : NonnegativeGrading A) := ModuleGrading G M → ℤ → AddSubgroup M
def shiftPieceValue (G : NonnegativeGrading A) : shiftPieceType (M := M) G :=
  fun U j => U.piece (j - 1)

/-- The shifted pieces must again give a genuine graded module. -/
def shiftType (G : NonnegativeGrading A) (U : ModuleGrading G M) : Prop :=
  ∃ V : ModuleGrading G M, ∀ j, V.piece j = U.piece (j - 1)


/-- Closed types for the independent declaration comparisons. -/
def standardDefinitionType :=
  ∀ {A : Type*} [CommRing A], NonnegativeGrading A → Prop

def standardDefinitionValue : standardDefinitionType := @standardValue

def shiftPieceDefinitionType :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A), ModuleGrading G M → ℤ → AddSubgroup M

def shiftPieceDefinitionValue : shiftPieceDefinitionType := @shiftPieceValue

def homogeneousGeneratorsTheorem : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M) [Module.Finite A M],
    homogeneousGeneratorsType G U

def boundedBelowTheorem : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M) [Module.Finite A M],
    boundedBelowType G U

def shiftTheorem : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M), shiftType G U

end Specs.P103.Graded
