import MathGenome.Internal.Specs.D07.Ch19.ResultantDefinition
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-! K07.19.resultant_specialization, paper.tex:5486–5513.
The bounds stay fixed under coefficient homomorphisms. No characteristic
restriction, separability assumption, or nonvanishing condition on the second
polynomial is added. A single splitting extension contains all roots.
The positive degree guard excludes the empty determinant and forces only one
specialized polynomial to be nonzero. -/
universe u v w
namespace Specs.D07.Ch19.ResultantSpecialization
open Polynomial
open Specs.D07.Ch19.ResultantDefinition

def CoefficientHomomorphism : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (f g : R[X]) (n m : ℕ),
    f.degree ≤ (n : WithBot ℕ) → g.degree ≤ (m : WithBot ℕ) →
    fixedResultant (f.map φ) (g.map φ) n m = φ (fixedResultant f g n m)

/-- The necessary implication allows arbitrary commutative root rings. -/
def NecessaryElimination : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (f g : R[X]) (n m : ℕ) (x : S),
    f.degree ≤ (n : WithBot ℕ) → g.degree ≤ (m : WithBot ℕ) → 0 < n + m →
    (f.map φ).eval x = 0 → (g.map φ).eval x = 0 →
    φ (fixedResultant f g n m) = 0

/-- Either positive degree may survive, and the other polynomial may become
zero or constant. Splitting is required only for the surviving polynomial. -/
def SplittingFieldCriterion : Prop :=
  ∀ (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [Field K] [Field L] [Algebra K L]
    (φ : R →+* K) (f g : R[X]) (n m : ℕ),
    f.degree ≤ (n : WithBot ℕ) → g.degree ≤ (m : WithBot ℕ) →
    ((0 < n ∧ (f.map φ).natDegree = n ∧
        ((f.map φ).map (algebraMap K L)).Splits) ∨
      (0 < m ∧ (g.map φ).natDegree = m ∧
        ((g.map φ).map (algebraMap K L)).Splits)) →
    (φ (fixedResultant f g n m) = 0 ↔
      ∃ x : L, aeval x (f.map φ) = 0 ∧ aeval x (g.map φ) = 0)

/-- In particular this gives the stated criterion in any chosen algebraically
closed extension of the specialized coefficient field. -/
def AlgebraicClosureCriterion : Prop :=
  ∀ (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (φ : R →+* K) (f g : R[X]) (n m : ℕ),
    f.degree ≤ (n : WithBot ℕ) → g.degree ≤ (m : WithBot ℕ) →
    ((0 < n ∧ (f.map φ).natDegree = n) ∨
      (0 < m ∧ (g.map φ).natDegree = m)) →
    (φ (fixedResultant f g n m) = 0 ↔
      ∃ x : L, aeval x (f.map φ) = 0 ∧ aeval x (g.map φ) = 0)

def EmptyDeterminant : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]),
    fixedResultant f g 0 0 = 1 ∧ fixedResultant (0 : R[X]) 0 0 0 = 1

/-- The notes' example includes the literal Sylvester matrix, the parameter
resultant, specialization of both polynomials and resultant, and failure of
lifting even to an extension field. The first X below is the parameter Y. -/
def DegreeDropCounterexample : Prop :=
  let f : ℚ[X][X] := C X * X + 1
  let g : ℚ[X][X] := C X * X + C 2
  let φ : ℚ[X] →+* ℚ := evalRingHom 0
  f.natDegree = 1 ∧ g.natDegree = 1 ∧
    descendingSylvester f g 1 1 = !![X, 1; X, 2] ∧
    fixedResultant f g 1 1 = X ∧
    f.map φ = C 1 ∧ g.map φ = C 2 ∧
    φ (fixedResultant f g 1 1) = 0 ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      ¬ ∃ x : L, aeval x (f.map φ) = 0 ∧ aeval x (g.map φ) = 0

end Specs.D07.Ch19.ResultantSpecialization
