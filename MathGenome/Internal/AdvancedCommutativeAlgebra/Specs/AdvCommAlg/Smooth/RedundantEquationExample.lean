import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.JacobianPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! The warning following SM-17, paper.tex:1495–1503.
There is one variable and two displayed equations, X and X². Rows of
Jacobian matrices are variables and columns are equations, as in KD-12.
No nontriviality hypothesis is imposed on the base ring.
-/
namespace Specs.AdvCommAlg.Smooth.Redundant

universe u
noncomputable section
open MvPolynomial

/-- The redundant ordered list of equations. -/
def equations (A : Type u) [CommRing A] : Fin 2 → MvPolynomial (Fin 1) A :=
  fun j => if j = 0 then X 0 else X 0 ^ 2

abbrev relationIdeal (A : Type u) [CommRing A] :=
  Ideal.span (Set.range (equations A))

/-- The literal quotient by the redundant list, with its quotient A-algebra structure. -/
abbrev Quotient (A : Type u) [CommRing A] :=
  MvPolynomial (Fin 1) A ⧸ relationIdeal A

/-- Partial derivatives of a list, reduced first in the displayed quotient
and then in the residue field of its prime. -/
def residueMatrix {A : Type u} [CommRing A] (q : PrimeSpectrum (Quotient A))
    {c : ℕ} (f : Fin c → MvPolynomial (Fin 1) A) :
    Matrix (Fin 1) (Fin c) q.asIdeal.ResidueField :=
  fun i j => algebraMap (Quotient A) q.asIdeal.ResidueField
    (Ideal.Quotient.mk (relationIdeal A) (pderiv i (f j)))

def redundantMatrix {A : Type u} [CommRing A] (q : PrimeSpectrum (Quotient A)) :=
  residueMatrix q (equations A)

def singleMatrix {A : Type u} [CommRing A] (q : PrimeSpectrum (Quotient A)) :=
  residueMatrix q (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) A))

/-- Both lists generate exactly (X). -/
def idealEquality : Prop := ∀ (A : Type u) [CommRing A],
  relationIdeal A = Ideal.span ({X 0, X 0 ^ 2} : Set (MvPolynomial (Fin 1) A)) ∧
  relationIdeal A = Ideal.span ({X 0} : Set (MvPolynomial (Fin 1) A))

/-- The identification is an A-algebra isomorphism and sends every polynomial
class to evaluation at zero, so in particular the variable goes to zero. -/
def quotientIdentification : Prop := ∀ (A : Type u) [CommRing A],
  ∃ e : Quotient A ≃ₐ[A] A, ∀ p : MvPolynomial (Fin 1) A,
    e (Ideal.Quotient.mk (relationIdeal A) p) = aeval (fun _ => (0 : A)) p

def smoothExample : Prop := ∀ (A : Type u) [CommRing A],
  Algebra.Smooth A (Quotient A)

/-- These are the actual partial derivative matrices over each residue field. -/
def matrixEntries : Prop := ∀ (A : Type u) [CommRing A]
  (q : PrimeSpectrum (Quotient A)),
  redundantMatrix q = Matrix.of ![![1, 0]] ∧ singleMatrix q = 1

def rankComparison : Prop := ∀ (A : Type u) [CommRing A]
  (q : PrimeSpectrum (Quotient A)),
  (redundantMatrix q).rank = 1 ∧ (redundantMatrix q).rank ≠ 2 ∧
    (singleMatrix q).rank = 1

/-- Smoothness does not imply full column rank for the redundant list.
The one-equation list generates the same ideal and has full column rank. -/
def warningExample : Prop := ∀ (A : Type u) [CommRing A],
  Algebra.Smooth A (Quotient A) ∧
    (relationIdeal A = Ideal.span ({X 0} : Set (MvPolynomial (Fin 1) A))) ∧
    ∀ q : PrimeSpectrum (Quotient A),
      (redundantMatrix q).rank ≠ 2 ∧ (singleMatrix q).rank = 1

/-- For the zero ring the rank comparison has no points at which to be tested. -/
def zeroCase : Prop := ∀ (A : Type u) [CommRing A] [Subsingleton A],
  IsEmpty (PrimeSpectrum (Quotient A))

end
end Specs.AdvCommAlg.Smooth.Redundant
