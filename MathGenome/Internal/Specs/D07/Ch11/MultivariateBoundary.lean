import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.Quotient
import MathGenome.Internal.Specs.D07.Ch11.MultivariateBoundaryBivariateNonprincipalIdeal
import MathGenome.Internal.Specs.D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders

/-!
Independent statements for K07.11.multivariate_boundary, paper.tex:2828–2874.
The coefficient ring is any commutative ring, including the zero ring.
Finite exponent vectors and coefficients are formal data, never functions
obtained by evaluating a polynomial. The bivariate equivalence puts X (index
0) in the coefficient ring and Y (index 1) in the outer polynomial ring.

The degree example has its usual values when 1 ≠ 0. The zero-ring case is
stated separately, so it is not excluded from the general construction.
Natural-valued total and coordinate degrees use the supremum of the empty
support, namely zero. Lexicographic degree is a different, vector-valued
object. The two substantial counterexamples use the upstream interfaces.
-/

universe u
noncomputable section

namespace Specs.D07.Ch11.MultivariateBoundary

open MvPolynomial
open scoped Pointwise MonomialOrder

abbrev exponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

/-- Swap first, since `finSuccEquiv` makes coordinate zero the outer variable. -/
def bivariateEquivValue (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R ≃+* Polynomial (Polynomial R) :=
  ((renameEquiv R (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (finSuccEquiv R 1).toRingEquiv).trans
    (Polynomial.mapEquiv (uniqueAlgEquiv R (Fin 1)).toRingEquiv)

def BivariateEquivType : Type (u + 1) :=
  (R : Type u) → [CommRing R] →
    MvPolynomial (Fin 2) R ≃+* Polynomial (Polynomial R)

/-- On a finite variable set, finitely supported exponent vectors are all of ℕ^m. -/
def ExponentVectorModel : Prop :=
  ∀ m : ℕ, ∃ e : (Fin m →₀ ℕ) ≃ (Fin m → ℕ), ∀ d i, e d i = d i

def CoefficientModel : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ),
    (∀ p : MvPolynomial (Fin m) R, (Function.support fun d => p.coeff d).Finite) ∧
    (∀ p q : MvPolynomial (Fin m) R, (∀ d, p.coeff d = q.coeff d) ↔ p = q) ∧
    (∀ a : (Fin m →₀ ℕ) →₀ R, ∃ p : MvPolynomial (Fin m) R, p.coeff = a)

def MonomialExpansion : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ) (p : MvPolynomial (Fin m) R),
    p = ∑ d ∈ p.support, C (p.coeff d) * ∏ i : Fin m, (X i) ^ d i

def CoefficientArithmetic : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ) (p q : MvPolynomial (Fin m) R)
    (d : Fin m →₀ ℕ),
    (p + q).coeff d = p.coeff d + q.coeff d ∧
    (-p).coeff d = -p.coeff d ∧
    (p * q).coeff d = ∑ ab ∈ Finset.antidiagonal d, p.coeff ab.1 * q.coeff ab.2

def SupportClosure : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ) (p q : MvPolynomial (Fin m) R),
    (p + q).support ⊆ p.support ∪ q.support ∧
    (-p).support = p.support ∧ (p * q).support ⊆ p.support + q.support

/-- The canonical coefficientwise/convolution operations form a commutative ring. -/
def RingStructure : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ),
    ∃ s : CommRing (MvPolynomial (Fin m) R),
      s.toAddCommGroup = (inferInstance : AddCommGroup (MvPolynomial (Fin m) R)) ∧
      s.toMul = (inferInstance : Mul (MvPolynomial (Fin m) R)) ∧
      s.toOne = (inferInstance : One (MvPolynomial (Fin m) R))

def RingLaws : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ) (p q r : MvPolynomial (Fin m) R),
    (p * q) * r = p * (q * r) ∧
    C 1 * p = p ∧ p * C 1 = p ∧
    p * (q + r) = p * q + p * r ∧
    (p + q) * r = p * r + q * r ∧ p * q = q * p

def BivariateCoefficients : Prop :=
  ∀ (R : Type u) [CommRing R] (p : MvPolynomial (Fin 2) R) (i j : ℕ),
    ((bivariateEquivValue R p).coeff j).coeff i = p.coeff (exponent i j)

def BivariateGenerators : Prop :=
  ∀ (R : Type u) [CommRing R],
    bivariateEquivValue R (X 0) = Polynomial.C Polynomial.X ∧
    bivariateEquivValue R (X 1) = Polynomial.X ∧
    ∀ a : R, bivariateEquivValue R (C a) = Polynomial.C (Polynomial.C a)

/-- Coefficient support in the two presentations is exactly the same data. -/
def BivariateSupport : Prop :=
  ∀ (R : Type u) [CommRing R] (p : MvPolynomial (Fin 2) R),
    (∀ i j, exponent i j ∈ p.support ↔
      i ∈ ((bivariateEquivValue R p).coeff j).support) ∧
    (∀ j, j ∈ (bivariateEquivValue R p).support ↔
      ∃ i, exponent i j ∈ p.support)

/-- The same double convolution computes products in both descriptions. -/
def BivariateProductCoefficients : Prop :=
  ∀ (R : Type u) [CommRing R] (p q : MvPolynomial (Fin 2) R) (k l : ℕ),
    (p * q).coeff (exponent k l) =
      ∑ jj ∈ Finset.antidiagonal l, ∑ ii ∈ Finset.antidiagonal k,
        p.coeff (exponent ii.1 jj.1) * q.coeff (exponent ii.2 jj.2) ∧
    (((bivariateEquivValue R p) * (bivariateEquivValue R q)).coeff l).coeff k =
      ∑ jj ∈ Finset.antidiagonal l, ∑ ii ∈ Finset.antidiagonal k,
        p.coeff (exponent ii.1 jj.1) * q.coeff (exponent ii.2 jj.2)

/-- Setting either coordinate to zero leaves the polynomial ring in the other. -/
def CoordinateQuotients : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∃ e : (MvPolynomial (Fin 2) R ⧸ Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) R)))
        ≃+* Polynomial R,
      e (Ideal.Quotient.mk _ (X 1)) = Polynomial.X ∧
      ∀ a : R, e (Ideal.Quotient.mk _ (C a)) = Polynomial.C a) ∧
    (∃ e : (MvPolynomial (Fin 2) R ⧸ Ideal.span ({X 1} : Set (MvPolynomial (Fin 2) R)))
        ≃+* Polynomial R,
      e (Ideal.Quotient.mk _ (X 0)) = Polynomial.X ∧
      ∀ a : R, e (Ideal.Quotient.mk _ (C a)) = Polynomial.C a)

def DegreeDefinitions : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ) (p : MvPolynomial (Fin m) R),
    p.totalDegree = p.support.sup (fun d => d.sum fun _ n => n) ∧
    ∀ i : Fin m, p.degreeOf i = p.support.sup (fun d => d i)

/-- Bottom-valued degrees distinguish zero from a nonzero constant; the
canonical natural-valued degrees are their nonzero values. -/
def DegreeWithBottom : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (m : ℕ) (p : MvPolynomial (Fin m) R),
    p.support.sup (fun d => WithBot.some (d.sum fun _ n => n)) =
      (if p = 0 then ⊥ else WithBot.some p.totalDegree) ∧
    ∀ i : Fin m, p.support.sup (fun d => WithBot.some (d i)) =
      (if p = 0 then ⊥ else WithBot.some (p.degreeOf i))

def ExampleDegrees : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R],
    let p : MvPolynomial (Fin 2) R := X 0 + X 1 ^ 2
    p.totalDegree = 2 ∧ p.degreeOf 0 = 1 ∧ p.degreeOf 1 = 2

def ExampleLexLeadingMonomial : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R],
    let p : MvPolynomial (Fin 2) R := X 0 + X 1 ^ 2
    MultivariateBoundaryDistinctDivisionRemainders.lexOrder.degree p = Finsupp.single 0 1 ∧
    MultivariateBoundaryDistinctDivisionRemainders.lexOrder.leadingTerm p = X 0

def ZeroRingExample : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R],
    let p : MvPolynomial (Fin 2) R := X 0 + X 1 ^ 2
    p = 0 ∧ p.totalDegree = 0 ∧ p.degreeOf 0 = 0 ∧ p.degreeOf 1 = 0

/-- The field examples are supplied by the two separately proved prerequisites. -/
def FieldBoundaries : Prop :=
  MultivariateBoundaryBivariateNonprincipalIdeal.VariablesPrime.{u} ∧
  MultivariateBoundaryBivariateNonprincipalIdeal.XNotDvdY.{u} ∧
  MultivariateBoundaryBivariateNonprincipalIdeal.VariablesNotAssociated.{u} ∧
  MultivariateBoundaryBivariateNonprincipalIdeal.OriginIdealProper.{u} ∧
  MultivariateBoundaryBivariateNonprincipalIdeal.OriginIdealNotPrincipal.{u} ∧
  MultivariateBoundaryBivariateNonprincipalIdeal.UfdNotPid.{u} ∧
  MultivariateBoundaryDistinctDivisionRemainders.LexVariableOrder ∧
  MultivariateBoundaryDistinctDivisionRemainders.LeadingMonomials.{u} ∧
  MultivariateBoundaryDistinctDivisionRemainders.CancellationIdentities.{u} ∧
  MultivariateBoundaryDistinctDivisionRemainders.TerminalRemainders.{u} ∧
  MultivariateBoundaryDistinctDivisionRemainders.IdealDifference.{u} ∧
  MultivariateBoundaryDistinctDivisionRemainders.DivisionSteps.{u} ∧
  MultivariateBoundaryDistinctDivisionRemainders.DistinctDivisionRemainders.{u}

end Specs.D07.Ch11.MultivariateBoundary
