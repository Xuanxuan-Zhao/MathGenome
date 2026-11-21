import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.LinearAlgebra.StdBasis

/-!
Independent interface for paper.tex:357–362. Formal polynomials use Mathlib's
coefficient objects, never value functions. The exponent tuples below are actual
functions `Fin m → ℕ`. The monoid algebra is a one-field wrapper around the
finitely supported coefficient family, with convolution multiplication.
-/

noncomputable section

namespace D05.Foundations

abbrev Exponent (m : ℕ) := Fin m → ℕ

abbrev FormalPolynomial (R : Type*) [CommRing R] (m : ℕ) := MvPolynomial (Fin m) R

abbrev PolynomialCoefficients (R : Type*) [CommRing R] (m : ℕ) :=
  AddMonoidAlgebra R (Exponent m)

/-- Coordinate columns with their standard componentwise module structure. -/
abbrev CoordinateModule (R : Type*) (n : ℕ) := Fin n → R

/-- All functions on the finite variable set have finite support. -/
def exponentEquiv (m : ℕ) : (Fin m →₀ ℕ) ≃+ Exponent m :=
  Finsupp.addEquivFunOnFinite

/-- A finite enumeration of all pairs of nonnegative exponent tuples summing to γ.
The membership characterization is a separate obligation below. -/
def exponentSplittings {m : ℕ} (γ : Exponent m) : Finset (Exponent m × Exponent m) :=
  (Finset.antidiagonal ((exponentEquiv m).symm γ)).map
    ((exponentEquiv m).toEquiv.prodCongr (exponentEquiv m).toEquiv).toEmbedding

end D05.Foundations

namespace D05.Specs.FormalPolynomials

open D05.Foundations

def coefficientRingEquivType := ∀ (R : Type*) [CommRing R] (m : ℕ),
  FormalPolynomial R m ≃+* PolynomialCoefficients R m

def coefficientRingEquivValue : coefficientRingEquivType :=
  fun R _ m => AddMonoidAlgebra.mapDomainRingEquiv R (exponentEquiv m)

def coefficientEquivType := ∀ (R : Type*) [CommRing R] (m : ℕ),
  FormalPolynomial R m ≃ (Exponent m →₀ R)

def coefficientEquivValue : coefficientEquivType := fun R _ m =>
  (coefficientRingEquivValue R m).toEquiv.trans AddMonoidAlgebra.coeffEquiv

def coefficientBridge : Prop := ∀ (R : Type*) [CommRing R] (m : ℕ)
    (p : FormalPolynomial R m) (α : Exponent m),
  coefficientEquivValue R m p α = p.coeff ((exponentEquiv m).symm α)

def inverseCoefficientBridge : Prop := ∀ (R : Type*) [CommRing R] (m : ℕ)
    (a : Exponent m →₀ R) (s : Fin m →₀ ℕ),
  ((coefficientEquivValue R m).symm a).coeff s = a (exponentEquiv m s)

def coefficientExt : Prop := ∀ (R : Type*) [CommRing R] (m : ℕ)
    (p q : FormalPolynomial R m),
  p = q ↔ ∀ α : Exponent m, coefficientEquivValue R m p α = coefficientEquivValue R m q α

def splittingMembership : Prop := ∀ (m : ℕ) (γ α β : Exponent m),
  (α, β) ∈ exponentSplittings γ ↔ α + β = γ

def coefficientOperations : Prop := ∀ (R : Type*) [CommRing R] (m : ℕ)
    (p q : FormalPolynomial R m) (α : Exponent m),
  coefficientEquivValue R m 0 α = 0 ∧
  coefficientEquivValue R m (p + q) α =
    coefficientEquivValue R m p α + coefficientEquivValue R m q α ∧
  coefficientEquivValue R m (-p) α = -coefficientEquivValue R m p α ∧
  coefficientEquivValue R m 1 α = if α = 0 then 1 else 0

def coefficientConvolution : Prop := ∀ (R : Type*) [CommRing R] (m : ℕ)
    (p q : FormalPolynomial R m) (γ : Exponent m),
  coefficientEquivValue R m (p * q) γ =
    ∑ ab ∈ exponentSplittings γ,
      coefficientEquivValue R m p ab.1 * coefficientEquivValue R m q ab.2

def coefficientRingLaws : Prop := ∀ (R : Type*) [CommRing R] (m : ℕ)
    (a b c : PolynomialCoefficients R m),
  (a + b) + c = a + (b + c) ∧ a + b = b + a ∧
  0 + a = a ∧ a + 0 = a ∧ -a + a = 0 ∧
  (a * b) * c = a * (b * c) ∧ a * b = b * a ∧
  1 * a = a ∧ a * 1 = a ∧
  a * (b + c) = a * b + a * c ∧ (a + b) * c = a * c + b * c

def familyOperations : Prop := ∀ (R : Type*) [CommRing R] (m : ℕ)
    (a b : PolynomialCoefficients R m) (γ : Exponent m),
  (a + b).coeff γ = a.coeff γ + b.coeff γ ∧
  (-a).coeff γ = -a.coeff γ ∧
  (1 : PolynomialCoefficients R m).coeff γ = (if γ = 0 then 1 else 0) ∧
  (a * b).coeff γ = ∑ ab ∈ exponentSplittings γ, a.coeff ab.1 * b.coeff ab.2

def zeroVariableEquivType := ∀ (R : Type*) [CommRing R], FormalPolynomial R 0 ≃+* R

def zeroVariableEquivValue : zeroVariableEquivType :=
  fun R _ => MvPolynomial.isEmptyRingEquiv R (Fin 0)

def zeroVariableCoefficients : Prop := ∀ (R : Type*) [CommRing R]
    (p : FormalPolynomial R 0),
  zeroVariableEquivValue R p = coefficientEquivValue R 0 p 0 ∧
  p = MvPolynomial.C (coefficientEquivValue R 0 p 0)

def singleVariableEquivType := ∀ (R : Type*) [CommRing R],
  FormalPolynomial R 1 ≃ₐ[R] Polynomial R

def singleVariableEquivValue : singleVariableEquivType :=
  fun R _ => MvPolynomial.uniqueAlgEquiv R (Fin 1)

def singleVariableCoefficients : Prop := ∀ (R : Type*) [CommRing R]
    (p : FormalPolynomial R 1) (n : ℕ),
  (singleVariableEquivValue R p).coeff n = coefficientEquivValue R 1 p (fun _ => n)

def univariateCoefficientEquivType := ∀ (R : Type*) [CommRing R],
  Polynomial R ≃ (ℕ →₀ R)

def univariateCoefficientEquivValue : univariateCoefficientEquivType := fun R _ =>
  (Polynomial.toFinsuppIso R).toEquiv.trans AddMonoidAlgebra.coeffEquiv

def univariateCoefficientBridge : Prop := ∀ (R : Type*) [CommRing R] (p : Polynomial R) (n : ℕ),
  univariateCoefficientEquivValue R p n = p.coeff n

/-- The nonzero hypotheses make natural degree the paper's nonzero degree. -/
def leadingTerms : Prop := ∀ (K : Type*) [Field K] (p q : Polynomial K),
  p ≠ 0 → q ≠ 0 →
  p * q ≠ 0 ∧
  (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff ∧
  (p * q).coeff (p.natDegree + q.natDegree) = p.leadingCoeff * q.leadingCoeff ∧
  (p * q).natDegree = p.natDegree + q.natDegree ∧
  (p * q).degree = p.degree + q.degree

def coordinateBasisType := ∀ (R : Type*) [CommRing R] (n : ℕ),
  Module.Basis (Fin n) R (CoordinateModule R n)

def coordinateBasisValue : coordinateBasisType := fun R _ n => Pi.basisFun R (Fin n)

def coordinateOperations : Prop := ∀ (R : Type*) [CommRing R] (n : ℕ)
    (v w : CoordinateModule R n) (r : R) (i : Fin n),
  (0 : CoordinateModule R n) i = 0 ∧
  (v + w) i = v i + w i ∧ (r • v) i = r * v i ∧
  coordinateBasisValue R n i = Pi.single i 1

def coordinateExpansion : Prop := ∀ (R : Type*) [CommRing R] (n : ℕ)
    (v : CoordinateModule R n),
  v = ∑ i : Fin n, v i • coordinateBasisValue R n i

end D05.Specs.FormalPolynomials
