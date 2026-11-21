import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.Specs.D07.Ch11.FieldPolynomialPid
import MathGenome.Internal.Specs.D07.Ch11.DegreeArithmetic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.Polynomial.Basis

/-!
Independent specification for K07.11.linear_algebra_bridge,
paper.tex:2876–2923. Endomorphism multiplication is composition, and
polynomials are formal polynomials, not polynomial functions. No
nonzero-space or finite-dimensional hypothesis is imposed on evaluation
or on the monic-generator theorem for a nonzero annihilator ideal.

`minpoly F T` is the element minimal polynomial in the canonical F-algebra
`Module.End F V`, so it uses exactly the operator evaluation map below.
It is zero when no nonzero annihilator exists; that default is not asserted
to be a monic minimal polynomial. `Polynomial F`, with monomial basis,
is the countably based space in the shift counterexample.
-/

noncomputable section
universe u v
namespace Specs.D07.Ch11.LinearAlgebraBridge
open Polynomial

variable (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]

/-- The central scalar homomorphism, including the zero endomorphism algebra. -/
abbrev scalarHom : F →+* Module.End F V := algebraMap F (Module.End F V)

/-- The canonical operator evaluation, with composition as multiplication. -/
abbrev evaluation (T : Module.End F V) : F[X] →ₐ[F] Module.End F V := aeval T

/-- An actual ideal, not an assumed ideal certificate. -/
def annihilator (T : Module.End F V) : Ideal F[X] :=
  RingHom.ker (evaluation F V T).toRingHom

abbrev minimalPolynomial (T : Module.End F V) : F[X] := minpoly F T

variable {F V}

def ScalarAction : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (a : F),
    scalarHom F V a = a • (1 : Module.End F V) ∧
    (∀ v, scalarHom F V a v = a • v) ∧ Commute T (scalarHom F V a)

def EvaluationUniversal : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V),
    (∀ a, evaluation F V T (C a) = scalarHom F V a) ∧
    evaluation F V T X = T ∧
    ∀ Φ : F[X] →+* Module.End F V,
      (∀ a, Φ (C a) = scalarHom F V a) → Φ X = T →
        Φ = (evaluation F V T).toRingHom

def EvaluationLaws : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (f g : F[X]),
    evaluation F V T (f * g) = evaluation F V T f * evaluation F V T g ∧
    evaluation F V T f = ∑ i ∈ f.support, scalarHom F V (f.coeff i) * T ^ i

def AnnihilatorCarrier : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (f : F[X]),
    f ∈ annihilator F V T ↔ evaluation F V T f = 0

def NonzeroAnnihilatorIffIntegral : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V), annihilator F V T ≠ ⊥ ↔ IsIntegral F T

def MinimalGenerator : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V), annihilator F V T ≠ ⊥ →
    (minimalPolynomial F V T).Monic ∧
    annihilator F V T = Ideal.span {minimalPolynomial F V T} ∧
    ∃! p : F[X], p.Monic ∧ annihilator F V T = Ideal.span {p}

def AnnihilationIffDivisibility : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (f : F[X]), annihilator F V T ≠ ⊥ →
    (evaluation F V T f = 0 ↔ minimalPolynomial F V T ∣ f)

def MinimalDegree : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (f : F[X]),
    f ≠ 0 → evaluation F V T f = 0 →
      (minimalPolynomial F V T).degree ≤ f.degree ∧
      (minimalPolynomial F V T).natDegree ≤ f.natDegree

def EndDimension : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V],
    Module.finrank F (Module.End F V) = (Module.finrank F V) ^ 2

def PowersDependent : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    ¬LinearIndependent F (fun j : Fin ((Module.finrank F V) ^ 2 + 1) => T ^ (j : ℕ))

def FiniteAnnihilator : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    annihilator F V T ≠ ⊥ ∧
    ∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ (Module.finrank F V) ^ 2 ∧
      evaluation F V T p = 0

def FiniteMinimalExists : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    (minimalPolynomial F V T).Monic ∧
      annihilator F V T = Ideal.span {minimalPolynomial F V T}

def CharpolyFormula : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (n : ℕ) (b : Module.Basis (Fin n) F V),
    T.charpoly = Matrix.det (Matrix.scalar (Fin n) (X : F[X]) -
      (LinearMap.toMatrix b b T).map C)

def CharpolyBasisIndependent : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (n m : ℕ)
    (b : Module.Basis (Fin n) F V) (c : Module.Basis (Fin m) F V),
    Matrix.det (Matrix.scalar (Fin n) (X : F[X]) - (LinearMap.toMatrix b b T).map C) =
    Matrix.det (Matrix.scalar (Fin m) (X : F[X]) - (LinearMap.toMatrix c c T).map C)

def CharpolyDegree : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    T.charpoly.Monic ∧ T.charpoly.degree = (Module.finrank F V : WithBot ℕ) ∧
      T.charpoly.natDegree = Module.finrank F V

def CayleyHamilton : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V), evaluation F V T T.charpoly = 0

def MinpolyCharpoly : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    minimalPolynomial F V T ∣ T.charpoly ∧
    (minimalPolynomial F V T).degree ≤ (Module.finrank F V : WithBot ℕ) ∧
    (minimalPolynomial F V T).natDegree ≤ Module.finrank F V

def ZeroSpace : Prop :=
  ∀ (F : Type u) (V : Type v) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V), Module.finrank F V = 0 →
    Subsingleton (Module.End F V) ∧ (1 : Module.End F V) = 0 ∧
    (∀ f, evaluation F V T f = 0) ∧ annihilator F V T = ⊤ ∧
    minimalPolynomial F V T = 1 ∧ T.charpoly = 1 ∧
    (minimalPolynomial F V T).degree = 0 ∧ T.charpoly.degree = 0

/-- Multiplication by X on the formal polynomial vector space is the right shift. -/
def shift (F : Type u) [Field F] : Module.End F F[X] := Algebra.lmul F F[X] X

def ShiftBasis : Prop :=
  ∀ (F : Type u) [Field F],
    (∀ i : ℕ, Polynomial.basisMonomials F i = (X : F[X]) ^ i) ∧
    (∀ i : ℕ, shift F (Polynomial.basisMonomials F i) = Polynomial.basisMonomials F (i + 1)) ∧
    ¬FiniteDimensional F F[X]

def ShiftEvaluation : Prop :=
  ∀ (F : Type u) [Field F] (f : F[X]),
    evaluation F F[X] (shift F) f (Polynomial.basisMonomials F 0) = f ∧
    evaluation F F[X] (shift F) f (Polynomial.basisMonomials F 0) =
      ∑ i ∈ f.support, f.coeff i • Polynomial.basisMonomials F i

def ShiftNoMinimalPolynomial : Prop :=
  ∀ (F : Type u) [Field F],
    (∀ f : F[X], f ≠ 0 →
      evaluation F F[X] (shift F) f (Polynomial.basisMonomials F 0) ≠ 0) ∧
    annihilator F F[X] (shift F) = ⊥ ∧
    ¬IsIntegral F (shift F) ∧
    ¬∃ p : F[X], p.Monic ∧ evaluation F F[X] (shift F) p = 0

end Specs.D07.Ch11.LinearAlgebraBridge
