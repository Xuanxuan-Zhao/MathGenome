import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.Algebra.Polynomial.Taylor

/-!
Independent statements for paper.tex:385–389. We use the same Mathlib formal
coefficient polynomials as the upstream interface. A bivariate polynomial is
`Polynomial (Polynomial K)`: the inner variable is x and the outer variable is h.
Thus `C X` denotes x, `X` denotes h, and `(f.map C).comp (C X + X)` denotes
f(x+h). These are identities of coefficient objects, including over finite fields.
The scalar `(j.factorial : K)⁻¹` is 1/j!, acting on the j-th formal derivative.
Algebras in the substitution statements may be noncommutative and may be zero;
only the two substituted elements are required to commute.
-/

noncomputable section

namespace D05.Specs.DifferentiationTaylor

open Polynomial

def productRule : Prop := ∀ (K : Type*) [Field K] (f g : Polynomial K),
  (f * g).derivative = f.derivative * g + f * g.derivative

def quadraticRemainder : Prop := ∀ (K : Type*) [Field K] (f : Polynomial K),
  ∃ R : Polynomial (Polynomial K),
    (f.map C).comp (C X + X) = C f + X * C f.derivative + X ^ 2 * R

/-- Natural degree is used only for the nonzero polynomial in this statement. -/
def finiteTaylor : Prop := ∀ (K : Type*) [Field K] [CharZero K]
    (f : Polynomial K), f ≠ 0 →
  (f.map C).comp (C X + X) =
    ∑ j ∈ Finset.range (f.natDegree + 1),
      C ((j.factorial : K)⁻¹ • ((derivative^[j]) f)) * X ^ j

/-- Explicit zero case, without assigning the paper's degree to the zero polynomial. -/
def zeroTaylor : Prop := ∀ (K : Type*) [Field K],
  (∀ j : ℕ, (derivative^[j]) (0 : Polynomial K) = 0) ∧
  (((0 : Polynomial K).map C).comp (C X + X) = 0) ∧
  (∑ j ∈ Finset.range 1,
    C ((j.factorial : K)⁻¹ • ((derivative^[j]) (0 : Polynomial K))) * X ^ j) =
      (0 : Polynomial (Polynomial K))

/-- The substitution is constructed, rather than assumed as a certificate. -/
def commutingSubstitution : Prop := ∀ (K A : Type*) [Field K] [Ring A] [Algebra K A]
    (x h : A), Commute x h →
  ∃ Φ : Polynomial (Polynomial K) →ₐ[K] A,
    (∀ P, Φ P = P.eval₂ (aeval x).toRingHom h) ∧
    (∀ p : Polynomial K, Φ (C p) = aeval x p) ∧
    Φ X = h ∧
    (∀ f : Polynomial K, Φ ((f.map C).comp (C X + X)) = aeval (x + h) f)

def evaluatedProductRule : Prop := ∀ (K A : Type*) [Field K] [Ring A] [Algebra K A]
    (f g : Polynomial K) (x : A),
  aeval x (f * g).derivative =
    aeval x f.derivative * aeval x g + aeval x f * aeval x g.derivative

/-- One formal remainder works for all commuting substitutions in all K-algebras. -/
def evaluatedQuadraticRemainder : Prop := ∀ (K : Type*) [Field K] (f : Polynomial K),
  ∃ R : Polynomial (Polynomial K),
    (f.map C).comp (C X + X) = C f + X * C f.derivative + X ^ 2 * R ∧
    ∀ (A : Type*) [Ring A] [Algebra K A] (x h : A), Commute x h →
      aeval (x + h) f = aeval x f + h * aeval x f.derivative +
        h ^ 2 * R.eval₂ (aeval x).toRingHom h

def evaluatedFiniteTaylor : Prop := ∀ (K A : Type*) [Field K] [CharZero K]
    [Ring A] [Algebra K A] (f : Polynomial K) (x h : A), Commute x h →
  aeval (x + h) f =
    ∑ j ∈ Finset.range (f.natDegree + 1),
      ((j.factorial : K)⁻¹ • aeval x ((derivative^[j]) f)) * h ^ j

end D05.Specs.DifferentiationTaylor
