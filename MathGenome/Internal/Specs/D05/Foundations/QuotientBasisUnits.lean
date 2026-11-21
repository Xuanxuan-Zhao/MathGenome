import Mathlib.RingTheory.AdjoinRoot
import MathGenome.Internal.Specs.D05.Foundations.IdealsGcd
import MathGenome.Internal.Specs.D05.M02.Basis

/-! Independent statements for paper.tex:383. `AdjoinRoot q` is, by definition,
the quotient of the formal polynomial ring by `Ideal.span {q}`. Its scalar
action is the quotient action, not an arbitrarily chosen coordinate action.
Polynomial degree takes values in `WithBot ℕ`, so the zero representative has
degree below every nonzero constant polynomial. No positive degree is assumed.
-/

namespace D05.Specs.QuotientBasisUnits

/-- Every residue class has exactly one representative of degree below that
of the monic modulus, including modulus one. -/
def uniqueRepresentative : Prop :=
  ∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic →
    ∀ z : AdjoinRoot q, ∃! r : Polynomial K,
      r.degree < q.degree ∧ AdjoinRoot.mk q r = z

/-- The specified residue classes, with their original exponents and quotient
scalar action, form a basis indexed by the degree of the modulus. -/
def residueBasis : Prop :=
  ∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic →
    ∃ b : Module.Basis (Fin q.natDegree) K (AdjoinRoot q),
      ∀ i, b i = AdjoinRoot.mk q (Polynomial.X ^ (i : ℕ))

/-- The gcd is the shared monic normalization, not an arbitrary associate.
The criterion applies to every polynomial representative. -/
def isUnit_iff_gcd_eq_one : Prop :=
  ∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic →
    ∀ f : Polynomial K,
      IsUnit (AdjoinRoot.mk q f) ↔ D05.Foundations.monicGcd f q = 1

/-- A monic irreducible modulus yields a field. `IsField` asserts the field
properties of the existing quotient ring and includes nontriviality. -/
def irreducibleQuotientIsField : Prop :=
  ∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic →
    Irreducible q → IsField (AdjoinRoot q)

/-- Explicit boundary case: modulus one has degree zero, zero quotient, and
an empty basis. The zero ring is not a field. -/
def constantOneQuotient : Prop :=
  ∀ (K : Type*) [Field K],
    (1 : Polynomial K).natDegree = 0 ∧
    Subsingleton (AdjoinRoot (1 : Polynomial K)) ∧
    ¬ IsField (AdjoinRoot (1 : Polynomial K)) ∧
    ∃ b : Module.Basis (Fin 0) K (AdjoinRoot (1 : Polynomial K)),
      ∀ i, b i = AdjoinRoot.mk (1 : Polynomial K) (Polynomial.X ^ (i : ℕ))

end D05.Specs.QuotientBasisUnits
