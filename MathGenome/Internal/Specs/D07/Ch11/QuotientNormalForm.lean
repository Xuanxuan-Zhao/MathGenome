import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Basis

/-!
Independent statements for K07.11.quotient_normal_form, paper.tex:2776–2804.
The quotient is the canonical ideal quotient of formal polynomials. Its
canonical F-algebra structure acts by multiplication by constant classes.
No monicity or irreducibility is required for normal forms or finite dimension.
The bound uses bottom-valued degree, so zero is allowed even in degree zero.
-/

universe u

namespace Specs.D07.Ch11.QuotientNormalForm

open Polynomial Module

/-- Every class has exactly one polynomial representative below the divisor's degree. -/
def UniqueRepresentative : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 →
    ∀ x : Polynomial F ⧸ Ideal.span {f},
      ∃! r : Polynomial F,
        r.degree < f.degree ∧ Ideal.Quotient.mk (Ideal.span {f}) r = x

/-- The usual scalar action really is multiplication by constant classes. -/
def ScalarAction : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F) (a : F)
    (x : Polynomial F ⧸ Ideal.span {f}),
    a • x = Ideal.Quotient.mk (Ideal.span {f}) (C a) * x

/-- The classes of the first n powers of X form a basis, including Fin 0. -/
def QuotientBasis : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 →
    ∃ b : Basis (Fin f.natDegree) F (Polynomial F ⧸ Ideal.span {f}),
      ∀ i, b i = Ideal.Quotient.mk (Ideal.span {f}) (X ^ (i : ℕ))

/-- Finiteness is stated separately, since finrank alone defaults to zero in infinite dimension. -/
def QuotientDimension : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 →
    Module.Finite F (Polynomial F ⧸ Ideal.span {f}) ∧
      Module.finrank F (Polynomial F ⧸ Ideal.span {f}) = f.natDegree

/-- The cardinality assertion is restricted to finite coefficient fields and proves finiteness. -/
def FiniteCardinality : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (f : Polynomial F), f ≠ 0 →
    Finite (Polynomial F ⧸ Ideal.span {f}) ∧
      Nat.card (Polynomial F ⧸ Ideal.span {f}) = Nat.card F ^ f.natDegree

/-- For degree zero, the general power basis has empty index and the quotient has one element. -/
def DegreeZeroCase : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 → f.natDegree = 0 →
    Subsingleton (Polynomial F ⧸ Ideal.span {f}) ∧
      Nat.card (Polynomial F ⧸ Ideal.span {f}) = 1 ∧
      Nonempty (Basis (Fin 0) F (Polynomial F ⧸ Ideal.span {f}))

/-- Division by a nonzero constant has the zero polynomial as its sole normal form. -/
def ConstantCase : Prop :=
  ∀ (F : Type u) [Field F] (a : F), a ≠ 0 →
    ∀ x : Polynomial F ⧸ Ideal.span {C a},
      ∀ r : Polynomial F,
        (r.degree < (C a).degree ∧ Ideal.Quotient.mk (Ideal.span {C a}) r = x) ↔ r = 0

/-- Zero has no natural-valued degree; the quotient by zero is the polynomial
algebra, whose powers of X form an infinite basis, and which is not finite-dimensional. -/
def ZeroPolynomialCase : Prop :=
  ∀ (F : Type u) [Field F],
    (0 : Polynomial F).degree = ⊥ ∧
    (∀ n : ℕ, (0 : Polynomial F).degree ≠ (n : WithBot ℕ)) ∧
    (∃ e : (Polynomial F ⧸ Ideal.span {(0 : Polynomial F)}) ≃ₐ[F] Polynomial F,
      ∀ p, e (Ideal.Quotient.mk (Ideal.span {(0 : Polynomial F)}) p) = p) ∧
    (∃ b : Basis ℕ F (Polynomial F), ∀ i, b i = X ^ i) ∧
    ¬ Module.Finite F (Polynomial F) ∧
    ¬ Module.Finite F (Polynomial F ⧸ Ideal.span {(0 : Polynomial F)})

/-- Irreducibility adds the field property and an embedding of F, with the same extension degree. -/
def IrreducibleExtension : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), Irreducible f →
    IsField (Polynomial F ⧸ Ideal.span {f}) ∧
    Function.Injective (algebraMap F (Polynomial F ⧸ Ideal.span {f})) ∧
    Module.Finite F (Polynomial F ⧸ Ideal.span {f}) ∧
    Module.finrank F (Polynomial F ⧸ Ideal.span {f}) = f.natDegree

end Specs.D07.Ch11.QuotientNormalForm
