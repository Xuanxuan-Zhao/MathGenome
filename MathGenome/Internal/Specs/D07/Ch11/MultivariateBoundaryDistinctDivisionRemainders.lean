import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Span

/-!
Independent specification for the division counterexample in
K07.11.multivariate_boundary, paper.tex:2860–2872.

The variables are formal, commuting indeterminates, indexed by `Fin 2`.
Mathlib's lexicographic order compares coordinate 0 first, so X > Y.
Exponent inequalities in `Terminal` are coordinatewise: these express
monomial divisibility, rather than comparison in the lexicographic order.
No general multivariate division or uniqueness theorem is assumed.
-/

universe u

noncomputable section

namespace Specs.D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders

open MvPolynomial
open scoped MonomialOrder

abbrev x (F : Type u) [Field F] : MvPolynomial (Fin 2) F := X 0
abbrev y (F : Type u) [Field F] : MvPolynomial (Fin 2) F := X 1

def g₁ (F : Type u) [Field F] : MvPolynomial (Fin 2) F := x F * y F - 1
def g₂ (F : Type u) [Field F] : MvPolynomial (Fin 2) F := y F ^ 2 - 1
def dividend (F : Type u) [Field F] : MvPolynomial (Fin 2) F := x F * y F ^ 2

noncomputable def lexOrder : MonomialOrder (Fin 2) := MonomialOrder.lex

/-- No monomial of the remainder is divisible by either leading monomial. -/
def Terminal {F : Type u} [Field F] (r : MvPolynomial (Fin 2) F) : Prop :=
  ∀ e ∈ r.support,
    ¬ lexOrder.degree (g₁ F) ≤ e ∧ ¬ lexOrder.degree (g₂ F) ≤ e

/-- A single division step cancels the current leading term by a monomial
multiple of the specified divisor. The exponent and coefficient equations
ensure that the subtracted multiple has exactly that leading term. -/
def LeadingCancellation {F : Type u} [Field F]
    (g p r : MvPolynomial (Fin 2) F) : Prop :=
  lexOrder.leadingCoeff g ≠ 0 ∧
    ∃ (d : Fin 2 →₀ ℕ) (c : F), c ≠ 0 ∧
      d + lexOrder.degree g = lexOrder.degree p ∧
      c * lexOrder.leadingCoeff g = lexOrder.leadingCoeff p ∧
      r = p - monomial d c * g

/-- A terminal remainder obtainable in one permitted cancellation, choosing
either member of the divisor list `[g₁, g₂]`. -/
def OneStepTerminalRemainder {F : Type u} [Field F]
    (p r : MvPolynomial (Fin 2) F) : Prop :=
  (LeadingCancellation (g₁ F) p r ∨ LeadingCancellation (g₂ F) p r) ∧ Terminal r

def LexVariableOrder : Prop :=
  Finsupp.single (1 : Fin 2) 1 ≺[lexOrder] Finsupp.single (0 : Fin 2) 1

/-- Leading monomials and their coefficients for the two actual divisors. -/
def LeadingMonomials : Prop :=
  ∀ (F : Type u) [Field F],
    lexOrder.degree (g₁ F) = Finsupp.single 0 1 + Finsupp.single 1 1 ∧
    lexOrder.degree (g₂ F) = Finsupp.single 1 2 ∧
    lexOrder.leadingCoeff (g₁ F) = 1 ∧ lexOrder.leadingCoeff (g₂ F) = 1

def CancellationIdentities : Prop :=
  ∀ (F : Type u) [Field F],
    dividend F - y F * g₁ F = y F ∧ dividend F - x F * g₂ F = x F

def TerminalRemainders : Prop :=
  ∀ (F : Type u) [Field F], Terminal (x F) ∧ Terminal (y F) ∧ x F ≠ y F

def IdealDifference : Prop :=
  ∀ (F : Type u) [Field F],
    x F - y F = y F * g₁ F - x F * g₂ F ∧
    x F - y F ∈ Ideal.span ({g₁ F, g₂ F} : Set (MvPolynomial (Fin 2) F))

/-- Both displayed equations are actual leading-term cancellation steps. -/
def DivisionSteps : Prop :=
  ∀ (F : Type u) [Field F],
    LeadingCancellation (g₁ F) (dividend F) (y F) ∧
    LeadingCancellation (g₂ F) (dividend F) (x F)

/-- Thus the same dividend and divisor list admit distinct terminal remainders. -/
def DistinctDivisionRemainders : Prop :=
  ∀ (F : Type u) [Field F],
    ∃ r s : MvPolynomial (Fin 2) F,
      OneStepTerminalRemainder (dividend F) r ∧
      OneStepTerminalRemainder (dividend F) s ∧ r ≠ s

end Specs.D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders
