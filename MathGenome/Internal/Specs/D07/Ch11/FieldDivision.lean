import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
Independent specification of K07.11.field_division
(paper.tex:2349–2361; chapters/M07.11.tex:204–216).

These are the canonical formal polynomials, not polynomial functions.
`Field` includes commutativity and nontriviality. Degree takes values in
`WithBot ℕ`, with degree zero polynomial equal to bottom. Every assertion
about division explicitly excludes the zero divisor polynomial.
-/

universe u

namespace Specs.D07.Ch11.FieldDivision

open Polynomial

/-- Joint existence and uniqueness of the quotient and remainder. -/
def UniqueFieldDivision : Prop :=
  ∀ (F : Type u) [Field F] (f g : Polynomial F), g ≠ 0 →
    ∃! qr : Polynomial F × Polynomial F,
      f = qr.1 * g + qr.2 ∧ (qr.2 = 0 ∨ qr.2.degree < g.degree)

/-- The term added to the quotient in a single leading-term cancellation.
Its coefficient uses only division in the coefficient field. -/
noncomputable def cancellationTerm {F : Type u} [Field F]
    (p g : Polynomial F) : Polynomial F :=
  C (p.leadingCoeff / g.leadingCoeff) * X ^ (p.natDegree - g.natDegree)

/-- A legal cancellation strictly lowers the bottom-valued degree. -/
def LeadingTermCancellation : Prop :=
  ∀ (F : Type u) [Field F] (p g : Polynomial F),
    g ≠ 0 → p ≠ 0 → g.degree ≤ p.degree →
      (p - cancellationTerm p g * g).degree < p.degree

/-- A finite run of long division, indexed by the number of cancellations.
The stopping test and the actual field-operation update are specified here;
existence of a terminating run and its correctness are obligations below. -/
inductive DivisionSteps {F : Type u} [Field F] (g : Polynomial F) :
    ℕ → Polynomial F → Polynomial F → Polynomial F → Prop
  | stop {p : Polynomial F} (h : p = 0 ∨ p.degree < g.degree) :
      DivisionSteps g 0 p 0 p
  | cancel {n : ℕ} {p q r : Polynomial F}
      (hp : p ≠ 0) (hdeg : g.degree ≤ p.degree)
      (next : DivisionSteps g n (p - cancellationTerm p g * g) q r) :
      DivisionSteps g (n + 1) p (cancellationTerm p g + q) r

/-- Repeated cancellation terminates and returns a correct division pair. -/
def TerminatingDivisionAlgorithm : Prop :=
  ∀ (F : Type u) [Field F] (f g : Polynomial F), g ≠ 0 →
    ∃ (n : ℕ) (q r : Polynomial F), DivisionSteps g n f q r ∧
      f = q * g + r ∧ (r = 0 ∨ r.degree < g.degree)

/-- For any division pair for a nonzero constant, the remainder vanishes.
The quotient is multiplication by the inverse constant. -/
def NonzeroConstantDivision : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F) (a : F), a ≠ 0 →
    ∀ (q r : Polynomial F),
      f = q * C a + r → (r = 0 ∨ r.degree < (C a).degree) →
        r = 0 ∧ q = f * C a⁻¹

end Specs.D07.Ch11.FieldDivision
