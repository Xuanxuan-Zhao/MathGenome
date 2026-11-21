import MathGenome.Internal.Specs.D05.Foundations.Division
import Mathlib.Data.Set.Card

/-!
Independent statements for the polynomial root argument used in
paper.tex:923–933 (Vandermonde), 1228–1231 (interpolation), and 3032–3035
(polynomial functions). The polynomials are the same formal coefficient objects
as in the division interface. No infinitude or characteristic assumption on the
field is imposed. Finsets encode distinct scalar roots, not multiplicities.
-/

namespace D05.Specs.RootBound

open Polynomial

/-- The factor theorem includes the zero polynomial. -/
def factorTheorem : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K) (a : K),
    p.eval a = 0 ↔ X - C a ∣ p

/-- Division at a root removes one linear factor, preserves every other root,
and decreases the degree by one when the dividend is nonzero. -/
def divisionAtRoot : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K) (a : K), p.eval a = 0 →
    ∃ q : Polynomial K,
      p = (X - C a) * q ∧
      (∀ b : K, b ≠ a → (q.eval b = 0 ↔ p.eval b = 0)) ∧
      (p ≠ 0 → q ≠ 0 ∧ q.natDegree + 1 = p.natDegree)

/-- Repeated division by the linear factors at any finite set of distinct
roots. The empty set and zero dividend are included. -/
def repeatedDivision : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K) (s : Finset K),
    (∀ a ∈ s, p.eval a = 0) →
    ∃ q : Polynomial K,
      p = (∏ a ∈ s, (X - C a)) * q ∧
      (p ≠ 0 → q ≠ 0 ∧ s.card + q.natDegree = p.natDegree)

/-- Any finite set of distinct roots of a nonzero degree-d polynomial has
cardinality at most d, including nonzero constants (d = 0). -/
def distinctRootBound : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K), p ≠ 0 →
    ∀ s : Finset K, (∀ a ∈ s, p.eval a = 0) → s.card ≤ p.natDegree

/-- The full set of scalar roots is finite and has at most d elements. The
explicit finiteness assertion prevents `Set.ncard`'s infinite-set convention
from weakening the conclusion. -/
def rootSetBound : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K), p ≠ 0 →
    Set.Finite {a : K | p.eval a = 0} ∧
      Set.ncard {a : K | p.eval a = 0} ≤ p.natDegree

end D05.Specs.RootBound
