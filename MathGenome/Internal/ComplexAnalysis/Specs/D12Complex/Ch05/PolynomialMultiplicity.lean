import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Algebra.Polynomial.Div

/-! Independent statements for paper.tex:1403–1417, D12.05.07.
The analytic multiplicity is the upstream local holomorphic zero order.
The algebraic multiplicity is the largest exponent of the single linear
factor X - C a dividing the polynomial. No splitting over ℂ is assumed.
The general comparison includes nonroots (order zero), but excludes the
zero polynomial, whose analytic germ has infinite order.
-/
noncomputable section
open Polynomial

namespace Specs.D12Complex.Ch05.PolynomialMultiplicity
open _root_.D12Complex
open Specs.D12Complex.Ch05.LocalZeroFactorization

def polynomial_holomorphic_type : Prop :=
  ∀ P : Polynomial ℂ, HolomorphicOn Set.univ (fun z => P.eval z)

/-- The bounded number of successive linear divisions leaves a nonzero
value at a, even when the original polynomial has other roots. -/
def polynomial_linear_factorization_type : Prop :=
  ∀ (P : Polynomial ℂ), P ≠ 0 → ∀ a : ℂ,
    P.rootMultiplicity a ≤ P.natDegree ∧
      ∃ Q : Polynomial ℂ,
        P = (X - C a) ^ P.rootMultiplicity a * Q ∧ Q.eval a ≠ 0

def polynomial_hasFiniteOrder_type : Prop :=
  ∀ (P : Polynomial ℂ), P ≠ 0 → ∀ a : ℂ,
    HasFiniteOrder_value (fun z => P.eval z) a (P.rootMultiplicity a)

def polynomial_order_eq_rootMultiplicity_type : Prop :=
  ∀ (P : Polynomial ℂ), P ≠ 0 → ∀ a : ℂ,
    order_value (fun z => P.eval z) a = (P.rootMultiplicity a : ℕ∞)

/-- In particular, no other local holomorphic factorization has a
nonvanishing remaining factor at a different exponent. -/
def polynomial_hasFiniteOrder_iff_type : Prop :=
  ∀ (P : Polynomial ℂ), P ≠ 0 → ∀ (a : ℂ) (m : ℕ),
    HasFiniteOrder_value (fun z => P.eval z) a m ↔ m = P.rootMultiplicity a

/-- The source assertion at a root, with positivity, largestness among
all algebraic exponents, and the degree bound for termination. -/
def polynomial_multiplicity_type : Prop :=
  ∀ (P : Polynomial ℂ), P ≠ 0 → ∀ a : ℂ, P.eval a = 0 →
    ∃ m : ℕ, 0 < m ∧
      HasFiniteOrder_value (fun z => P.eval z) a m ∧
      order_value (fun z => P.eval z) a = (m : ℕ∞) ∧
      IsGreatest {n : ℕ | (X - C a) ^ n ∣ P} m ∧ m ≤ P.natDegree

end Specs.D12Complex.Ch05.PolynomialMultiplicity
