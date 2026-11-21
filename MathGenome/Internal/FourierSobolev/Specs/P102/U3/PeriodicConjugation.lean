import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugationData
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugationKernel
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugationBound

/-! Independent interface for the periodic-conjugation part of paper.tex:1186–1200.
The canonical circle and probability Haar measure are inherited from Foundation.
There is no assumed periodic singular-integral estimate in this interface. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace P102.Periodic.Conjugation
open P102.Periodic.Expected

/-- Reuse the upstream range of finite exponents strictly greater than one. -/
abbrev Exponent := P102.U2.CZLpData.Exponent

variable (T : ℝ) [Fact (0 < T)]

abbrev Space (p : Exponent) := Lp ℂ p.val (haar T)
abbrev Operator (p : Exponent) := Space T p →L[ℂ] Space T p

/-- Send a continuous representative to the canonical probability-Haar Lp class. -/
abbrev toSpace (p : Exponent) : C(Circle T, ℂ) →L[ℂ] Space T p :=
  ContinuousMap.toLp p.val (haar T) ℂ

/-- Agreement is equality of actual Lp classes for every finite frequency set. -/
def AgreesOnPolynomials (p : Exponent) (H : Operator T p) : Prop :=
  ∀ c : ℤ →₀ ℂ, H (toSpace T p (synthesis T c)) =
    toSpace T p (polynomialAction T c)

/-- Compatibility with coefficient functionals on every Lp input. -/
def HasFourierSymbol (p : Exponent) (H : Operator T p) : Prop :=
  ∀ (f : Space T p) (n : ℤ), coefficient T (H f) n = symbol n * coefficient T f n

/-- Equivalent analytic estimate formulated entirely on finite multipliers. -/
def PolynomialBound (p : Exponent) : Prop :=
  ∃ C : ℝ≥0, ∀ c : ℤ →₀ ℂ,
    ‖toSpace T p (polynomialAction T c)‖ ≤
      (C : ℝ) * ‖toSpace T p (synthesis T c)‖

/-- Full original obligation: construction, finite operator bound, polynomial
action, coefficient action on every input, kernel identification, and uniqueness
among all bounded complex-linear operators agreeing on polynomials. -/
def Result (p : Exponent) : Prop :=
  ∃ (H : Operator T p) (C : ℝ≥0),
    ‖H‖ ≤ C ∧ AgreesOnPolynomials T p H ∧ HasFourierSymbol T p H ∧
    PolynomialPrincipalValues T ∧
    (∀ U : Operator T p, AgreesOnPolynomials T p U → U = H)

end P102.Periodic.Conjugation

namespace P102.Specs.U3.PeriodicConjugation
open P102.Periodic.Conjugation

def full_theorem : Prop := ∀ (T : ℝ) [Fact (0 < T)] (p : Exponent), Result T p

/-- Assembly interface for the two independent, unconditional child results. -/
def assemblyStatement : Prop :=
  (∀ (T : ℝ) [Fact (0 < T)], PolynomialPrincipalValues T) →
  (∀ (T : ℝ) [Fact (0 < T)] (p : Exponent), CancelledBound T p) →
  full_theorem

end P102.Specs.U3.PeriodicConjugation
