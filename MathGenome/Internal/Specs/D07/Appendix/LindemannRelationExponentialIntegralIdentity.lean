import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Independent specification of the analytic identity in the special Lindemann
relation, paper.tex:7744–7762 (pi-transcendence.tex, proof of
`lem:lindemann-special-relation`). The degree bound may exceed the degree;
the zero polynomial and N = 0 are included. All integrals are complex-valued
integrals over a real interval, with real parameter t and its canonical cast
into ℂ. Fin m indexes a finite list and retains repeated entries.
-/

noncomputable section

namespace Specs.D07.Appendix.LindemannRelationExponentialIntegralIdentity

open Polynomial
open scoped BigOperators

/-- The polynomial F = f + f' + ⋯ + f^(N), with formal derivatives. -/
def derivativeSum (f : Polynomial ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ r ∈ Finset.range (N + 1), Polynomial.derivative^[r] f

def DerivativeSumType := Polynomial ℂ → ℕ → Polynomial ℂ

def derivativeSumValue : DerivativeSumType := derivativeSum

/-- Polynomial identity, before evaluation at any complex number. -/
def TelescopingIdentity : Prop :=
  ∀ (f : Polynomial ℂ) (N : ℕ), f.natDegree ≤ N →
    (derivativeSum f N).derivative - derivativeSum f N = -f

/-- Real differentiation along the segment used in the manuscript. -/
def SegmentDerivative : Prop :=
  ∀ (f : Polynomial ℂ) (N : ℕ), f.natDegree ≤ N → ∀ (β : ℂ) (t : ℝ),
    HasDerivAt
      (fun x : ℝ => Complex.exp (-((x : ℂ) * β)) *
        (derivativeSum f N).eval ((x : ℂ) * β))
      (-β * Complex.exp (-((t : ℂ) * β)) * f.eval ((t : ℂ) * β)) t

/-- The exponential integral identity for every complex endpoint β. -/
def ExponentialIntegralIdentity : Prop :=
  ∀ (f : Polynomial ℂ) (N : ℕ), f.natDegree ≤ N → ∀ β : ℂ,
    Complex.exp β * (derivativeSum f N).eval 0 - (derivativeSum f N).eval β =
      β * ∫ t : ℝ in 0..1,
        Complex.exp ((1 - (t : ℂ)) * β) * f.eval ((t : ℂ) * β)

/-- Summing the identity under the assumed exponential relation. No
nonzero-root, rational-coefficient, or positivity condition is needed here. -/
def SummedExponentialIntegralIdentity : Prop :=
  ∀ (f : Polynomial ℂ) (N : ℕ), f.natDegree ≤ N →
    ∀ (m : ℕ) (β : Fin m → ℂ) (k : ℕ),
    (k : ℂ) + ∑ j, Complex.exp (β j) = 0 →
    -((k : ℂ) * (derivativeSum f N).eval 0 +
        ∑ j, (derivativeSum f N).eval (β j)) =
      ∑ j, β j * ∫ t : ℝ in 0..1,
        Complex.exp ((1 - (t : ℂ)) * β j) * f.eval ((t : ℂ) * β j)

end Specs.D07.Appendix.LindemannRelationExponentialIntegralIdentity
