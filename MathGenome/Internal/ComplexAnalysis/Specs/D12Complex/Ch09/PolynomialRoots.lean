import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.PolynomialMultiplicity
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyFormula
import Mathlib.Algebra.BigOperators.Finprod

/-! Independent statements for the monic polynomial part of D12.09.04,
`paper.tex:2295–2300`. Counts use the actual local analytic zero order.
The finite sets below contain every zero in the indicated domain, with
no repetitions; their summands provide its multiplicity. The circle is
parametrized counterclockwise on [0, 2π] by the shared canonical path.
-/
noncomputable section
open Polynomial
open scoped BigOperators

namespace Specs.D12Complex.Ch09.PolynomialRoots

/-- Every monic polynomial has finite analytic order at every point, and
this order agrees with the algebraic multiplicity, including at nonroots. -/
def multiplicity_agrees_type : Prop :=
  ∀ (P : Polynomial ℂ), P.Monic → ∀ a : ℂ,
    Ch05.LocalZeroFactorization.HasFiniteOrder_value
      (fun z => P.eval z) a (P.rootMultiplicity a) ∧
    analyticOrderAt (fun z => P.eval z) a = (P.rootMultiplicity a : ℕ∞) ∧
    analyticOrderNatAt (fun z => P.eval z) a = P.rootMultiplicity a

/-- Total analytic and algebraic zero counts, on all of ℂ. Finite support
ensures that the global finite sum is an ordinary finite count. Degree zero
is included, so no positive-degree hypothesis occurs here. -/
def total_count_type : Prop :=
  ∀ (P : Polynomial ℂ), P.Monic →
    (Function.support (fun a => analyticOrderNatAt (fun z => P.eval z) a)).Finite ∧
    (∑ᶠ a : ℂ, analyticOrderNatAt (fun z => P.eval z) a) = P.natDegree ∧
    ∃ s : Finset ℂ,
      (∀ a, a ∈ s ↔ P.eval a = 0) ∧
      (∑ a ∈ s, analyticOrderNatAt (fun z => P.eval z) a) = P.natDegree ∧
      (∑ a ∈ s, P.rootMultiplicity a) = P.natDegree

/-- The stated quantitative radius, for every strict choice of R. -/
def roots_in_radius_type : Prop :=
  ∀ (P : Polynomial ℂ), P.Monic → 1 ≤ P.natDegree →
    ∀ R : ℝ, 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < R →
      ∀ a : ℂ, P.eval a = 0 → ‖a‖ < R

/-- The positive-circle zero count, both as an ordinary multiplicity sum
and as the normalized logarithmic-derivative contour integral. -/
def circle_count_type : Prop :=
  ∀ (P : Polynomial ℂ), P.Monic → 1 ≤ P.natDegree →
    ∀ R : ℝ, 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < R →
      (∀ a ∈ Metric.sphere (0 : ℂ) R, P.eval a ≠ 0) ∧
      (∃ s : Finset ℂ,
        (∀ a, a ∈ s ↔ a ∈ Metric.ball (0 : ℂ) R ∧ P.eval a = 0) ∧
        (∑ a ∈ s, analyticOrderNatAt (fun z => P.eval z) a) = P.natDegree ∧
        (∑ a ∈ s, P.rootMultiplicity a) = P.natDegree) ∧
      (Ch04.DiskCauchyFormula.circlePath_value 0 R).integral
        (fun z => deriv (fun w => P.eval w) z / P.eval z) /
          (2 * Real.pi * Complex.I : ℂ) = (P.natDegree : ℂ)

/-- The monic degree-zero polynomial is 1 and has no roots. -/
def degree_zero_type : Prop :=
  ∀ (P : Polynomial ℂ), P.Monic → P.natDegree = 0 →
    P = 1 ∧ (∀ a : ℂ, P.eval a ≠ 0) ∧
      (∑ᶠ a : ℂ, analyticOrderNatAt (fun z => P.eval z) a) = 0

end Specs.D12Complex.Ch09.PolynomialRoots
