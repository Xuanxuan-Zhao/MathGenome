import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.Basic.Real.Basic

/-!
Independent statements for the counterexample in paper.tex:3226–3228.
The plane is the standard real coordinate module, and polynomial representations
use formal multivariate polynomials, with an explicit evaluation map.
-/

noncomputable section

namespace D05.Specs.PolynomialPolarization.HomogeneityExample

open D05.Foundations

/-- The function is explicitly assigned zero at the origin. -/
def qType := CoordinateModule ℝ 2 → ℝ

def qValue : qType := fun v =>
  if v = 0 then 0 else v 0 ^ 4 / (v 0 ^ 2 + v 1 ^ 2)

def formula : Prop := ∀ v : CoordinateModule ℝ 2,
  qValue v = v 0 ^ 4 / (v 0 ^ 2 + v 1 ^ 2)

def atOrigin : Prop := qValue 0 = 0

/-- All real scalars, including zero and negative scalars, are quantified. -/
def homogeneity : Prop := ∀ (t : ℝ) (v : CoordinateModule ℝ 2),
  qValue (t • v) = t ^ 2 * qValue v

def sampleValues : Prop :=
  qValue ![1, 0] = 1 ∧ qValue ![0, 1] = 0 ∧
  qValue ![1, 1] = 1 / 2 ∧ qValue ![1, -1] = 1 / 2

/-- The three possible coefficients of a homogeneous quadratic cannot work. -/
def notQuadraticExpression : Prop :=
  ¬ ∃ a b c : ℝ, ∀ v : CoordinateModule ℝ 2,
    qValue v = a * v 0 ^ 2 + b * v 0 * v 1 + c * v 1 ^ 2

/-- A stronger conclusion: there is no formal polynomial of any degree
whose evaluation is this function. In particular there is no quadratic one. -/
def notPolynomial : Prop :=
  ¬ ∃ p : FormalPolynomial ℝ 2, ∀ v : CoordinateModule ℝ 2,
    MvPolynomial.eval v p = qValue v

end D05.Specs.PolynomialPolarization.HomogeneityExample
