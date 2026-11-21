import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Independent definitions for paper.tex, Definition d13:09:indicial.
The coefficient functions are ambient functions, with holomorphy required only
on the stated open disc. The cut and the logarithm are retained as data.
No existence of a Frobenius solution is assumed here. -/

noncomputable section

namespace Specs.D13Unified.Ch09.Indicial

/-- The regular-singular equation is `z² y'' + z p(z) y' + q(z) y = 0`.
The positive radius and both complex holomorphy hypotheses are part of its data. -/
structure Equation where
  radius : ℝ
  radius_pos : 0 < radius
  p : ℂ → ℂ
  q : ℂ → ℂ
  p_holomorphic : DifferentiableOn ℂ p (Metric.ball 0 radius)
  q_holomorphic : DifferentiableOn ℂ q (Metric.ball 0 radius)

/-- Rotation by `angle`; its inverse is rotation by `-angle`. -/
def rotation (angle : ℝ) : ℂ ≃ₜ ℂ :=
  Homeomorph.mulLeft₀ (Complex.exp ((angle : ℂ) * Complex.I)) (Complex.exp_ne_zero _)

/-- The radius-`R` disc with zero and the rotated negative real ray removed.
In particular angle zero gives the usual principal slit disc. -/
def slitDiscValue (R angle : ℝ) : Set ℂ :=
  rotation angle '' (Metric.ball 0 R ∩ Complex.slitPlane)

/-- A freely chosen holomorphic logarithm on the *specified* slit disc.
The exponential identity is the defining property of a logarithm branch,
not an assumption about a solution of the differential equation. -/
structure LogBranch (R : ℝ) where
  angle : ℝ
  log : ℂ → ℂ
  holomorphic : DifferentiableOn ℂ log (slitDiscValue R angle)
  exp_log : ∀ z ∈ slitDiscValue R angle, Complex.exp (log z) = z

/-- Canonical Taylor coefficient at zero. -/
def taylorCoefficientValue (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

def pZeroValue (E : Equation) : ℂ := taylorCoefficientValue E.p 0

def qZeroValue (E : Equation) : ℂ := taylorCoefficientValue E.q 0

/-- An actual polynomial in `ℂ[X]`, not only a suggestively named function. -/
def indicialPolynomialValue (E : Equation) : Polynomial ℂ :=
  Polynomial.X * (Polynomial.X - 1) +
    Polynomial.C (pZeroValue E) * Polynomial.X + Polynomial.C (qZeroValue E)

/-- Evaluation form used in the Frobenius recurrence. -/
def indicialValue (E : Equation) (r : ℂ) : ℂ :=
  r * (r - 1) + pZeroValue E * r + qZeroValue E

/-- `z^r` on a specified branch. Values off its slit disc are irrelevant;
solution and independence predicates below always retain that disc. -/
def powerValue {R : ℝ} (b : LogBranch R) (r z : ℂ) : ℂ :=
  Complex.exp (r * b.log z)

/-- Classical holomorphic solution on the chosen branch domain. -/
def solutionValue (E : Equation) (b : LogBranch E.radius) (y : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ y (slitDiscValue E.radius b.angle) ∧
  DifferentiableOn ℂ (deriv y) (slitDiscValue E.radius b.angle) ∧
  ∀ z ∈ slitDiscValue E.radius b.angle,
    z ^ 2 * deriv (deriv y) z + z * E.p z * deriv y z + E.q z * y z = 0

/-- Independence means independence of restrictions to this actual domain. -/
def independentValue {R : ℝ} (b : LogBranch R) (y₁ y₂ : ℂ → ℂ) : Prop :=
  ∀ c₁ c₂ : ℂ,
    (∀ z ∈ slitDiscValue R b.angle, c₁ * y₁ z + c₂ * y₂ z = 0) →
    c₁ = 0 ∧ c₂ = 0

/-- Formula for an explicit branch; arbitrary branches remain allowed. -/
def principalBranchExpected (angle : ℝ) : ℂ → ℂ :=
  fun z => (angle : ℂ) * Complex.I + Complex.log ((rotation angle).symm z)

def taylorCoefficientType := (ℂ → ℂ) → ℕ → ℂ
def pZeroType := Equation → ℂ
def qZeroType := Equation → ℂ
def indicialPolynomialType := Equation → Polynomial ℂ
def indicialType := Equation → ℂ → ℂ
def slitDiscType := ℝ → ℝ → Set ℂ
def powerType := {R : ℝ} → LogBranch R → ℂ → ℂ → ℂ
def solutionType := (E : Equation) → LogBranch E.radius → (ℂ → ℂ) → Prop
def independentType := {R : ℝ} → LogBranch R → (ℂ → ℂ) → (ℂ → ℂ) → Prop

/-- The full defining identities and geometry, with no solution existence
or independence conclusion smuggled into the assumptions. -/
def setupType : Prop :=
  (∀ E : Equation, pZeroValue E = E.p 0 ∧ qZeroValue E = E.q 0) ∧
  (∀ (E : Equation) (r : ℂ),
    (indicialPolynomialValue E).eval r = indicialValue E r) ∧
  (∀ (R angle : ℝ), 0 < R →
    IsOpen (slitDiscValue R angle) ∧ IsSimplyConnected (slitDiscValue R angle) ∧
    slitDiscValue R angle ⊆ Metric.ball 0 R ∧
    (∀ z ∈ slitDiscValue R angle, z ≠ 0)) ∧
  (∀ (R : ℝ) (b : LogBranch R) (r : ℂ),
    DifferentiableOn ℂ (powerValue b r) (slitDiscValue R b.angle) ∧
    ∀ z ∈ slitDiscValue R b.angle, powerValue b r z ≠ 0)

/-- Certify that the named Taylor coefficients really expand the coefficients. -/
def coefficientExpansionType : Prop :=
  ∀ (E : Equation) (z : ℂ), z ∈ Metric.ball 0 E.radius →
    HasSum (fun n => taylorCoefficientValue E.p n * z ^ n) (E.p z) ∧
    HasSum (fun n => taylorCoefficientValue E.q n * z ^ n) (E.q z)

/-- Exact branch formula for the explicitly constructed branch. -/
def branchExistsType : Prop :=
  ∀ R angle, ∃ b : LogBranch R,
    b.angle = angle ∧ b.log = principalBranchExpected angle

end Specs.D13Unified.Ch09.Indicial
