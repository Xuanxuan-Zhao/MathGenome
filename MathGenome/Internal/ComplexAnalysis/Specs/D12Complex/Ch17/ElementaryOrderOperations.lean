import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.OrderDivisorDefinitions

/-! Growth bridges in paper.tex:3092–3116. All orders and maxima are the
canonical, clipped log-log quantities from OrderDivisorDefinitions. -/
noncomputable section
open Filter
open scoped Topology ENNReal
namespace Specs.D12Complex.Ch17.ElementaryOrderOperations
open _root_.D12Complex _root_.D12Complex.OrderDivisorDefinitions
open Specs.D12Complex.Ch17.OrderDivisorDefinitions

/-- Nonconstant entire functions have maximum modulus tending to infinity. -/
def maximumModulus_tendsto_atTop_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn Set.univ f →
    (¬ ∃ c : ℂ, ∀ z, f z = c) → Tendsto (maximumModulus_value f) atTop atTop

/-- Both maxima in the translation argument diverge. -/
def translated_maxima_tendsto_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicOn Set.univ f →
    (¬ ∃ c : ℂ, ∀ z, f z = c) →
    Tendsto (maximumModulus_value f) atTop atTop ∧
    Tendsto (maximumModulus_value (fun z => f z - a)) atTop atTop

def order_sub_const_type : Prop :=
  ∀ (f g : NonzeroEntireFunction) (a : ℂ),
    (¬ ∃ c : ℂ, ∀ z, f.toFun z = c) →
    g.toFun = (fun z => f.toFun z - a) → order_value g = order_value f

/-- Every allowed translate has an order-bearing nonzero entire representative;
this also makes the quantified applicability of order_sub_const explicit. -/
def translated_order_type : Prop :=
  ∀ (f : NonzeroEntireFunction) (a : ℂ),
    (¬ ∃ c : ℂ, ∀ z, f.toFun z = c) →
    ∃ g : NonzeroEntireFunction,
      g.toFun = (fun z => f.toFun z - a) ∧ order_value g = order_value f

/-- The polynomial-exponential expression is an actual nonzero entire function. -/
def polynomial_exp_exists_type : Prop :=
  ∀ (A Q : Polynomial ℂ), A ≠ 0 → ∃ f : NonzeroEntireFunction,
    f.toFun = (fun z => A.eval z * Complex.exp (Q.eval z))

/-- Upper bound for the logarithm of the maximum, with positive exponent degree. -/
def polynomial_exp_upper_type : Prop :=
  ∀ (A Q : Polynomial ℂ), A ≠ 0 → 0 < Q.natDegree →
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∀ r ≥ R,
      Real.log (max (Real.exp 1)
        (maximumModulus_value (fun z => A.eval z * Complex.exp (Q.eval z)) r)) ≤
          C * r ^ Q.natDegree

/-- A ray on which the leading exponential term is positive gives the lower
bound, including the polynomial prefactor's logarithmic growth. -/
def polynomial_exp_ray_lower_type : Prop :=
  ∀ (A Q : Polynomial ℂ), A ≠ 0 → 0 < Q.natDegree →
    ∃ u : ℂ, ‖u‖ = 1 ∧
      Q.leadingCoeff * u ^ Q.natDegree = (‖Q.leadingCoeff‖ : ℂ) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ R : ℝ,
      0 < R ∧ ∀ r ≥ R,
        c * r ^ Q.natDegree + (A.natDegree : ℝ) * Real.log r - C ≤
          Real.log ‖A.eval ((r : ℂ) * u) * Complex.exp (Q.eval ((r : ℂ) * u))‖

/-- Exact order; natDegree is zero for constant polynomials, including Q=0. -/
def polynomial_exp_order_type : Prop :=
  ∀ (A Q : Polynomial ℂ) (f : NonzeroEntireFunction), A ≠ 0 →
    f.toFun = (fun z => A.eval z * Complex.exp (Q.eval z)) →
      order_value f = (Q.natDegree : ℝ≥0∞)

end Specs.D12Complex.Ch17.ElementaryOrderOperations
