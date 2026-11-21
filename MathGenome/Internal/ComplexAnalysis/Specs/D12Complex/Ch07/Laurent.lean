import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent interface for paper.tex:1616–1667 (D12.07.01).
The outer radius is extended, including ∞. The finite inner radius may be zero.
Integer powers are ordinary field powers. Positive and strictly negative terms
are summed separately; no symmetric summation convention is used.
-/
noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace D12Complex.Laurent

/-- The open annulus; the point a is excluded also when r₀ = 0. -/
def annulus (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞) : Set ℂ :=
  {z | r₀ < ‖z - a‖ ∧ (‖z - a‖₊ : ℝ≥0∞) < R₀}

def closedSubannulus (a : ℂ) (s t : ℝ) : Set ℂ :=
  {z | s ≤ ‖z - a‖ ∧ ‖z - a‖ ≤ t}

/-- Counterclockwise circle integral, normalized by (2πi)⁻¹. -/
def coefficientIntegral (f : ℂ → ℂ) (a : ℂ) (ρ : ℝ) (n : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    circleIntegral (fun w => f w / (w - a) ^ (n + 1)) a ρ

def positiveTerm (c : ℤ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  c (n : ℤ) * (z - a) ^ n

def negativeTerm (c : ℤ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  c (-(n : ℤ) - 1) * (z - a) ^ (-(n : ℤ) - 1)

def positivePart (c : ℤ → ℂ) (a z : ℂ) : ℂ := ∑' n, positiveTerm c a n z

def negativePart (c : ℤ → ℂ) (a z : ℂ) : ℂ := ∑' n, negativeTerm c a n z

/-- A summable representation by the two one-sided sums. The uniqueness
assertion uses the weaker ordinary convergence predicate below. -/
def HasLaurentSeriesOn (f : ℂ → ℂ) (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞)
    (c : ℤ → ℂ) : Prop :=
  ∀ z ∈ annulus a r₀ R₀,
    Summable (fun n => positiveTerm c a n z) ∧
    Summable (fun n => negativeTerm c a n z) ∧
    f z = positivePart c a z + negativePart c a z

/-- Ordinary convergence of the two sequences of partial sums. This is the
competitor predicate for uniqueness: neither absolute nor uniform convergence
nor the coefficient formula is assumed. -/
def ConvergentLaurentSeriesOn (f : ℂ → ℂ) (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞)
    (c : ℤ → ℂ) : Prop :=
  ∀ z ∈ annulus a r₀ R₀, ∃ p q : ℂ,
    Tendsto (fun N => ∑ n ∈ Finset.range N, positiveTerm c a n z) atTop (𝓝 p) ∧
    Tendsto (fun N => ∑ n ∈ Finset.range N, negativeTerm c a n z) atTop (𝓝 q) ∧
    f z = p + q

/-- Uniform convergence of the series and of its series of absolute values,
together with pointwise absolute summability on the whole set. -/
def AbsoluteUniformSeriesOn (u : ℕ → ℂ → ℂ) (K : Set ℂ) : Prop :=
  (∀ z ∈ K, Summable (fun n => ‖u n z‖)) ∧
  TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, u n z)
    (fun z => ∑' n, u n z) atTop K ∧
  TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, ‖u n z‖)
    (fun z => ∑' n, ‖u n z‖) atTop K

/-- The derivative terms are the actual derivatives of individual monomials. -/
def derivativePositiveTerm (c : ℤ → ℂ) (a : ℂ) (k n : ℕ) : ℂ → ℂ :=
  iteratedDeriv k (positiveTerm c a n)

def derivativeNegativeTerm (c : ℤ → ℂ) (a : ℂ) (k n : ℕ) : ℂ → ℂ :=
  iteratedDeriv k (negativeTerm c a n)

/-- Each one-sided sum may be differentiated k times, and so may their sum f. -/
def TermwiseDerivativesOn (f : ℂ → ℂ) (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞)
    (c : ℤ → ℂ) : Prop :=
  ∀ k : ℕ, ∀ z ∈ annulus a r₀ R₀,
    DifferentiableAt ℂ (iteratedDeriv k (positivePart c a)) z ∧
    DifferentiableAt ℂ (iteratedDeriv k (negativePart c a)) z ∧
    DifferentiableAt ℂ (iteratedDeriv k f) z ∧
    Summable (fun n => derivativePositiveTerm c a k n z) ∧
    Summable (fun n => derivativeNegativeTerm c a k n z) ∧
    iteratedDeriv k (positivePart c a) z = ∑' n, derivativePositiveTerm c a k n z ∧
    iteratedDeriv k (negativePart c a) z = ∑' n, derivativeNegativeTerm c a k n z ∧
    iteratedDeriv k f z =
      (∑' n, derivativePositiveTerm c a k n z) +
      (∑' n, derivativeNegativeTerm c a k n z)

end D12Complex.Laurent

namespace Specs.D12Complex.Ch07.Laurent
open _root_.D12Complex _root_.D12Complex.Laurent

-- Exact value interfaces for the canonical definitions above.
def annulus_type := ℂ → ℝ → ℝ≥0∞ → Set ℂ
def annulus_value : annulus_type := _root_.D12Complex.Laurent.annulus

def closedSubannulus_type := ℂ → ℝ → ℝ → Set ℂ
def closedSubannulus_value : closedSubannulus_type := _root_.D12Complex.Laurent.closedSubannulus

def coefficientIntegral_type := (ℂ → ℂ) → ℂ → ℝ → ℤ → ℂ
def coefficientIntegral_value : coefficientIntegral_type := _root_.D12Complex.Laurent.coefficientIntegral

def positiveTerm_type := (ℤ → ℂ) → ℂ → ℕ → ℂ → ℂ
def positiveTerm_value : positiveTerm_type := _root_.D12Complex.Laurent.positiveTerm

def negativeTerm_type := (ℤ → ℂ) → ℂ → ℕ → ℂ → ℂ
def negativeTerm_value : negativeTerm_type := _root_.D12Complex.Laurent.negativeTerm

def positivePart_type := (ℤ → ℂ) → ℂ → ℂ → ℂ
def positivePart_value : positivePart_type := _root_.D12Complex.Laurent.positivePart

def negativePart_type := (ℤ → ℂ) → ℂ → ℂ → ℂ
def negativePart_value : negativePart_type := _root_.D12Complex.Laurent.negativePart

def HasLaurentSeriesOn_type := (ℂ → ℂ) → ℂ → ℝ → ℝ≥0∞ → (ℤ → ℂ) → Prop
def HasLaurentSeriesOn_value : HasLaurentSeriesOn_type := _root_.D12Complex.Laurent.HasLaurentSeriesOn

def ConvergentLaurentSeriesOn_type := (ℂ → ℂ) → ℂ → ℝ → ℝ≥0∞ → (ℤ → ℂ) → Prop
def ConvergentLaurentSeriesOn_value : ConvergentLaurentSeriesOn_type :=
  _root_.D12Complex.Laurent.ConvergentLaurentSeriesOn

def AbsoluteUniformSeriesOn_type := (ℕ → ℂ → ℂ) → Set ℂ → Prop
def AbsoluteUniformSeriesOn_value : AbsoluteUniformSeriesOn_type := _root_.D12Complex.Laurent.AbsoluteUniformSeriesOn

def derivativePositiveTerm_type := (ℤ → ℂ) → ℂ → ℕ → ℕ → ℂ → ℂ
def derivativePositiveTerm_value : derivativePositiveTerm_type := _root_.D12Complex.Laurent.derivativePositiveTerm

def derivativeNegativeTerm_type := (ℤ → ℂ) → ℂ → ℕ → ℕ → ℂ → ℂ
def derivativeNegativeTerm_value : derivativeNegativeTerm_type := _root_.D12Complex.Laurent.derivativeNegativeTerm

def TermwiseDerivativesOn_type := (ℂ → ℂ) → ℂ → ℝ → ℝ≥0∞ → (ℤ → ℂ) → Prop
def TermwiseDerivativesOn_value : TermwiseDerivativesOn_type := _root_.D12Complex.Laurent.TermwiseDerivativesOn

/-- Full original theorem, including all radii, uniqueness among convergent
representations, absolute uniform convergence, and every derivative order. -/
def laurent_expansion_type : Prop :=
  ∀ (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞) (f : ℂ → ℂ),
    0 ≤ r₀ → ENNReal.ofReal r₀ < R₀ → HolomorphicOn (annulus a r₀ R₀) f →
    ∃ c : ℤ → ℂ,
      HasLaurentSeriesOn f a r₀ R₀ c ∧
      (∀ d : ℤ → ℂ, ConvergentLaurentSeriesOn f a r₀ R₀ d → d = c) ∧
      (∀ ρ : ℝ, r₀ < ρ → ENNReal.ofReal ρ < R₀ →
        ∀ n : ℤ, c n = coefficientIntegral f a ρ n) ∧
      TermwiseDerivativesOn f a r₀ R₀ c ∧
      (∀ (s t : ℝ), r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ → ∀ k : ℕ,
        AbsoluteUniformSeriesOn (derivativePositiveTerm c a k) (closedSubannulus a s t) ∧
        AbsoluteUniformSeriesOn (derivativeNegativeTerm c a k) (closedSubannulus a s t))

/-- A separately usable form of the radius-independence assertion. -/
def coefficientIntegral_independent_type : Prop :=
  ∀ (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞) (f : ℂ → ℂ),
    0 ≤ r₀ → HolomorphicOn (annulus a r₀ R₀) f →
    ∀ (ρ σ : ℝ), r₀ < ρ → ENNReal.ofReal ρ < R₀ →
      r₀ < σ → ENNReal.ofReal σ < R₀ →
      ∀ n : ℤ, coefficientIntegral f a ρ n = coefficientIntegral f a σ n

/-- ML bound, valid for every integer coefficient and every positive circle. -/
def coefficientIntegral_bound_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (ρ M : ℝ), 0 < ρ →
    (∀ w ∈ Metric.sphere a ρ, ‖f w‖ ≤ M) → ∀ n : ℤ,
      ‖coefficientIntegral f a ρ n‖ ≤ M * ρ ^ (-n)

/-- The exact integral which extracts a single Laurent monomial. -/
def coefficientIntegral_monomial_type : Prop :=
  ∀ (a : ℂ) (ρ : ℝ), 0 < ρ → ∀ m n : ℤ,
    coefficientIntegral (fun w => (w - a) ^ m) a ρ n = if m = n then 1 else 0

/-- Explicit derivative of a Laurent monomial, with falling integer factors. -/
def iteratedDeriv_monomial_type : Prop :=
  ∀ (a b z : ℂ) (m : ℤ) (k : ℕ),
    iteratedDeriv k (fun w : ℂ => b * (w - a) ^ m) z =
      b * (∏ j ∈ Finset.range k, ((m : ℂ) - j)) * (z - a) ^ (m - k)

/-- Coefficient identities imply absolute uniform convergence on every closed
subannulus; this helper does not assume that the series represents f. -/
def normalConvergence_of_coefficientFormula_type : Prop :=
  ∀ (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞) (f : ℂ → ℂ) (c : ℤ → ℂ),
    0 ≤ r₀ → HolomorphicOn (annulus a r₀ R₀) f →
    (∀ ρ : ℝ, r₀ < ρ → ENNReal.ofReal ρ < R₀ →
      ∀ n : ℤ, c n = coefficientIntegral f a ρ n) →
    ∀ (s t : ℝ), r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ →
      AbsoluteUniformSeriesOn (positiveTerm c a) (closedSubannulus a s t) ∧
      AbsoluteUniformSeriesOn (negativeTerm c a) (closedSubannulus a s t)

/-- The annular Cauchy formula with an outer positive circle and an inner
negative circle. Only weak holomorphy on the given annulus is required. -/
def annular_cauchy_formula_type : Prop :=
  ∀ (a z : ℂ) (r₀ ρ σ : ℝ) (R₀ : ℝ≥0∞) (f : ℂ → ℂ),
    0 ≤ r₀ → HolomorphicOn (annulus a r₀ R₀) f →
    r₀ < ρ → ρ < ‖z - a‖ → ‖z - a‖ < σ → ENNReal.ofReal σ < R₀ →
    f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (circleIntegral (fun w => f w / (w - z)) a σ -
       circleIntegral (fun w => f w / (w - z)) a ρ)

/-- The existence and coefficient formula part, retaining absolute uniform
convergence of both undifferentiated series on every closed subannulus. -/
def laurent_exists_type : Prop :=
  ∀ (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞) (f : ℂ → ℂ),
    0 ≤ r₀ → ENNReal.ofReal r₀ < R₀ → HolomorphicOn (annulus a r₀ R₀) f →
    ∃ c : ℤ → ℂ,
      HasLaurentSeriesOn f a r₀ R₀ c ∧
      (∀ ρ : ℝ, r₀ < ρ → ENNReal.ofReal ρ < R₀ →
        ∀ n : ℤ, c n = coefficientIntegral f a ρ n) ∧
      (∀ (s t : ℝ), r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ →
        AbsoluteUniformSeriesOn (positiveTerm c a) (closedSubannulus a s t) ∧
        AbsoluteUniformSeriesOn (negativeTerm c a) (closedSubannulus a s t))

/-- Uniqueness among ordinary convergent two-sided representations. -/
def laurent_unique_type : Prop :=
  ∀ (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞) (f : ℂ → ℂ) (c d : ℤ → ℂ),
    0 ≤ r₀ → ENNReal.ofReal r₀ < R₀ →
    ConvergentLaurentSeriesOn f a r₀ R₀ c →
    ConvergentLaurentSeriesOn f a r₀ R₀ d → c = d

/-- Every ordinary convergent representation of a holomorphic function admits
all orders of termwise differentiation and absolute uniform derivative convergence. -/
def laurent_calculus_type : Prop :=
  ∀ (a : ℂ) (r₀ : ℝ) (R₀ : ℝ≥0∞) (f : ℂ → ℂ) (c : ℤ → ℂ),
    0 ≤ r₀ → HolomorphicOn (annulus a r₀ R₀) f →
    ConvergentLaurentSeriesOn f a r₀ R₀ c →
    TermwiseDerivativesOn f a r₀ R₀ c ∧
    (∀ (s t : ℝ), r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ → ∀ k : ℕ,
      AbsoluteUniformSeriesOn (derivativePositiveTerm c a k) (closedSubannulus a s t) ∧
      AbsoluteUniformSeriesOn (derivativeNegativeTerm c a k) (closedSubannulus a s t))

end Specs.D12Complex.Ch07.Laurent
