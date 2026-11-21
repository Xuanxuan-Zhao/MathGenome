import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Substitution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Polynomial
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigInverses

/-! K03.09.trig_substitution. Canonical trig functions are identified with the
upstream series functions and analytic π by the proved Ch07 bridges.
Bivariate polynomials are `Polynomial (Polynomial K)`: the outer variable is
sine and the inner variable is cosine. The quotient keeps its original
specified denominator, including removable zeros. All integrals below are
proper Darboux integrals, with separate existence conclusions. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch09.TrigSubstitution
open Set
open Specs.SingleVariableAnalysis.Ch08

def branch (k : ℤ) : Set ℝ := Ioo ((2 * (k : ℝ) - 1) * Real.pi)
  ((2 * (k : ℝ) + 1) * Real.pi)
def forward (x : ℝ) : ℝ := Real.tan (x / 2)
def inverse (k : ℤ) (t : ℝ) : ℝ := 2 * Real.arctan t + 2 * k * Real.pi
def jacobian (t : ℝ) : ℝ := 2 / (1 + t ^ 2)
def rationalSin (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)
def rationalCos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

def bivarEval {K : Type*} [CommSemiring K] (P : Polynomial (Polynomial K)) (s c : K) : K :=
  P.eval₂ (Polynomial.evalRingHom c) s

def sourceCompatibility : Prop :=
  (∀ x : ℝ, Ch07.SinCos.realSeriesSinValue x = Real.sin x ∧
    Ch07.SinCos.realSeriesCosValue x = Real.cos x) ∧
  Ch07.PiPeriod.analyticPiValue = Real.pi ∧
  Ch07.TrigInverses.principalArctanValue = Real.arctan

def branchBijection : Prop := ∀ k : ℤ,
  StrictMonoOn forward (branch k) ∧ BijOn forward (branch k) univ ∧
  MapsTo (inverse k) univ (branch k) ∧
  (∀ x ∈ branch k, inverse k (forward x) = x) ∧
  (∀ t : ℝ, forward (inverse k t) = t) ∧
  ContDiffOn ℝ 1 forward (branch k) ∧ ContDiff ℝ 1 (inverse k)

def formulas : Prop :=
  (∀ (k : ℤ) (x : ℝ), x ∈ branch k →
    Real.cos (x / 2) ≠ 0 ∧ Real.sin x = rationalSin (forward x) ∧
    Real.cos x = rationalCos (forward x) ∧
    HasDerivAt forward (1 / (2 * Real.cos (x / 2) ^ 2)) x) ∧
  (∀ (k : ℤ) (t : ℝ), HasDerivAt (inverse k) (jacobian t) t)

/-- A literal quotient of univariate polynomials after rationalization, with
no new real zeros of the denominator at regular points. The assertion holds
for real and complex coefficients; the outer universal is instantiated only
at the two source scalar types below. -/
def rationalFormFor (K : Type*) [Field K] [Algebra ℝ K] : Prop :=
  ∀ P Q : Polynomial (Polynomial K), ∃ p q : Polynomial K, ∀ t : ℝ,
    (bivarEval P (algebraMap ℝ K (rationalSin t)) (algebraMap ℝ K (rationalCos t)) /
      bivarEval Q (algebraMap ℝ K (rationalSin t)) (algebraMap ℝ K (rationalCos t))) *
        algebraMap ℝ K (jacobian t) = p.eval (algebraMap ℝ K t) / q.eval (algebraMap ℝ K t) ∧
    (q.eval (algebraMap ℝ K t) ≠ 0 ↔
      bivarEval Q (algebraMap ℝ K (rationalSin t)) (algebraMap ℝ K (rationalCos t)) ≠ 0)

def rationalForm : Prop := rationalFormFor ℝ ∧ rationalFormFor ℂ

/-- The compact interval [a,b] lies strictly inside one branch and avoids
all zeros of Q(sin x,cos x). No global nonvanishing of Q is assumed. -/
def realRationalSubstitution : Prop :=
  ∀ (P Q : Polynomial (Polynomial ℝ)) (k : ℤ) (a b : ℝ), a ≤ b →
    Icc a b ⊆ branch k →
    (∀ x ∈ Icc a b, bivarEval Q (Real.sin x) (Real.cos x) ≠ 0) →
    let f := fun x => bivarEval P (Real.sin x) (Real.cos x) /
      bivarEval Q (Real.sin x) (Real.cos x)
    let g := fun t => (bivarEval P (rationalSin t) (rationalCos t) /
      bivarEval Q (rationalSin t) (rationalCos t)) * jacobian t
    ∃ hf : Integral.realIntegrableValue f a b,
    ∃ hg : Integral.realIntegrableValue g (forward a) (forward b),
      Integral.realIntegralValue f hf = Integral.realIntegralValue g hg

def complexRationalSubstitution : Prop :=
  ∀ (P Q : Polynomial (Polynomial ℂ)) (k : ℤ) (a b : ℝ), a ≤ b →
    Icc a b ⊆ branch k →
    (∀ x ∈ Icc a b, bivarEval Q (Real.sin x : ℂ) (Real.cos x : ℂ) ≠ 0) →
    let f := fun x => bivarEval P (Real.sin x : ℂ) (Real.cos x : ℂ) /
      bivarEval Q (Real.sin x : ℂ) (Real.cos x : ℂ)
    let g := fun t => (bivarEval P (rationalSin t : ℂ) (rationalCos t : ℂ) /
      bivarEval Q (rationalSin t : ℂ) (rationalCos t : ℂ)) * (jacobian t : ℂ)
    ∃ hf : Integral.complexIntegrableValue f a b,
    ∃ hg : Integral.complexIntegrableValue g (forward a) (forward b),
      Integral.complexIntegralValue f hf = Integral.complexIntegralValue g hg

end Specs.SingleVariableAnalysis.Ch09.TrigSubstitution
