import Mathlib.Topology.ContinuousMap.Weierstrass
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Independent objects and full proposition types for Lemma 1.9 and Theorem 1.10,
`paper.tex:438–473`. No ordering assumption is imposed on the interval endpoints.
The scalar parameter ranges over both ℝ and ℂ (and all RCLike scalars).
At n = 0 the Bernstein approximant is the constant f(0), since 0/0 = 0. -/
noncomputable section
open Filter Set
open scoped Topology unitInterval Polynomial

namespace P102.Approximation.Expected

abbrev bernsteinApproximantType :=
  {𝕜 : Type} → [RCLike 𝕜] → ℕ → C(I, 𝕜) → C(I, 𝕜)

def bernsteinApproximantValue : bernsteinApproximantType :=
  fun n f => bernsteinApproximation n f

abbrev bernsteinPolynomialForType :=
  {𝕜 : Type} → [RCLike 𝕜] → ℕ → C(I, 𝕜) → 𝕜[X]

def bernsteinPolynomialForValue : bernsteinPolynomialForType :=
  fun {𝕜} [_] n f => ∑ k : Fin (n + 1),
    Polynomial.C (f (bernstein.z k)) * bernsteinPolynomial 𝕜 n k

def bernsteinFormulaStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (n : ℕ) (f : C(I, 𝕜)) (x : I),
    bernsteinApproximantValue n f x = ∑ k : Fin (n + 1),
      ((n.choose k : ℝ) * (x : ℝ) ^ (k : ℕ) * (1 - (x : ℝ)) ^ (n - k)) •
        f (bernstein.z k)

def bernsteinEvaluationStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (n : ℕ) (f : C(I, 𝕜)) (x : I),
    (bernsteinPolynomialForValue n f).eval (algebraMap ℝ 𝕜 (x : ℝ)) =
      bernsteinApproximantValue n f x

def bernsteinZeroStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (f : C(I, 𝕜)),
    bernsteinApproximantValue 0 f = ContinuousMap.const I (f 0)

def bernsteinUniformStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (f : C(I, 𝕜)),
    TendstoUniformly (fun n x => bernsteinApproximantValue n f x) f atTop

/-- The norm is the supremum norm, including on singleton and empty intervals. -/
def algebraicRealStatement : Prop := ∀ (a b : ℝ) (f : C(Icc a b, ℝ)) (ε : ℝ),
  0 < ε → ∃ p : ℝ[X], ‖p.toContinuousMapOn (Icc a b) - f‖ < ε

/-- The quantifier over ε gives uniform approximation on the whole interval.
The polynomial has complex coefficients, and its variable is evaluated at real points. -/
def algebraicComplexStatement : Prop := ∀ (a b : ℝ) (f : C(Icc a b, ℂ)) (ε : ℝ),
  0 < ε → ∃ p : ℂ[X], ∀ x : Icc a b, ‖p.eval (x : ℂ) - f x‖ < ε

def trigonometricRealStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : C(Periodic.Expected.Circle T, ℝ)) (ε : ℝ), 0 < ε →
    ∃ p ∈ Periodic.Expected.realTrigPolynomials T, ‖p - f‖ < ε

def trigonometricComplexStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : C(Periodic.Expected.Circle T, ℂ)) (ε : ℝ), 0 < ε →
    ∃ p ∈ Periodic.Expected.complexTrigPolynomials T, ‖p - f‖ < ε

end P102.Approximation.Expected
