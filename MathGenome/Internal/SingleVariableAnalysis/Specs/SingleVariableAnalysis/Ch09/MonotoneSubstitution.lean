import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! K03.09.monotone_substitution, paper.tex:2464–2495.
The derivative is supplied as a real function with its continuous one-sided
endpoint values. `HasDerivWithinAt` tests only the closed domain; values of
ambient extensions outside it are unrestricted. Monotonicity is non-strict
and includes either direction and constant maps. Both integrals are the
previously defined proper Darboux integrals, with orientation on the image.
Transformed integrability is a conclusion, not a hypothesis. -/
namespace Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution
open Set

/-- The usual C¹ data on a compact real interval. -/
def C1OnInterval (φ dφ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn dφ (Icc a b) ∧
    ∀ t ∈ Icc a b, HasDerivWithinAt φ (dφ t) (Icc a b) t

def realMonotoneSubstitution : Prop :=
  ∀ (φ dφ f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    C1OnInterval φ dφ a b →
    (MonotoneOn φ (Icc a b) ∨ AntitoneOn φ (Icc a b)) →
    ∀ hf : Ch08.Oriented.realIntegrableValue f (φ a) (φ b),
      ∃ hg : Ch08.Integral.realIntegrableValue (fun t => dφ t * f (φ t)) a b,
        Ch08.Integral.realIntegralValue _ hg =
          Ch08.Oriented.realIntegralValue f hf

def complexMonotoneSubstitution : Prop :=
  ∀ (φ dφ : ℝ → ℝ) (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    C1OnInterval φ dφ a b →
    (MonotoneOn φ (Icc a b) ∨ AntitoneOn φ (Icc a b)) →
    ∀ hf : Ch08.Oriented.complexIntegrableValue f (φ a) (φ b),
      ∃ hg : Ch08.Integral.complexIntegrableValue
        (fun t => (dφ t : ℂ) * f (φ t)) a b,
        Ch08.Integral.complexIntegralValue _ hg =
          Ch08.Oriented.complexIntegralValue f hf

end Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution
