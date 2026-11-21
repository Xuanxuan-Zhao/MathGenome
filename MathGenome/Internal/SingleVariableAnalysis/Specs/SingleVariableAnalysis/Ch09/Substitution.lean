import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.ContinuousOn

/-! K03.09.substitution, paper.tex:2447–2466.
The data `φ, φ'` express C¹ on the closed interval: both are continuous
there and φ' is the derivative within that interval, including the available
one-sided derivatives. Only the domain interval I of f is ordered connected;
it may be closed, half open, unbounded, or a singleton. There is no
monotonicity condition on φ and no neighborhood condition on its image.
The conclusions supply existence of both proper Darboux integrals, with
orientation on the image endpoints. Real increments are used for both scalars.
-/
namespace Specs.SingleVariableAnalysis.Ch09.Substitution
open Set
open Specs.SingleVariableAnalysis.Ch08

def realSubstitution : Prop :=
  ∀ (φ φ' f : ℝ → ℝ) (a b : ℝ) (I : Set ℝ), a ≤ b →
    ContinuousOn φ (Icc a b) → ContinuousOn φ' (Icc a b) →
    (∀ t ∈ Icc a b, HasDerivWithinAt φ (φ' t) (Icc a b) t) →
    I.OrdConnected → ContinuousOn f I → MapsTo φ (Icc a b) I →
    ∃ hg : Integral.realIntegrableValue (fun t => f (φ t) * φ' t) a b,
    ∃ hf : Oriented.realIntegrableValue f (φ a) (φ b),
      Integral.realIntegralValue _ hg = Oriented.realIntegralValue f hf

def complexSubstitution : Prop :=
  ∀ (φ φ' : ℝ → ℝ) (f : ℝ → ℂ) (a b : ℝ) (I : Set ℝ), a ≤ b →
    ContinuousOn φ (Icc a b) → ContinuousOn φ' (Icc a b) →
    (∀ t ∈ Icc a b, HasDerivWithinAt φ (φ' t) (Icc a b) t) →
    I.OrdConnected → ContinuousOn f I → MapsTo φ (Icc a b) I →
    ∃ hg : Integral.complexIntegrableValue (fun t => f (φ t) * (φ' t : ℂ)) a b,
    ∃ hf : Oriented.complexIntegrableValue f (φ a) (φ b),
      Integral.complexIntegralValue _ hg = Oriented.complexIntegralValue f hf

end Specs.SingleVariableAnalysis.Ch09.Substitution
