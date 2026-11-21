import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Lagrange
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.FiniteChanges

/-!
K03.09.ftc_second (paper.tex:2396–2414). These are proper Darboux integrals,
with boundedness included in integrability. The extension `g` agrees with the
real-variable derivative only in the open interval; its endpoint values and
all values outside the closed interval are unrestricted. Closed-interval
continuity is relative, so endpoint derivatives are not assumed. Both scalar
choices are stated separately, and singleton intervals are included.
-/
namespace Specs.SingleVariableAnalysis.Ch09.FtcSecond
open Set
open Specs.SingleVariableAnalysis.Ch08.Integral

/-- Newton–Leibniz for a real function and any integrable derivative extension. -/
def realFtcSecond : Prop :=
  ∀ (F g : ℝ → ℝ) (a b : ℝ), a ≤ b →
    ContinuousOn F (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt F (g x) x) →
    ∀ hg : realIntegrableValue g a b,
      realIntegralValue g hg = F b - F a

/-- Real increments, complex values, and the componentwise Darboux integral. -/
def complexFtcSecond : Prop :=
  ∀ (F g : ℝ → ℂ) (a b : ℝ), a ≤ b →
    ContinuousOn F (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt F (g x) x) →
    ∀ hg : complexIntegrableValue g a b,
      complexIntegralValue g hg = F b - F a

/-- Any finite endpoint reassignment remains integrable with the same value. -/
def realEndpointExtensions : Prop :=
  ∀ (f g : ℝ → ℝ) (a b : ℝ),
    (∀ x ∈ Ioo a b, f x = g x) →
    ∀ hf : realIntegrableValue f a b,
      ∃ hg : realIntegrableValue g a b,
        realIntegralValue g hg = realIntegralValue f hf

/-- The same endpoint independence for complex values. -/
def complexEndpointExtensions : Prop :=
  ∀ (f g : ℝ → ℂ) (a b : ℝ),
    (∀ x ∈ Ioo a b, f x = g x) →
    ∀ hf : complexIntegrableValue f a b,
      ∃ hg : complexIntegrableValue g a b,
        complexIntegralValue g hg = complexIntegralValue f hf

end Specs.SingleVariableAnalysis.Ch09.FtcSecond
