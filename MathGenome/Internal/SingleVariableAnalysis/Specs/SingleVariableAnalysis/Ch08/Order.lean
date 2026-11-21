import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! K03.08.order (paper.tex:2070–2088). All integrals below are the
existing Darboux integrals. The two scalar cases are ℝ and ℂ;
the real function given by its usual norm has its own real integral.
Integrability retains the ordered interval hypothesis, including a = b. -/
namespace Specs.SingleVariableAnalysis.Ch08.Order
open _root_.SingleVariableAnalysis _root_.SingleVariableAnalysis.Riemann

/-- Pointwise order is needed only on the interval of integration. -/
def realIntegralMono : Prop :=
  ∀ (f g : ℝ → ℝ) {a b : ℝ}
    (hf : Integral.realIntegrableValue f a b)
    (hg : Integral.realIntegrableValue g a b),
    (∀ x ∈ Set.Icc a b, f x ≤ g x) →
    Integral.realIntegralValue f hf ≤ Integral.realIntegralValue g hg

/-- The absolute value of a real integrable function is integrable,
with the integral bounded by the length times its supremum. -/
def realNormEstimate : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (hf : Integral.realIntegrableValue f a b),
    ∃ hn : Integral.realIntegrableValue (fun x => ‖f x‖) a b,
      ‖Integral.realIntegralValue f hf‖ ≤ Integral.realIntegralValue _ hn ∧
      Integral.realIntegralValue _ hn ≤ (b - a) * sSup ((fun x => ‖f x‖) '' Set.Icc a b)

/-- The complex modulus satisfies exactly the same bound, with no extra
constant or regularity hypothesis. Both component integrals are Darboux values. -/
def complexNormEstimate : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ} (hf : Integral.complexIntegrableValue f a b),
    ∃ hn : Integral.realIntegrableValue (fun x => ‖f x‖) a b,
      ‖Integral.complexIntegralValue f hf‖ ≤ Integral.realIntegralValue _ hn ∧
      Integral.realIntegralValue _ hn ≤ (b - a) * sSup ((fun x => ‖f x‖) '' Set.Icc a b)

end Specs.SingleVariableAnalysis.Ch08.Order
