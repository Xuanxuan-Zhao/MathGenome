import MathGenome.Internal.RealAnalysis.D11.Ch03.BorelEnvelopes
import MathGenome.Internal.RealAnalysis.D11.Ch03.FiniteBoxApproximation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.BorelBoxApproximation

/-! Borel and box approximation (paper.tex:932–958), assembled from the
null-envelope and finite-disjoint-box approximation theorems. Both use
the same Euclidean space and full Carathéodory Lebesgue measure. -/

namespace D11.Ch03.BorelBoxApproximation

theorem borel_box_approximation :
    Specs.D11.Ch03.BorelBoxApproximation.borel_box_approximation := by
  intro d _ E hE
  exact ⟨BorelEnvelopes.borel_envelopes d E hE,
    FiniteBoxApproximation.finite_box_approximation d E hE⟩

end D11.Ch03.BorelBoxApproximation
