import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Singularities

/-! Casorati–Weierstrass, paper.tex:1714–1730, d12:07-03.
The representative's value at the puncture is unrestricted. Holomorphy
means the canonical weak holomorphy, and essentiality is the canonical
exclusion of removability and poles. The conclusion spells out density
by approximation of every complex value with every positive tolerance. -/

namespace Specs.D12Complex.Ch07.Casorati

open _root_.D12Complex

def approximation_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ), 0 < R →
    HolomorphicOn (puncturedDisk a R) f → EssentialSingularityAt f a →
    ∀ r : ℝ, 0 < r → r ≤ R → ∀ (w : ℂ) (ε : ℝ), 0 < ε →
      ∃ z ∈ puncturedDisk a r, ‖f z - w‖ < ε

end Specs.D12Complex.Ch07.Casorati
