import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-! Independent statement of paper.tex:924–933 and the Liouville clause
of paper.tex:1455–1465. Entire means the canonical weak holomorphy on ℂ;
no continuity of the derivative or power-series certificate is assumed. -/

namespace Specs.D12Complex.Ch04.Liouville
open _root_.D12Complex

/-- Every globally bounded entire complex function is constant. -/
def bounded_entire_constant_type : Prop :=
  ∀ (f : ℂ → ℂ) (M : ℝ), HolomorphicOn Set.univ f →
    0 ≤ M → (∀ z : ℂ, ‖f z‖ ≤ M) →
    ∃ c : ℂ, ∀ z : ℂ, f z = c

end Specs.D12Complex.Ch04.Liouville
