import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains

/-! The real chain identity needed in paper.tex, D12.03.02.
The parameter map has an actual finite C1 partition, including the empty
partition when its interval is degenerate. Monotonicity is nonstrict.
All derivatives are those of the canonical total representatives; the
conclusion uses restricted Lebesgue measure and thus ignores endpoints. -/

noncomputable section
open Set MeasureTheory

namespace Specs.D12Complex.Ch03.PC1MonotoneChainRule
open _root_.D12Complex

def ae_deriv_monotone_comp_type : Prop :=
  ∀ (γ η : PiecewiseC1Path) (φ : ℝ → ℝ),
    ContinuousOn φ (Icc η.path.a η.path.b) →
    MonotoneOn φ (Icc η.path.a η.path.b) →
    MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) →
    SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) →
    ∀ (n : ℕ) (node : Fin (n + 1) → ℝ),
      StrictMono node → node 0 = η.path.a → node (Fin.last n) = η.path.b →
      (∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ))) →
      (∀ t ∈ Icc η.path.a η.path.b, η t = γ (φ t)) →
      ∀ᵐ t ∂(volume.restrict (Icc η.path.a η.path.b)),
        deriv η t = deriv φ t • deriv γ (φ t)

end Specs.D12Complex.Ch03.PC1MonotoneChainRule
