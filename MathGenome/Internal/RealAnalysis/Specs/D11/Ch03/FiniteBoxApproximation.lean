import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! The finite-measure clause of paper.tex:932–958. Every coordinate endpoint
is finite and may independently be included or excluded. Degenerate and empty
boxes, as well as an empty finite family, are permitted. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal symmDiff

namespace Specs.D11.Ch03.FiniteBoxApproximation
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def finite_box_approximation : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    MeasurableSet[lebesgueSpace_value d] E → lebesgue_value d E < ∞ →
    ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Set (Point d)),
      (∀ B ∈ S, ∃ (a b : Fin d → ℝ) (lower upper : Fin d → Bool),
        B = endpointBox a b lower upper) ∧
      (S : Set (Set (Point d))).PairwiseDisjoint id ∧
      lebesgue_value d (E ∆ ⋃₀ (S : Set (Set (Point d)))) < ENNReal.ofReal ε

end Specs.D11.Ch03.FiniteBoxApproximation
