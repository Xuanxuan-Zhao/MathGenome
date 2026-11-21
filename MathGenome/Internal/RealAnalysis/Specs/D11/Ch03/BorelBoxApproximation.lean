import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statement of Borel and box approximation,
paper.tex:932–958. The first clause has no finite-measure assumption.
The second clause allows any positive error and uses bounded coordinate
boxes with independently chosen endpoint conventions. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal symmDiff

namespace Specs.D11.Ch03.BorelBoxApproximation

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def borel_box_approximation : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    MeasurableSet[lebesgueSpace_value d] E →
    (∃ F G : Set (Point d),
      (∃ K : ℕ → Set (Point d), (∀ n, IsClosed (K n)) ∧ F = ⋃ n, K n) ∧
      (∃ U : ℕ → Set (Point d), (∀ n, IsOpen (U n)) ∧ G = ⋂ n, U n) ∧
      MeasurableSet[borel (Point d)] F ∧ MeasurableSet[borel (Point d)] G ∧
      F ⊆ E ∧ E ⊆ G ∧
      lebesgue_value d (E \ F) = 0 ∧ lebesgue_value d (G \ E) = 0) ∧
    (lebesgue_value d E < ∞ →
      ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Set (Point d)),
        (∀ B ∈ S, ∃ (a b : Fin d → ℝ) (lower upper : Fin d → Bool),
          B = endpointBox a b lower upper) ∧
        (S : Set (Set (Point d))).PairwiseDisjoint id ∧
        lebesgue_value d (E ∆ ⋃₀ (S : Set (Set (Point d)))) < ENNReal.ofReal ε)

end Specs.D11.Ch03.BorelBoxApproximation
