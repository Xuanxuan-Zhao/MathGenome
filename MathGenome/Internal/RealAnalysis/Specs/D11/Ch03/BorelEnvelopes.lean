import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statement of the null Borel-envelope clause of
paper.tex:932–947. The displayed countable closed/open representations
express F_sigma and G_delta directly. Borel measurability uses the canonical
Borel structure, while the errors use the full Lebesgue measure. -/

noncomputable section

open Set MeasureTheory

namespace Specs.D11.Ch03.BorelEnvelopes

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def borel_envelopes : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    MeasurableSet[lebesgueSpace_value d] E →
    ∃ F G : Set (Point d),
      (∃ K : ℕ → Set (Point d), (∀ n, IsClosed (K n)) ∧ F = ⋃ n, K n) ∧
      (∃ U : ℕ → Set (Point d), (∀ n, IsOpen (U n)) ∧ G = ⋂ n, U n) ∧
      MeasurableSet[borel (Point d)] F ∧ MeasurableSet[borel (Point d)] G ∧
      F ⊆ E ∧ E ⊆ G ∧
      lebesgue_value d (E \ F) = 0 ∧ lebesgue_value d (G \ E) = 0

end Specs.D11.Ch03.BorelEnvelopes
