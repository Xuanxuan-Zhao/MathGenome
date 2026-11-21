import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statements for paper.tex:880–915, Euclidean regularity.
`Point d` has its Euclidean topology. The measurable domain and measure below
are the full Carathéodory Lebesgue objects fixed by the upstream interface.
Neither finiteness nor Borel measurability is imposed on the first two claims. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch03.EuclideanRegularity

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def outer_regularity : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  MeasurableSet[lebesgueSpace_value d] E →
    lebesgue_value d E =
      ⨅ (U : Set (Point d)) (_ : E ⊆ U) (_ : IsOpen U), lebesgue_value d U

def inner_regularity : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  MeasurableSet[lebesgueSpace_value d] E →
    lebesgue_value d E =
      ⨆ (K : Set (Point d)) (_ : K ⊆ E) (_ : IsCompact K), lebesgue_value d K

def compact_open_approximation : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  MeasurableSet[lebesgueSpace_value d] E → lebesgue_value d E < ∞ →
    ∀ ε : ℝ, 0 < ε → ∃ K U : Set (Point d),
      IsCompact K ∧ K ⊆ E ∧ E ⊆ U ∧ IsOpen U ∧
        lebesgue_value d (U \ K) < ENNReal.ofReal ε

end Specs.D11.Ch03.EuclideanRegularity
