import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorSet
import Mathlib.MeasureTheory.MeasurableSpace.Card

/-! Independent statements for paper.tex:1115–1141. Borel measurability
is kept separate from the completed covering-volume structure. The real
line is identified with Euclidean R¹ by the shared `linePoint` map. -/

open Set MeasureTheory
open scoped Cardinal

namespace Specs.D11.Ch03.NonborelLebesgue

open _root_.D11.Ch03 _root_.D11.Ch03.CantorConstruction

/-- The cardinal bound applies to every second-countable space, in particular
to R and to Euclidean Rᵈ with their original topologies. -/
def borel_cardinality_le : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X],
    Cardinal.mk {s : Set X | MeasurableSet[borel X] s} ≤ 𝔠

def exists_nonborel_cantor_subset : Prop :=
  ∃ N : Set ℝ, N ⊆ CantorSet.C_value ∧ ¬ MeasurableSet[borel ℝ] N

/-- The same subset is non-Borel on the real line and under the canonical
identification with R¹, but belongs to the completed Lebesgue space with mass zero. -/
def lebesgue_not_borel : Prop :=
  ∃ N : Set ℝ, N ⊆ CantorSet.C_value ∧
    ¬ MeasurableSet[borel ℝ] N ∧
    ¬ MeasurableSet[borel (Point 1)] (linePoint '' N) ∧
    MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1] (linePoint '' N) ∧
    LebesgueMeasures.lebesgue_value 1 (linePoint '' N) = 0

def borel_incomplete : Prop :=
  ¬ (LebesgueMeasures.borelMeasure_value 1).IsComplete

end Specs.D11.Ch03.NonborelLebesgue
