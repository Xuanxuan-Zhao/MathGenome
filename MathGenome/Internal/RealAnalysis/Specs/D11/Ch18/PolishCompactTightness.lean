import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
Independent specification for the compact-tightness stage of
paper.tex:5402–5411 (`d11:18:polish-tightness-regular`).

The measure is on exactly the Borel sigma-algebra. Completeness is metric
completeness, separability is topological separability, and the only size
assumption is finite total mass. In particular there is no Radon, local
compactness, properness, probability, or nonempty-space assumption.
The further Borel-set approximation conclusion is a separate allocated goal.
-/

namespace Specs.D11.Ch18.PolishCompactTightness

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- Every positive real error permits a compact set missing less than that mass. -/
def compact_tightness : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X] [SeparableSpace X]
    (μ : @Measure X (borel X)), μ univ < ∞ →
      ∀ (ε : ℝ), 0 < ε →
        ∃ K : Set X, IsCompact K ∧ μ (univ \ K) < ENNReal.ofReal ε

end Specs.D11.Ch18.PolishCompactTightness
