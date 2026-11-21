import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import Mathlib.Topology.Order.Basic

/-! Independent specification of the isolated-spike remark under
K03.15.rs_jump, paper.tex:3767–3774. Both f and α are exactly this
real unit spike, retaining its value at c. Tags are in closed cells. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction
open _root_.SingleVariableAnalysis.Riemann
open Filter Topology

abbrev spikeType := ℝ → ℝ → ℝ
noncomputable def spikeValue : spikeType := fun c x => if x = c then 1 else 0

def variationAndBounds : Prop := ∀ {a c b : ℝ}, a < c → c < b →
  Variation.totalVariationValue (spikeValue c) a b = 2 ∧
  Variation.boundedVariationValue (spikeValue c) a b ∧
  RsSums.boundedOnValue a b (spikeValue c)

/-- The full jump is zero, whereas the separate jumps are +1 and -1. -/
def zeroNetJump : Prop := ∀ c : ℝ, ∃ L R : ℝ,
  L = 0 ∧ R = 0 ∧
  Tendsto (spikeValue c) (𝓝[<] c) (𝓝 L) ∧
  Tendsto (spikeValue c) (𝓝[>] c) (𝓝 R) ∧
  R - L = 0 ∧ spikeValue c c - L = 1 ∧ R - spikeValue c c = -1

def sumsOnPartition : Prop := ∀ {a c b : ℝ}, a < c → c < b →
  ∀ P : PartitionData a b, c ∈ Specs.SingleVariableAnalysis.Ch08.Partitions.pointsValue P →
  ∃ tneg tzero tpos : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
    RsSums.sumValue P tneg (spikeValue c) (spikeValue c) = -1 ∧
    RsSums.sumValue P tzero (spikeValue c) (spikeValue c) = 0 ∧
    RsSums.sumValue P tpos (spikeValue c) (spikeValue c) = 1

/-- Every controlling partition admits a refinement with the three sums. -/
def sumsOnRefinements : Prop := ∀ {a c b : ℝ}, a < c → c < b →
  ∀ P₀ : PartitionData a b, ∃ P : PartitionData a b,
    Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue P P₀ ∧
    c ∈ Specs.SingleVariableAnalysis.Ch08.Partitions.pointsValue P ∧
    ∃ tneg tzero tpos : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
      RsSums.sumValue P tneg (spikeValue c) (spikeValue c) = -1 ∧
      RsSums.sumValue P tzero (spikeValue c) (spikeValue c) = 0 ∧
      RsSums.sumValue P tpos (spikeValue c) (spikeValue c) = 1

def noRefinementLimit : Prop := ∀ {a c b : ℝ}, a < c → c < b →
  ¬ ∃ I : ℝ, RsSums.limitValue a b (spikeValue c) (spikeValue c) I

def noIntegral : Prop := ∀ {a c b : ℝ}, a < c → c < b →
  ¬ ∃ I : ℝ, RsSums.integralValue a b (spikeValue c) (spikeValue c) I

end Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction
