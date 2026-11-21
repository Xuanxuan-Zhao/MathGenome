import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Partitions
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Normed.Group.Real

/-! Independent specification of K03.15.variation, paper.tex:3567–3573.
The supremum is taken over the previously defined strict endpoint partitions.
The same formula includes the zero-cell partition of a singleton interval.
Functions are ambient functions restricted to the closed interval; values at every
point, including nodes and endpoints, are retained. The normed-group generality
includes both of the manuscript's scalar choices, ℝ and ℂ. -/
namespace Specs.SingleVariableAnalysis.Ch15.Variation
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators ENNReal
universe u

abbrev partitionSumType := {E : Type u} → [NormedAddCommGroup E] →
  {a b : ℝ} → PartitionData a b → (ℝ → E) → ℝ≥0∞

noncomputable def partitionSumValue : partitionSumType :=
  fun P f => ∑ i : Fin P.n, ENNReal.ofReal ‖f (P.point i.succ) - f (P.point i.castSucc)‖

abbrev totalVariationType := {E : Type u} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → ℝ → ℝ≥0∞

noncomputable def totalVariationValue : totalVariationType :=
  fun f a b => ⨆ P : PartitionData a b, partitionSumValue P f

abbrev boundedVariationType := {E : Type u} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → ℝ → Prop

noncomputable def boundedVariationValue : boundedVariationType :=
  fun f a b => totalVariationValue f a b < ⊤

def partitionSumFinite : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  {a b : ℝ} (P : PartitionData a b) (f : ℝ → E), partitionSumValue P f < ⊤

def supremumCharacterization : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) (a b : ℝ) (v : ℝ≥0∞),
  totalVariationValue f a b ≤ v ↔ ∀ P : PartitionData a b, partitionSumValue P f ≤ v

def degenerate : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) (a : ℝ), totalVariationValue f a a = 0

def eVariationCompatibility : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a b : ℝ}, a ≤ b →
  totalVariationValue f a b = eVariationOn f (Set.Icc a b)

def boundedVariationCompatibility : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a b : ℝ}, a ≤ b →
  (boundedVariationValue f a b ↔ BoundedVariationOn f (Set.Icc a b))

def finiteValue : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a b : ℝ}, boundedVariationValue f a b →
  ENNReal.ofReal (totalVariationValue f a b).toReal = totalVariationValue f a b

def intervalCongruence : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  {f g : ℝ → E} {a b : ℝ}, Set.EqOn f g (Set.Icc a b) →
  totalVariationValue f a b = totalVariationValue g a b

/-- Every isolated point value is counted, over both real and complex scalars.
Taking z = 1 gives exactly the manuscript's spike of variation 2. -/
def spikeVariation : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (z : E) {a c b : ℝ}, a < c → c < b →
  totalVariationValue (fun x => if x = c then z else 0) a b =
    2 * ENNReal.ofReal ‖z‖

def realUnitSpike : Prop := ∀ {a c b : ℝ}, a < c → c < b →
  totalVariationValue (fun x => if x = c then (1 : ℝ) else 0) a b = 2

def complexUnitSpike : Prop := ∀ {a c b : ℝ}, a < c → c < b →
  totalVariationValue (fun x => if x = c then (1 : ℂ) else 0) a b = 2

end Specs.SingleVariableAnalysis.Ch15.Variation
