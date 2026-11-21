import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent specification of paper.tex:6058–6066. A map on an arbitrary
subset `E` is a function on the subtype. The source mass is evaluated on
`Subtype.val '' A` in the ambient space, with no measurability assumptions.
The shared outer measure retains singleton cost one at exponent zero. -/

noncomputable section

open Set
open scoped NNReal ENNReal

universe u v

namespace Specs.D11.Ch22.LipschitzZeroCases

def imageBoundStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (L s : ℝ≥0), 0 < L → LipschitzWith L f →
    ∀ A : Set E,
      HausdorffOuterMeasure.outerMeasureValue s (f '' A) ≤
        (L : ℝ≥0∞) ^ (s : ℝ) *
          HausdorffOuterMeasure.outerMeasureValue s (Subtype.val '' A)

def zeroImageStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y), LipschitzWith 0 f →
    ∀ (A : Set E) (a : E), a ∈ A → f '' A = {f a}

def zeroPositiveMassStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y), LipschitzWith 0 f →
    ∀ (A : Set E), A.Nonempty → ∀ (s : ℝ≥0), 0 < s →
      HausdorffOuterMeasure.outerMeasureValue s (f '' A) = 0

def zeroCountingMassStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y), LipschitzWith 0 f →
    ∀ (A : Set E), A.Nonempty →
      HausdorffOuterMeasure.outerMeasureValue 0 (f '' A) = 1

def emptyImageStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (s : ℝ≥0),
      f '' (∅ : Set E) = ∅ ∧
      HausdorffOuterMeasure.outerMeasureValue s (f '' (∅ : Set E)) = 0

end Specs.D11.Ch22.LipschitzZeroCases
