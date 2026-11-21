import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure
import Mathlib.Data.Set.Card

/-! Independent statements for paper.tex:6040–6047. All evaluations use the
shared coefficient-one diameter-cover outer measure on arbitrary subsets of a
genuine metric space. No measurability or finiteness of the space is assumed.
The extended cardinality takes the value infinity on every infinite set. -/

noncomputable section

open Set
open scoped ENNReal

universe u

namespace Specs.D11.Ch22.ZeroDimensionCounting

def finiteStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (hE : E.Finite),
    HausdorffOuterMeasure.outerMeasureValue 0 E = (hE.toFinset.card : ℝ≥0∞)

def infiniteStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X), E.Infinite →
    HausdorffOuterMeasure.outerMeasureValue 0 E = ∞

def countingStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    HausdorffOuterMeasure.outerMeasureValue 0 E = (E.encard : ℝ≥0∞)

end Specs.D11.Ch22.ZeroDimensionCounting
