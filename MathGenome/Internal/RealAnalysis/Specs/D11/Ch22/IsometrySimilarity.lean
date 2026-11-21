import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure
import Mathlib.Topology.MetricSpace.Isometry

/-!
Independent statements of paper.tex:6050–6056. Both statements concern outer
measure on every subset of genuine metric spaces. Neither surjectivity nor
measurability is assumed. A positive nonnegative real represents the source's
positive real distance multiplier. The exponent ranges over all nonnegative
reals, including zero, with the shared nonempty-set cost convention.
-/

noncomputable section

open Set
open scoped NNReal ENNReal

universe u v

namespace Specs.D11.Ch22.IsometrySimilarity

def isometryStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y), Isometry f → ∀ (s : ℝ≥0) (E : Set X),
      HausdorffOuterMeasure.outerMeasureValue s (f '' E) =
        HausdorffOuterMeasure.outerMeasureValue s E

def similarityStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (r : ℝ≥0), 0 < r →
    (∀ x y, dist (f x) (f y) = (r : ℝ) * dist x y) →
    ∀ (s : ℝ≥0) (E : Set X),
      HausdorffOuterMeasure.outerMeasureValue s (f '' E) =
        (r : ℝ≥0∞) ^ (s : ℝ) * HausdorffOuterMeasure.outerMeasureValue s E

end Specs.D11.Ch22.IsometrySimilarity
