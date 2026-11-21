import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.DimensionDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.OuterVolume

/-! Independent statements for paper.tex:6111–6117, ambient Euclidean
Hausdorff dimension. `Point n` has the l2 metric; all masses are the shared
coefficient-one outer masses, and sets need not be measurable. A cube may be
embedded by an isometry defined only on the cube, with arbitrary positive side
length; no extension of that isometry to the whole space is assumed. -/

noncomputable section
open Set
open scoped NNReal ENNReal

namespace Specs.D11.Ch22.EuclideanDimension
open _root_.D11.Ch03

def ambientBoundStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ E : Set (Point n),
    DimensionDefinition.dimensionValue E ≤ (n : ℝ≥0∞)

def openSetStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ U : Set (Point n), IsOpen U → U.Nonempty →
    DimensionDefinition.dimensionValue U = (n : ℝ≥0∞) ∧
      ∀ s : ℝ≥0, s < (n : ℝ≥0) →
        HausdorffOuterMeasure.outerMeasureValue s U = ∞

def higherExponentStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ s : ℝ≥0, (n : ℝ≥0) < s →
    HausdorffOuterMeasure.outerMeasureValue s (univ : Set (Point n)) = 0

/-- The range of an arbitrary isometric embedding of a closed, positive-side
`k`-cube, for every `1 ≤ k ≤ n`. Translations and rotations are included. -/
def embeddedCubeStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n →
    ∀ (r : ℝ≥0), 0 < r →
    ∀ f : {x : Point k // x ∈ closedBox (0 : Fin k → ℝ) (fun _ => (r : ℝ))} → Point n,
      Isometry f →
      DimensionDefinition.dimensionValue (range f) = (k : ℝ≥0∞) ∧
      0 < HausdorffOuterMeasure.outerMeasureValue (k : ℝ≥0) (range f) ∧
      HausdorffOuterMeasure.outerMeasureValue (k : ℝ≥0) (range f) < ∞

/-- The zero-dimensional cube boundary, including the exact counting mass. -/
def singletonStatement : Prop :=
  ∀ (n : ℕ) (x : Point n),
    DimensionDefinition.dimensionValue ({x} : Set (Point n)) = 0 ∧
      HausdorffOuterMeasure.outerMeasureValue 0 ({x} : Set (Point n)) = 1

end Specs.D11.Ch22.EuclideanDimension
