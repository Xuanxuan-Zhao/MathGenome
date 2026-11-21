import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statements for paper.tex:977–998. `Point d` is Euclidean
R^d, `coveringOuter` is the open-box covering outer measure, `lebesgue_value`
is its full Carathéodory restriction, and `borelMeasure_value` is its Borel
restriction. The two-sided assertions require a nonzero scale. -/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch03.TranslationDilation

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def outer_affine : Prop :=
  ∀ (d : ℕ) [NeZero d] (a : Point d) (r : ℝ) (E : Set (Point d)),
    coveringOuter d ((fun x => a + r • x) '' E) =
      ENNReal.ofReal (|r| ^ d) * coveringOuter d E

def borel_image_iff : Prop :=
  ∀ (d : ℕ) [NeZero d] (a : Point d) (r : ℝ), r ≠ 0 →
    ∀ E : Set (Point d),
      MeasurableSet[borel (Point d)] ((fun x => a + r • x) '' E) ↔
        MeasurableSet[borel (Point d)] E

def lebesgue_image_iff : Prop :=
  ∀ (d : ℕ) [NeZero d] (a : Point d) (r : ℝ), r ≠ 0 →
    ∀ E : Set (Point d),
      MeasurableSet[lebesgueSpace_value d] ((fun x => a + r • x) '' E) ↔
        MeasurableSet[lebesgueSpace_value d] E

def borel_affine : Prop :=
  ∀ (d : ℕ) [NeZero d] (a : Point d) (r : ℝ) (E : Set (Point d)),
    MeasurableSet[borel (Point d)] E →
      MeasurableSet[borel (Point d)] ((fun x => a + r • x) '' E) ∧
        borelMeasure_value d ((fun x => a + r • x) '' E) =
          ENNReal.ofReal (|r| ^ d) * borelMeasure_value d E

def lebesgue_affine : Prop :=
  ∀ (d : ℕ) [NeZero d] (a : Point d) (r : ℝ) (E : Set (Point d)),
    MeasurableSet[lebesgueSpace_value d] E →
      MeasurableSet[lebesgueSpace_value d] ((fun x => a + r • x) '' E) ∧
        lebesgue_value d ((fun x => a + r • x) '' E) =
          ENNReal.ofReal (|r| ^ d) * lebesgue_value d E

def zero_image : Prop :=
  ∀ (d : ℕ) [NeZero d] (a : Point d) (E : Set (Point d)),
    (E = ∅ ∧ (fun x => a + (0 : ℝ) • x) '' E = ∅) ∨
      (E.Nonempty ∧ (fun x => a + (0 : ℝ) • x) '' E = {a})

/-- No measurability hypothesis on E is made at scale zero. In particular,
this is a forward assertion, with no reverse measurability assertion. -/
def zero_image_measurable_null : Prop :=
  ∀ (d : ℕ) [NeZero d] (a : Point d) (E : Set (Point d)),
    let F := (fun x => a + (0 : ℝ) • x) '' E
    MeasurableSet[borel (Point d)] F ∧
      MeasurableSet[lebesgueSpace_value d] F ∧ coveringOuter d F = 0 ∧
        borelMeasure_value d F = 0 ∧ lebesgue_value d F = 0

end Specs.D11.Ch03.TranslationDilation
