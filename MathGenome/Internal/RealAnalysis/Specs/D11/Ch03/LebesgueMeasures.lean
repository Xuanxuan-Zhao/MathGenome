import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.OuterVolume
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Independent interfaces for paper.tex:844–876. Dimensions are positive and
`Point d` has its Euclidean norm. The full measurable space is defined by the
covering outer measure's splitting test. The Borel measure uses native volume;
its agreement with that covering construction is a required theorem below.
No regularity or identification of a completion is assumed. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch03.LebesgueMeasures

open _root_.D11.Ch03

abbrev coveringOuter (d : ℕ) [NeZero d] :=
  Specs.D11.Ch03.OuterVolume.outerVolume_value d

def lebesgueSpace_type := (d : ℕ) → [NeZero d] → MeasurableSpace (Point d)
def lebesgueSpace_value : lebesgueSpace_type := fun d _ => (coveringOuter d).caratheodory

def lebesgue_type := (d : ℕ) → [NeZero d] → @Measure (Point d) (lebesgueSpace_value d)
noncomputable def lebesgue_value : lebesgue_type := fun d _ =>
  Specs.D11.Ch02.Caratheodory.measure_value (coveringOuter d)

def borelMeasure_type := (d : ℕ) → [NeZero d] → Measure (Point d)
noncomputable def borelMeasure_value : borelMeasure_type := fun _ _ => volume

def borel_structure : Prop := ∀ (d : ℕ),
  (inferInstance : MeasurableSpace (Point d)) = borel (Point d)

def borel_le_lebesgue : Prop := ∀ (d : ℕ) [NeZero d],
  borel (Point d) ≤ lebesgueSpace_value d

def measurable_iff : Prop := ∀ (d : ℕ) [NeZero d] (A : Set (Point d)),
  MeasurableSet[lebesgueSpace_value d] A ↔
    ∀ E, coveringOuter d E = coveringOuter d (E ∩ A) + coveringOuter d (E \ A)

def native_outer_agreement : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  volume E = coveringOuter d E

def lebesgue_apply : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  MeasurableSet[lebesgueSpace_value d] E → lebesgue_value d E = coveringOuter d E

def borel_apply : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  MeasurableSet[borel (Point d)] E → borelMeasure_value d E = coveringOuter d E

def borel_restriction : Prop := ∀ (d : ℕ) [NeZero d]
  (h : (inferInstance : MeasurableSpace (Point d)) ≤ lebesgueSpace_value d),
  (lebesgue_value d).trim h = borelMeasure_value d

def endpointBox_borel : Prop := ∀ (d : ℕ) [NeZero d] (a b : Fin d → ℝ)
  (lower upper : Fin d → Bool),
  MeasurableSet[borel (Point d)] (endpointBox a b lower upper)

def lebesgue_box : Prop := ∀ (d : ℕ) [NeZero d] (a b : Fin d → ℝ)
  (lower upper : Fin d → Bool),
  lebesgue_value d (endpointBox a b lower upper) = boxContent a b

def borel_box : Prop := ∀ (d : ℕ) [NeZero d] (a b : Fin d → ℝ)
  (lower upper : Fin d → Bool),
  borelMeasure_value d (endpointBox a b lower upper) = boxContent a b

def lebesgue_sigmaFinite : Prop := ∀ (d : ℕ) [NeZero d],
  @SigmaFinite (Point d) (lebesgueSpace_value d) (lebesgue_value d)

def borel_sigmaFinite : Prop := ∀ (d : ℕ) [NeZero d],
  SigmaFinite (borelMeasure_value d)

def lebesgue_complete : Prop := ∀ (d : ℕ) [NeZero d],
  @Measure.IsComplete (Point d) (lebesgueSpace_value d) (lebesgue_value d)

def singleton_outer_null : Prop := ∀ (d : ℕ) [NeZero d] (x : Point d),
  coveringOuter d {x} = 0

def countable_outer_null : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  E.Countable → coveringOuter d E = 0

def null_subset : Prop := ∀ (d : ℕ) [NeZero d] (N E : Set (Point d)),
  MeasurableSet[lebesgueSpace_value d] N → lebesgue_value d N = 0 → E ⊆ N →
    MeasurableSet[lebesgueSpace_value d] E ∧ lebesgue_value d E = 0

def countable_measurable_null : Prop := ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
  E.Countable → MeasurableSet[lebesgueSpace_value d] E ∧ lebesgue_value d E = 0

end Specs.D11.Ch03.LebesgueMeasures
