import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion

/-!
Independent statements for paper.tex:959–976. The full Lebesgue space is
the Carathéodory space of covering outer volume, rather than a completion
by definition. The completion here is that of its Borel restriction.
Equality of spaces and equality of values on all their measurable sets
identify the two measure spaces, including sets of infinite measure.
-/

noncomputable section

open Set MeasureTheory

namespace Specs.D11.Ch03.LebesgueCompletion

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def completion_space : Prop :=
  ∀ (d : ℕ) [NeZero d],
    lebesgueSpace_value d =
      Specs.D11.Ch02.Completion.completedSpace_value (borelMeasure_value d)

def completion_value : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    MeasurableSet[lebesgueSpace_value d] E →
      lebesgue_value d E =
        Specs.D11.Ch02.Completion.completedMeasure_value (borelMeasure_value d) E

/-- The full identification of the sigma-algebras and measures. -/
def lebesgue_completion : Prop :=
  ∀ (d : ℕ) [NeZero d],
    lebesgueSpace_value d =
        Specs.D11.Ch02.Completion.completedSpace_value (borelMeasure_value d) ∧
    ∀ E : Set (Point d), MeasurableSet[lebesgueSpace_value d] E →
      lebesgue_value d E =
        Specs.D11.Ch02.Completion.completedMeasure_value (borelMeasure_value d) E

/-- An arbitrary subset of a Borel null set may be adjoined to a Borel set;
the converse characterizes every Lebesgue set. No Borel premise is put on Z. -/
def borel_mod_null_iff : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    MeasurableSet[lebesgueSpace_value d] E ↔
      ∃ B N Z : Set (Point d),
        MeasurableSet[borel (Point d)] B ∧
        MeasurableSet[borel (Point d)] N ∧ borelMeasure_value d N = 0 ∧
        Z ⊆ N ∧ E = B ∪ Z

end Specs.D11.Ch03.LebesgueCompletion
