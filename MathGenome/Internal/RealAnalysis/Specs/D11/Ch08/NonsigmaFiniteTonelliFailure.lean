import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductSigma
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Count

/-!
Independent specification of paper.tex:2846–2863. `unitInterval` is the
subtype of real numbers in `[0,1]`, with its Borel (subtype) sigma-algebra.
Its canonical volume is the pullback of real Borel Lebesgue measure, without
completion. The ordinary product measurable space is used throughout.

The integral below is the shared supremum over finite simple minorants;
the accepted upstream `NonnegativeIntegral.eq_lintegral` identifies it with
the library nonnegative integral. No product measure or Tonelli hypothesis
is assumed in these statements.
-/

open Set MeasureTheory
open scoped ENNReal unitInterval

noncomputable section

namespace D11.Ch08.NonsigmaFiniteTonelliFailure

abbrev Interval := unitInterval

/-- Borel Lebesgue measure on the closed unit interval. -/
abbrev borelLebesgue : Measure Interval := volume

/-- Counting measure on that same Borel sigma-algebra. -/
abbrev counting : Measure Interval := Measure.count

def intervalDiagonal : Set (Interval × Interval) := {p | p.1 = p.2}

def diagonalIndicator : Interval × Interval → ℝ≥0∞ :=
  intervalDiagonal.indicator (fun _ => 1)

end D11.Ch08.NonsigmaFiniteTonelliFailure

namespace Specs.D11.Ch08.NonsigmaFiniteTonelliFailure

open _root_.D11.Ch08.NonsigmaFiniteTonelliFailure

local notation "I₊" => Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value

def borel_structures : Prop :=
  (inferInstance : MeasurableSpace Interval) = borel Interval ∧
  (inferInstance : MeasurableSpace (Interval × Interval)) = borel (Interval × Interval)

def lebesgue_values : Prop :=
  (∀ A : Set Interval, MeasurableSet A → borelLebesgue A =
    (volume : Measure ℝ) (Subtype.val '' A)) ∧
  borelLebesgue univ = 1 ∧ ∀ x : Interval, borelLebesgue {x} = 0

def diagonal_closed : Prop := IsClosed intervalDiagonal

def indicator_measurable : Prop := Measurable diagonalIndicator

def section_masses : Prop :=
  (∀ x : Interval, {y : Interval | (x, y) ∈ intervalDiagonal} = {x} ∧
    counting {y : Interval | (x, y) ∈ intervalDiagonal} = 1) ∧
  (∀ y : Interval, {x : Interval | (x, y) ∈ intervalDiagonal} = {y} ∧
    borelLebesgue {x : Interval | (x, y) ∈ intervalDiagonal} = 0)

def section_integrals : Prop :=
  (∀ x : Interval, I₊ counting (fun y => diagonalIndicator (x, y)) = 1) ∧
  (∀ y : Interval, I₊ borelLebesgue (fun x => diagonalIndicator (x, y)) = 0)

def iterated_integrals : Prop :=
  I₊ borelLebesgue (fun x => I₊ counting (fun y => diagonalIndicator (x, y))) = 1 ∧
  I₊ counting (fun y => I₊ borelLebesgue (fun x => diagonalIndicator (x, y))) = 0

def finite_counting_iff : Prop :=
  ∀ A : Set Interval, MeasurableSet A → (counting A < ∞ ↔ A.Finite)

def not_sigmaFinite : Prop := ¬ SigmaFinite counting

def iterated_ne : Prop :=
  I₊ borelLebesgue (fun x => I₊ counting (fun y => diagonalIndicator (x, y))) ≠
  I₊ counting (fun y => I₊ borelLebesgue (fun x => diagonalIndicator (x, y)))

end Specs.D11.Ch08.NonsigmaFiniteTonelliFailure
