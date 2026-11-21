import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Radius
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Nat.Choose.Sum

/-!
K03.13.composition, paper.tex:1422–1430: recentering only.
Centers d,b are real; complex arguments remain available for bounds.
The coefficient formula sums over all naturals: terms n<k vanish because
Nat.choose n k=0, so this is exactly the source sum over n≥k.
The coefficient convergence assertion also explicitly uses the tail n+k.
The conclusions identify ordinary numerical sums, not a total default value.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Recentering
open PowerSeries
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open scoped BigOperators ENNReal

def realRecenteredCoefficientType := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ
noncomputable def realRecenteredCoefficientValue : realRecenteredCoefficientType :=
  fun a d b k => ∑' n, (n.choose k : ℝ) * a n * (b-d)^(n-k)

def complexRecenteredCoefficientType := (ℕ → ℂ) → ℝ → ℝ → ℕ → ℂ
noncomputable def complexRecenteredCoefficientValue : complexRecenteredCoefficientType :=
  fun a d b k => ∑' n, (n.choose k : ℂ) * a n * ((b-d : ℝ) : ℂ)^(n-k)

def realCoefficientConvergence : Prop := ∀ (a : ℕ → ℝ) (d b : ℝ),
  ENNReal.ofReal |b-d| < realPowerSeriesRadiusValue a → ∀ k : ℕ,
  realSeriesHasSumValue (fun n => ((n+k).choose k : ℝ) * a (n+k) * (b-d)^n)
    (realRecenteredCoefficientValue a d b k) ∧
  realSeriesConvergesValue (fun n => |((n+k).choose k : ℝ) * a (n+k) * (b-d)^n|)

def complexCoefficientConvergence : Prop := ∀ (a : ℕ → ℂ) (d b : ℝ),
  ENNReal.ofReal |b-d| < complexPowerSeriesRadiusValue a → ∀ k : ℕ,
  complexSeriesHasSumValue (fun n => ((n+k).choose k : ℂ) * a (n+k) * ((b-d : ℝ) : ℂ)^n)
    (complexRecenteredCoefficientValue a d b k) ∧
  realSeriesConvergesValue (fun n => ‖((n+k).choose k : ℂ) * a (n+k) * ((b-d : ℝ) : ℂ)^n‖)

def realDoubleMajorant : Prop := ∀ (a : ℕ → ℝ) (d b h : ℝ),
  ENNReal.ofReal (|b-d|+|h|) < realPowerSeriesRadiusValue a →
  Summable (fun p : ℕ × ℕ => |(p.1.choose p.2 : ℝ) * a p.1 * (b-d)^(p.1-p.2) * h^p.2|) ∧
  (∑' n, ∑ k ∈ Finset.range (n+1),
    |a n| * (n.choose k : ℝ) * |b-d|^(n-k) * |h|^k) =
    ∑' n, |a n| * (|b-d|+|h|)^n

def complexDoubleMajorant : Prop := ∀ (a : ℕ → ℂ) (d b : ℝ) (h : ℂ),
  ENNReal.ofReal (|b-d|+‖h‖) < complexPowerSeriesRadiusValue a →
  Summable (fun p : ℕ × ℕ => ‖(p.1.choose p.2 : ℂ) * a p.1 *
    ((b-d : ℝ) : ℂ)^(p.1-p.2) * h^p.2‖) ∧
  (∑' n, ∑ k ∈ Finset.range (n+1),
    ‖a n‖ * (n.choose k : ℝ) * |b-d|^(n-k) * ‖h‖^k) =
    ∑' n, ‖a n‖ * (|b-d|+‖h‖)^n

def realRecentering : Prop := ∀ (a : ℕ → ℝ) (d b h : ℝ),
  ENNReal.ofReal (|b-d|+|h|) < realPowerSeriesRadiusValue a →
  ∃ S : ℝ, RealPowerSeriesHasSumValue a d (b+h) S ∧
    RealPowerSeriesHasSumValue (realRecenteredCoefficientValue a d b) b (b+h) S ∧
    RealPowerSeriesAbsolutelyConvergesValue (realRecenteredCoefficientValue a d b) b (b+h)

def complexRecentering : Prop := ∀ (a : ℕ → ℂ) (d b : ℝ) (h : ℂ),
  ENNReal.ofReal (|b-d|+‖h‖) < complexPowerSeriesRadiusValue a →
  ∃ S : ℂ, ComplexPowerSeriesHasSumValue a d ((b : ℂ)+h) S ∧
    ComplexPowerSeriesHasSumValue (complexRecenteredCoefficientValue a d b) b ((b : ℂ)+h) S ∧
    ComplexPowerSeriesAbsolutelyConvergesValue (complexRecenteredCoefficientValue a d b) b ((b : ℂ)+h)

def realPositiveNeighborhood : Prop := ∀ (a : ℕ → ℝ) (d b : ℝ),
  ENNReal.ofReal |b-d| < realPowerSeriesRadiusValue a →
  ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (|b-d|+r) < realPowerSeriesRadiusValue a ∧
    ∀ h : ℝ, |h| < r → ∃ S : ℝ,
      RealPowerSeriesHasSumValue a d (b+h) S ∧
      RealPowerSeriesHasSumValue (realRecenteredCoefficientValue a d b) b (b+h) S ∧
      RealPowerSeriesAbsolutelyConvergesValue (realRecenteredCoefficientValue a d b) b (b+h)

def complexPositiveNeighborhood : Prop := ∀ (a : ℕ → ℂ) (d b : ℝ),
  ENNReal.ofReal |b-d| < complexPowerSeriesRadiusValue a →
  ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (|b-d|+r) < complexPowerSeriesRadiusValue a ∧
    ∀ h : ℂ, ‖h‖ < r → ∃ S : ℂ,
      ComplexPowerSeriesHasSumValue a d ((b : ℂ)+h) S ∧
      ComplexPowerSeriesHasSumValue (complexRecenteredCoefficientValue a d b) b ((b : ℂ)+h) S ∧
      ComplexPowerSeriesAbsolutelyConvergesValue (complexRecenteredCoefficientValue a d b) b ((b : ℂ)+h)
end Specs.SingleVariableAnalysis.Ch13.Recentering
