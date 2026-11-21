import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Oscillation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.CompactInterval

/-!
Independent specification of the oscillation-set portion of
K03.08.oscillation_criterion, paper.tex:2211–2221.

Oscillation uses the canonical extended nonnegative suprema and infima from
Ch02. The finite bound below ensures that for bounded real functions these
values are finite. Neighborhoods include the base point, and continuity at
both endpoints is relative to the closed interval. The superlevel and
discontinuity sets are subsets of the interval, considered in ambient ℝ.
The natural index n in the union represents the source's positive index n+1.
-/
namespace Specs.SingleVariableAnalysis.Ch08.OscillationSets

open Specs.SingleVariableAnalysis.Ch02.Oscillation
open scoped ENNReal

def intervalOscillationType := (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ≥0∞

noncomputable def intervalOscillationValue : intervalOscillationType :=
  fun f a b x => localOscillationValue f (Set.Icc a b) x

def oscillationSuperlevelType := (ℝ → ℝ) → ℝ → ℝ → ℝ → Set ℝ

noncomputable def oscillationSuperlevelValue : oscillationSuperlevelType :=
  fun f a b α => {x | x ∈ Set.Icc a b ∧ ENNReal.ofReal α ≤ intervalOscillationValue f a b x}

def intervalDiscontinuitiesType := (ℝ → ℝ) → ℝ → ℝ → Set ℝ

def intervalDiscontinuitiesValue : intervalDiscontinuitiesType :=
  fun f a b => {x | x ∈ Set.Icc a b ∧ ¬ ContinuousWithinAt f (Set.Icc a b) x}

def intervalOscillationFormula : Prop :=
  ∀ (f : ℝ → ℝ) (a b x : ℝ),
    intervalOscillationValue f a b x =
      ⨅ r : {r : ℝ // 0 < r},
        oscillationValue f (Set.Ioo (x - r.val) (x + r.val) ∩ Set.Icc a b)

def intervalOscillationBound : Prop :=
  ∀ (f : ℝ → ℝ) (a b M : ℝ), (∀ y ∈ Set.Icc a b, |f y| ≤ M) →
    ∀ x : ℝ, intervalOscillationValue f a b x ≤ ENNReal.ofReal (2 * M)

def intervalOscillationFinite : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), (∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M) →
    ∀ x : ℝ, intervalOscillationValue f a b x ≠ ⊤

def intervalOscillationZeroIffContinuous : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), (∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M) →
    ∀ x ∈ Set.Icc a b,
      intervalOscillationValue f a b x = 0 ↔ ContinuousWithinAt f (Set.Icc a b) x

def oscillationSuperlevelClosed : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), (∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M) →
    ∀ α : ℝ, 0 < α → IsClosed (oscillationSuperlevelValue f a b α)

def oscillationSuperlevelCompact : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), (∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M) →
    ∀ α : ℝ, 0 < α → IsCompact (oscillationSuperlevelValue f a b α)

def intervalDiscontinuitiesEqUnion : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), (∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M) →
    intervalDiscontinuitiesValue f a b =
      ⋃ n : ℕ, oscillationSuperlevelValue f a b (1 / ((n : ℝ) + 1))

end Specs.SingleVariableAnalysis.Ch08.OscillationSets
