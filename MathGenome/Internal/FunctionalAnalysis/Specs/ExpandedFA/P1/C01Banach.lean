import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
Independent interface for Definition `fa2:p1:c01:banach`, paper.tex lines 160–165.

We relabel manuscript x₁, x₂, … by u 0, u 1, …, respectively; hence the
first N terms are `∑ n ∈ Finset.range N, u n`. For a positive-indexed
sequence presented as x : ℕ → E (with x 0 unused), substitute u n = x (n+1).
These are ordered initial sums. General series convergence is not defined
using the unconditional finite-subset notion `HasSum` or `Summable`.
Only the nonnegative real series of norms uses `Summable`.

The definitions need only a normed additive commutative group, and therefore
apply in particular to every real or complex normed vector space with the
canonical norm, metric, and topology fixed by C01Norm. No completeness
or nontriviality assumption is imposed on E.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C01Banach.Spec

def NormCauchySequenceType :=
  ∀ (E : Type*) [NormedAddCommGroup E], (ℕ → E) → Prop

/-- The Cauchy condition in the displayed norm. -/
def NormCauchySequenceValue : NormCauchySequenceType :=
  fun _ _ u => ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖u m - u n‖ < ε

def NormConvergesToType :=
  ∀ (E : Type*) [NormedAddCommGroup E], (ℕ → E) → E → Prop

/-- Convergence to a vector in the displayed norm. -/
def NormConvergesToValue : NormConvergesToType :=
  fun _ _ u a => ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ‖u n - a‖ < ε

def IsBanachSpaceType :=
  ∀ (E : Type*) [NormedAddCommGroup E], Prop

/-- Every norm Cauchy sequence converges in this space. No nontriviality is required. -/
def IsBanachSpaceValue : IsBanachSpaceType :=
  fun E _ => ∀ u : ℕ → E, NormCauchySequenceValue E u →
    ∃ a : E, NormConvergesToValue E u a

def seriesPartialSumsType :=
  ∀ (E : Type*) [NormedAddCommGroup E], (ℕ → E) → ℕ → E

/-- The sum of the first N terms; at N = 0 it is zero. -/
def seriesPartialSumsValue : seriesPartialSumsType :=
  fun _ _ u N => ∑ n ∈ Finset.range N, u n

def HasSequentialSumType :=
  ∀ (E : Type*) [NormedAddCommGroup E], (ℕ → E) → E → Prop

/-- An ordered series converges to a when its finite initial sums converge in norm. -/
def HasSequentialSumValue : HasSequentialSumType :=
  fun E _ u a => NormConvergesToValue E
    (seriesPartialSumsValue E u) a

def SequentiallySummableType :=
  ∀ (E : Type*) [NormedAddCommGroup E], (ℕ → E) → Prop

/-- Existence of a limit of the ordered partial sums, allowing conditional convergence. -/
def SequentiallySummableValue : SequentiallySummableType :=
  fun E _ u => ∃ a : E, HasSequentialSumValue E u a

def AbsolutelySummableType :=
  ∀ (E : Type*) [NormedAddCommGroup E], (ℕ → E) → Prop

/-- Absolute norm summability; the real nonnegative series has a finite sum. -/
def AbsolutelySummableValue : AbsolutelySummableType :=
  fun _ _ u => Summable (fun n => ‖u n‖)

def NormCauchySequenceIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] (u : ℕ → E),
    NormCauchySequenceValue E u ↔ CauchySeq u

def NormConvergenceIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] (u : ℕ → E) (a : E),
    NormConvergesToValue E u a ↔ Tendsto u atTop (𝓝 a)

def BanachIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E],
    IsBanachSpaceValue E ↔ CompleteSpace E

def SequentialSumIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] (u : ℕ → E) (a : E),
    HasSequentialSumValue E u a ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, u n) atTop (𝓝 a)

def SequentialSummabilityIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] (u : ℕ → E),
    SequentiallySummableValue E u ↔
      ∃ a : E, Tendsto (fun N => ∑ n ∈ Finset.range N, u n) atTop (𝓝 a)

def AbsoluteSummabilityIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] (u : ℕ → E),
    AbsolutelySummableValue E u ↔
      ∃ r : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, ‖u n‖) atTop (𝓝 r)

def AbsoluteSeriesBridge : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] (u : ℕ → E) (a : E),
    AbsolutelySummableValue E u →
      (HasSequentialSumValue E u a ↔ HasSum u a)

end ExpandedFA.P1.C01Banach.Spec
