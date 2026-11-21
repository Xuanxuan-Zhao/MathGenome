import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.AbsoluteUnconditionalBoundary

/-!
Independent statements for paper.tex 3985–3997, with its counterexample at
4021–4024. Index i : ℕ represents manuscript index i+1; a tail after the
first N terms therefore has N ≤ i. A subseries is the original ordered
series with terms outside an arbitrary subset replaced by zero. This
includes empty and finite subsets. A rearrangement is any permutation,
and its convergence hypothesis does not prescribe its limit.

The stronger additive-group formulation applies to both real and complex
Banach spaces, including the zero space. All notions of convergence below
are the accepted upstream notions in the displayed norm.
-/

noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.P1.C15UnconditionalCriteria.Spec

open C15Unconditional.Spec C01Banach.Spec

def FiniteTailConditionType :=
  ∀ {E : Type*} [NormedAddCommGroup E], (ℕ → E) → Prop

def FiniteTailConditionValue : FiniteTailConditionType :=
  fun {_} [_] v => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ F : Finset ℕ,
    (∀ i ∈ F, N ≤ i) → ‖finiteSubsumValue v F‖ < ε

def EverySubseriesConvergesType :=
  ∀ {E : Type*} [NormedAddCommGroup E], (ℕ → E) → Prop

def EverySubseriesConvergesValue : EverySubseriesConvergesType :=
  fun {E} [_] v => ∀ A : Set ℕ, SequentiallySummableValue E (A.indicator v)

def EveryRearrangementConvergesType :=
  ∀ {E : Type*} [NormedAddCommGroup E], (ℕ → E) → Prop

def EveryRearrangementConvergesValue : EveryRearrangementConvergesType :=
  fun {E} [_] v => ∀ σ : Equiv.Perm ℕ, SequentiallySummableValue E (v ∘ σ)

def CauchyTailCriterion : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (v : ℕ → E),
    CauchySeq (finiteSubsumValue v) ↔ FiniteTailConditionValue v

def UnconditionalTailCriterion : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (v : ℕ → E),
    UnconditionallyConvergentValue v ↔ FiniteTailConditionValue v

def SubseriesCriterion : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (v : ℕ → E),
    UnconditionallyConvergentValue v ↔ EverySubseriesConvergesValue v

def RearrangementCriterion : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (v : ℕ → E),
    UnconditionallyConvergentValue v ↔ EveryRearrangementConvergesValue v

def UnconditionalCriteria : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (v : ℕ → E),
    (UnconditionallyConvergentValue v ↔ FiniteTailConditionValue v) ∧
    (FiniteTailConditionValue v ↔ EverySubseriesConvergesValue v) ∧
    (FiniteTailConditionValue v ↔ EveryRearrangementConvergesValue v)

def RearrangementPreservesSum : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (v : ℕ → E) (x : E),
    HasUnconditionalSumValue v x → ∀ σ : Equiv.Perm ℕ,
      HasSequentialSumValue E (v ∘ σ) x

def RearrangementsHaveSameSum : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (v : ℕ → E),
    EveryRearrangementConvergesValue v → ∃ x : E,
      HasUnconditionalSumValue v x ∧
      ∀ σ : Equiv.Perm ℕ, HasSequentialSumValue E (v ∘ σ) x

/-- The original absolute implication and explicit canonical Hilbert-space
counterexample, reusing the independent accepted boundary specification. -/
def AbsoluteImpliesUnconditional : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (v : ℕ → E),
    AbsolutelySummableValue E v → UnconditionallyConvergentValue v

def HilbertConverseFails : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜],
    UnconditionallyConvergentValue (AbsoluteUnconditionalBoundary.harmonicTerm 𝕜) ∧
    ¬ AbsolutelySummableValue (C01SequenceSpaces.SequenceLp 𝕜 2)
      (AbsoluteUnconditionalBoundary.harmonicTerm 𝕜) ∧
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ‖AbsoluteUnconditionalBoundary.harmonicTerm 𝕜 n‖) atTop atTop

end ExpandedFA.P1.C15UnconditionalCriteria.Spec
