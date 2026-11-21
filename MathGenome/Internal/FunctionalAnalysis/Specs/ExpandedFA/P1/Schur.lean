import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.ContinuousMap.Compact

/-! Independent statements for paper.tex 3222–3227 (`fa2:p1:schur`).
Weak convergence and weak Cauchy sequences are tested against every continuous
scalar-linear functional. These definitions use the canonical sequence spaces,
with natural coordinate n representing manuscript coordinate n+1. -/

open Filter
open scoped Topology ENNReal
universe u v
namespace ExpandedFA.P1.Schur
open C01SequenceSpaces

/-- Convergence against the continuous linear dual, over either scalar field. -/
def WeakConverges (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : ℕ → E) (l : E) : Prop :=
  ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (x n)) atTop (𝓝 (f l))

/-- Every scalar test of the sequence is Cauchy. -/
def WeakCauchy (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : ℕ → E) : Prop :=
  ∀ f : E →L[𝕜] 𝕜, CauchySeq (fun n => f (x n))

/-- Every weakly Cauchy sequence has a weak limit in the same space. -/
def WeakSequentiallyComplete (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∀ x : ℕ → E, WeakCauchy 𝕜 x → ∃ l : E, WeakConverges 𝕜 x l

namespace Spec

def SchurProperty : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : ℕ → SequenceLp 𝕜 1) (l : SequenceLp 𝕜 1),
    WeakConverges 𝕜 x l → Tendsto x atTop (𝓝 l)

def L1WeakSequentialCompleteness : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], WeakSequentiallyComplete 𝕜 (SequenceLp 𝕜 1)

def C0NotWeakSequentiallyComplete : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ WeakSequentiallyComplete 𝕜 (SequenceC0 𝕜)

def ContinuousNotWeakSequentiallyComplete : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ WeakSequentiallyComplete 𝕜 C(Set.Icc (0 : ℝ) 1, 𝕜)

end Spec
end ExpandedFA.P1.Schur
