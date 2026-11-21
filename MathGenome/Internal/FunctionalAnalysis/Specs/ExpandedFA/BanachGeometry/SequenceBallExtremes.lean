import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Convex.Extreme

/-! The sequence-space assertions of `fa2:p2:classical-ball-extremes`,
paper.tex 8752–8778. Convexity is over ℝ, including for complex scalars.
The shared natural coordinate n represents manuscript coordinate n+1. -/
noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.BanachGeometry.SequenceBallExtremes
open ExpandedFA.P1.C01SequenceSpaces

/-- Convergent scalar sequences, with the inherited supremum norm. -/
def sequenceCSubmodule (𝕜 : Type u) [RCLike 𝕜] :
    Submodule 𝕜 (SequenceLInfinity 𝕜) where
  carrier := {x | ∃ a : 𝕜, Tendsto (fun n => x n) atTop (𝓝 a)}
  zero_mem' := ⟨0, tendsto_const_nhds⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, ha.add hb⟩
  smul_mem' := by
    rintro a x ⟨b, hb⟩
    exact ⟨a • b, hb.const_smul a⟩

abbrev SequenceC (𝕜 : Type u) [RCLike 𝕜] := ↥(sequenceCSubmodule 𝕜)

namespace Spec

def CType := ∀ (𝕜 : Type u) [RCLike 𝕜], Type u
def CValue : CType := fun 𝕜 _ => SequenceC 𝕜

/-- The bounded-sequence representation contains every convergent sequence,
and its norm is exactly the inherited supremum norm. -/
def ConvergentIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ x : ℕ → 𝕜,
      (∃ y : SequenceC 𝕜, (fun n => y.val n) = x) ↔
        ∃ a : 𝕜, Tendsto x atTop (𝓝 a)) ∧
    (∀ y : SequenceC 𝕜, ‖y‖ = ‖y.val‖ ∧ ‖y‖ = ⨆ n, ‖y.val n‖) ∧
    Isometry (fun y : SequenceC 𝕜 => y.val)

def InfinityExtremes : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : SequenceLInfinity 𝕜),
    x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔ ∀ n, ‖x n‖ = 1

def ConvergentExtremes : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : SequenceC 𝕜),
    letI : NormedSpace ℝ (SequenceC 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 _
    x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔ ∀ n, ‖x.val n‖ = 1

def C0Extremes : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    letI : NormedSpace ℝ (SequenceC0 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 _
    Set.extremePoints ℝ (Metric.closedBall (0 : SequenceC0 𝕜) 1) = ∅

def L1Extremes : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : SequenceLp 𝕜 1),
    x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔
      ∃ (n : ℕ) (a : 𝕜), ‖a‖ = 1 ∧ x = lp.single 1 n a

/-- Every norm-one vector, not only the canonical basis vectors. -/
def LpExtremes : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
    ∀ x : SequenceLp 𝕜 (ENNReal.ofReal p),
      x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔ ‖x‖ = 1

/-- In the real specialization the unit phases are precisely the two signs. -/
def RealPhases : Prop := ∀ a : ℝ, ‖a‖ = 1 ↔ a = -1 ∨ a = 1

def RealInfinityExtremes : Prop :=
  ∀ x : SequenceLInfinity ℝ,
    x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔
      ∀ n, x n = -1 ∨ x n = 1

def RealConvergentExtremes : Prop :=
  ∀ x : SequenceC ℝ,
    x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔
      ∀ n, x.val n = -1 ∨ x.val n = 1

def RealL1Extremes : Prop :=
  ∀ x : SequenceLp ℝ 1,
    x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔
      ∃ n : ℕ, x = lp.single 1 n 1 ∨ x = -(lp.single 1 n 1)

end Spec
end ExpandedFA.BanachGeometry.SequenceBallExtremes
