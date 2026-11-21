import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Independent statements for `fa2:p1:c07:incomplete-counterexample`, paper.tex
1506–1517. The domain is the finite-support subspace of the canonical ℓ∞,
with its inherited supremum norm, metric and topology. Scalars may be real or
complex. Coordinate `j : ℕ` represents manuscript coordinate `j+1`.
The weighted-coordinate family uses positive indices; partial sums also include
the empty sum at `n=0`. No completeness hypothesis is placed on the domain.
-/
noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C07IncompleteCounterexample
open C01SequenceSpaces

def c00SupSubmodule (𝕜 : Type u) [RCLike 𝕜] : Submodule 𝕜 (SequenceLInfinity 𝕜) :=
  (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞).range

abbrev C00Sup (𝕜 : Type u) [RCLike 𝕜] := ↥(c00SupSubmodule 𝕜)

/-- The same algebraic finite-support sequences, now with the supremum norm. -/
def c00SupEquiv (𝕜 : Type u) [RCLike 𝕜] : SequenceC00 𝕜 ≃ₗ[𝕜] C00Sup 𝕜 :=
  LinearEquiv.ofBijective (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞).rangeRestrict
    ⟨by
      intro x y h
      apply Finsupp.ext
      intro j
      exact congrArg (fun z : C00Sup 𝕜 => z.val j) h,
    LinearMap.surjective_rangeRestrict _⟩

def partialSumValue (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : C00Sup 𝕜 →L[𝕜] 𝕜 :=
  (∑ j ∈ Finset.range n, lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ j).domRestrict
    (c00SupSubmodule 𝕜)

/-- Summing over a finite support defines an algebraic linear functional. -/
def sumValue (𝕜 : Type u) [RCLike 𝕜] : C00Sup 𝕜 →ₗ[𝕜] 𝕜 :=
  (Finsupp.lsum 𝕜 (fun _ : ℕ => LinearMap.id : ℕ → 𝕜 →ₗ[𝕜] 𝕜)).comp
    (c00SupEquiv 𝕜).symm.toLinearMap

def onesBlock (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : C00Sup 𝕜 :=
  c00SupEquiv 𝕜 (∑ j ∈ Finset.range n, Finsupp.single j 1)

/-- Positive manuscript index `n` evaluates natural coordinate `n-1`. -/
def weightedCoordinateValue (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+) : C00Sup 𝕜 →L[𝕜] 𝕜 :=
  (n.val : 𝕜) • ((lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ (n.val - 1)).domRestrict
    (c00SupSubmodule 𝕜))

namespace Spec

def WeightedCoordinateType := ∀ (𝕜 : Type u) [RCLike 𝕜], ℕ+ → C00Sup 𝕜 →L[𝕜] 𝕜
def WeightedCoordinateValue : WeightedCoordinateType := weightedCoordinateValue

def WeightedCoordinateFormula : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+) (x : C00Sup 𝕜),
    weightedCoordinateValue 𝕜 n x = (n.val : 𝕜) * x.val (n.val - 1)

def WeightedCoordinateNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+), ‖weightedCoordinateValue 𝕜 n‖ = (n.val : ℝ)

def EventuallyZero : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (x : C00Sup 𝕜),
  ∀ᶠ n : ℕ+ in atTop, weightedCoordinateValue 𝕜 n x = 0

def PointwiseConvergence : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (x : C00Sup 𝕜),
  Tendsto (fun n : ℕ+ => weightedCoordinateValue 𝕜 n x) atTop (𝓝 0)

def PointwiseBounded : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (x : C00Sup 𝕜),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ+, ‖weightedCoordinateValue 𝕜 n x‖ ≤ C

def UnboundedNorms : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (C : ℝ),
  ∃ n : ℕ+, C < ‖weightedCoordinateValue 𝕜 n‖

def PartialSumType := ∀ (𝕜 : Type u) [RCLike 𝕜], ℕ → C00Sup 𝕜 →L[𝕜] 𝕜
def PartialSumValue : PartialSumType := partialSumValue

def SumType := ∀ (𝕜 : Type u) [RCLike 𝕜], C00Sup 𝕜 →ₗ[𝕜] 𝕜
def SumValue : SumType := sumValue

/-- Explicit coordinate and norm bridge to the shared scalar sequence objects. -/
def DomainIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ (x : SequenceC00 𝕜) j, (c00SupEquiv 𝕜 x).val j = x j) ∧
    (∀ x : C00Sup 𝕜, ‖x‖ = ⨆ j, ‖x.val j‖) ∧
    (∀ x : SequenceLInfinity 𝕜,
      x ∈ c00SupSubmodule 𝕜 ↔ (Function.support (fun j => x j)).Finite)

def Formulas : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ n (x : C00Sup 𝕜), partialSumValue 𝕜 n x = ∑ j ∈ Finset.range n, x.val j) ∧
    (∀ x : SequenceC00 𝕜, sumValue 𝕜 (c00SupEquiv 𝕜 x) = x.sum (fun _ a => a))

def PartialSumNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ), ‖partialSumValue 𝕜 n‖ = (n : ℝ)

def PointwiseLimit : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : C00Sup 𝕜),
    Tendsto (fun n => partialSumValue 𝕜 n x) atTop (𝓝 (sumValue 𝕜 x))

/-- The precise witnesses printed in the source; the unit-norm clause requires
`n>0`, while the coordinate and value formulas include `n=0`. -/
def Witnesses : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ),
    (∀ j, (onesBlock 𝕜 n).val j = if j < n then 1 else 0) ∧
    (0 < n → ‖onesBlock 𝕜 n‖ = 1) ∧
    sumValue 𝕜 (onesBlock 𝕜 n) = (n : 𝕜) ∧
    partialSumValue 𝕜 n (onesBlock 𝕜 n) = (n : 𝕜)

def UnboundedLimit : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : C00Sup 𝕜, ‖sumValue 𝕜 x‖ ≤ C * ‖x‖) ∧
    (¬ Continuous (sumValue 𝕜)) ∧
    (¬ Bornology.IsBounded (sumValue 𝕜 '' Metric.closedBall (0 : C00Sup 𝕜) 1))

def Completeness : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], (¬ CompleteSpace (C00Sup 𝕜)) ∧ CompleteSpace 𝕜

end Spec
end ExpandedFA.P1.C07IncompleteCounterexample
