import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Bases

/-! Independent statements for the standard-basis clauses of
`fa2:p1:c15:canonical`, paper.tex 3941–3967. Natural index n denotes the
source's positive index n+1. All norms are the canonical sequence norms.
The finite extended exponents p ≥ 1 include ENNReal.ofReal r for every
real r ≥ 1, including r = 1. No basis of all of ℓ∞ is asserted. -/

open Filter Topology TopologicalSpace
open scoped BigOperators ENNReal
noncomputable section
universe u v
namespace ExpandedFA.P1.C15Canonical.Spec
open C01SequenceSpaces

/-- The usual coordinate vector, in the native subspace of bounded null sequences. -/
def c0Unit (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : SequenceC0 𝕜 :=
  ⟨lp.single ∞ n 1, by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with k hk
    exact (lp.single_apply_ne (E := fun _ : ℕ => 𝕜) ∞ n 1 (ne_of_gt hk)).symm⟩

def LpBasis : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜)
      (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1)

def C0Basis : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (c0Unit 𝕜)

def LpCoordinates : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜)
      (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1))
    (x : SequenceLp 𝕜 p) (n : ℕ), C15Basis.Spec.rawCoordinates h x n = x n

def C0Coordinates : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (c0Unit 𝕜))
    (x : SequenceC0 𝕜) (n : ℕ), C15Basis.Spec.rawCoordinates h x n = x.val n

/-- Continuous realizations of the source partial sums, with their actual norms
and bounded supremum. The empty initial projection is zero. -/
def ConstantOne {𝕜 E : Type u} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {e : ℕ → E} (h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e) : Prop :=
  ∃ T : ℕ → E →L[𝕜] E,
    (∀ N x, T N x = C15Basis.Spec.rawPartialSum h N x) ∧
    T 0 = 0 ∧ (∀ N, ‖T (N + 1)‖ = 1) ∧
    BddAbove (Set.range fun N => ‖T N‖) ∧ (⨆ N, ‖T N‖) = 1

def LpBasisConstant : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜)
      (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1)), ConstantOne h

def C0BasisConstant : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (c0Unit 𝕜)), ConstantOne h

/-- Closed linear span in ℓ∞, with its supremum norm topology. -/
def ClosedSpanInLInfinity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (Submodule.span 𝕜 (Set.range fun n : ℕ =>
      lp.single (E := fun _ : ℕ => 𝕜) ∞ n 1)).topologicalClosure = sequenceC0Submodule 𝕜


/-- Type and value of the canonical null-sequence unit vector. -/
def C0UnitType := ∀ (𝕜 : Type u) [RCLike 𝕜], ℕ → SequenceC0 𝕜
def C0UnitValue : C0UnitType := c0Unit

def CountableBasisSeparable : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (e : ℕ → E),
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e → SeparableSpace E

def FiniteBasisSeparable : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (d : ℕ) (e : Fin d → E),
    C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e → SeparableSpace E

/-- Every binary sequence occurs, and distinct sequences have sup-distance one.
The range is explicitly uncountable. -/
def BinarySeparatedFamily : Prop := by
  classical
  exact ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ F : Set ℕ → SequenceLInfinity 𝕜,
      (∀ A n, F A n = if n ∈ A then 1 else 0) ∧
      Function.Injective F ∧
      (∀ A B, A ≠ B → dist (F A) (F B) = 1) ∧
      ¬ (Set.range F).Countable

def LInfinityNonseparable : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ SeparableSpace (SequenceLInfinity 𝕜)

/-- Excludes every ordered Schauder sequence, and every finite basis. -/
def LInfinityNoBasis : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ e : ℕ → SequenceLInfinity 𝕜,
      ¬ C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e) ∧
    (∀ (d : ℕ) (e : Fin d → SequenceLInfinity 𝕜),
      ¬ C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e)

/-- The complete proposition, using the upstream native c₀ and ℓᵖ objects and
its exact quantitative basis-constant statement. -/
def StandardBases : Prop :=
  LpBasis.{u} ∧
  C0Basis.{u} ∧
  LpBasisConstant.{u} ∧
  C0BasisConstant.{u} ∧
  ClosedSpanInLInfinity.{u} ∧
  LInfinityNoBasis.{u}

end ExpandedFA.P1.C15Canonical.Spec
