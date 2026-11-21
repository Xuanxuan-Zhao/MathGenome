import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statements for paper.tex 289–292. Natural coordinate `j` is
manuscript coordinate `j+1`; `range N` therefore retains the first N coordinates.
Every topology and distance below is that of the shared canonical norm. -/
noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.SequenceDensity
open C01SequenceSpaces

/-- The finite initial segment, as an actual finitely supported sequence. -/
def sequenceTruncation {𝕜 : Type u} [RCLike 𝕜] (x : ScalarSequence 𝕜)
    (N : ℕ) : SequenceC00 𝕜 :=
  ∑ j ∈ Finset.range N, Finsupp.single j (x j)

/-- Canonical pointwise inclusion into c₀, with its inherited supremum norm. -/
def sequenceFiniteInC0 (𝕜 : Type u) [RCLike 𝕜] (a : SequenceC00 𝕜) :
    SequenceC0 𝕜 :=
  ⟨C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ a, by
    apply tendsto_const_nhds.congr'
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [a.hasFiniteSupport.eventually_cofinite_notMem] with n hn
    change (0 : 𝕜) = a n
    simpa [Function.mem_support, eq_comm] using hn⟩

namespace Spec

def TruncationCoordinates : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : ScalarSequence 𝕜) (N j : ℕ),
    sequenceTruncation x N j = if j < N then x j else 0

def LpTruncationConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ x : SequenceLp 𝕜 p,
      Tendsto (fun N => C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p
        (sequenceTruncation (fun j => x j) N)) atTop (𝓝 x)

def C0TruncationConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : SequenceC0 𝕜),
    Tendsto (fun N => sequenceFiniteInC0 𝕜
      (sequenceTruncation (fun j => x.val j) N)) atTop (𝓝 x)

def LpDensity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    DenseRange (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p)

def C0Density : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], DenseRange (sequenceFiniteInC0 𝕜)

/-- Closure in ℓ∞, with the literal pointwise inclusion of c₀. -/
def InfinityClosure : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    closure (Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞)) =
      Set.range (fun x : SequenceC0 𝕜 => x.val)

def ConstantDistance : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Metric.infDist (1 : SequenceLInfinity 𝕜)
      (Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞)) = 1

def C0Proper : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (1 : SequenceLInfinity 𝕜) ∉ Set.range (fun x : SequenceC0 𝕜 => x.val) ∧
      Set.range (fun x : SequenceC0 𝕜 => x.val) ⊂ Set.univ

end Spec
end ExpandedFA.P1.SequenceDensity
