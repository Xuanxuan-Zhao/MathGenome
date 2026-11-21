import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Independent statements for the separated-sequence clause of
`fa2:p1:c01:unit-vectors`, paper.tex 327–334. Natural coordinate `n`
means manuscript coordinate `n+1`, as in the shared sequence interface.
`RCLike` quantification includes both `ℝ` and `ℂ`. The finite formula
uses the real value of the extended exponent; the shared interface
identifies every real exponent `p ≥ 1` with `ENNReal.ofReal p`.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u

namespace ExpandedFA.P1.C01UnitVectors
open C01SequenceSpaces

abbrev lpCoordinate (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) (n : ℕ) :
    SequenceLp 𝕜 p := lp.single p n (1 : 𝕜)

/-- The same coordinate vector in the subspace of sequences vanishing at infinity. -/
def c0Coordinate (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : SequenceC0 𝕜 :=
  ⟨lpCoordinate 𝕜 ∞ n, by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with j hj
    simp [lpCoordinate, lp.single_apply, ne_of_gt hj]⟩

namespace Spec

def LpNorms : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ),
    ‖lpCoordinate 𝕜 p n‖ = 1

def FiniteDistances : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (m n : ℕ), m ≠ n →
      dist (lpCoordinate 𝕜 p m) (lpCoordinate 𝕜 p n) = (2 : ℝ) ^ (1 / p.toReal)

def InfinityDistances : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (m n : ℕ), m ≠ n →
    dist (lpCoordinate 𝕜 ∞ m) (lpCoordinate 𝕜 ∞ n) = 1

def LpBounded : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    Bornology.IsBounded (Set.range (lpCoordinate 𝕜 p))

def LpNoConvergentSubsequence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (s : ℕ → ℕ), StrictMono s → ∀ x : SequenceLp 𝕜 p,
      ¬ Tendsto (fun k => lpCoordinate 𝕜 p (s k)) atTop (𝓝 x)

def C0Norms : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ), ‖c0Coordinate 𝕜 n‖ = 1

def C0Distances : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (m n : ℕ), m ≠ n →
    dist (c0Coordinate 𝕜 m) (c0Coordinate 𝕜 n) = 1

def C0Bounded : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], Bornology.IsBounded (Set.range (c0Coordinate 𝕜))

def C0NoConvergentSubsequence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (s : ℕ → ℕ), StrictMono s →
    ∀ x : SequenceC0 𝕜, ¬ Tendsto (fun k => c0Coordinate 𝕜 (s k)) atTop (𝓝 x)

/-- A scalar-specific version, with the finite-exponent formula written for
every real `p ≥ 1`, rather than in the extended-exponent notation. -/
def ScalarExample (𝕜 : Type u) [RCLike 𝕜] : Prop :=
  (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    (∀ n, ‖lpCoordinate 𝕜 p n‖ = 1) ∧
    Bornology.IsBounded (Set.range (lpCoordinate 𝕜 p)) ∧
    ∀ (s : ℕ → ℕ), StrictMono s → ∀ x : SequenceLp 𝕜 p,
      ¬ Tendsto (fun k => lpCoordinate 𝕜 p (s k)) atTop (𝓝 x)) ∧
  (∀ (p : ℝ) (hp : 1 ≤ p) (m n : ℕ), m ≠ n →
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    dist (lpCoordinate 𝕜 (ENNReal.ofReal p) m)
      (lpCoordinate 𝕜 (ENNReal.ofReal p) n) = (2 : ℝ) ^ (1 / p)) ∧
  (∀ m n, m ≠ n → dist (lpCoordinate 𝕜 ∞ m) (lpCoordinate 𝕜 ∞ n) = 1) ∧
  (∀ n, ‖c0Coordinate 𝕜 n‖ = 1) ∧
  (∀ m n, m ≠ n → dist (c0Coordinate 𝕜 m) (c0Coordinate 𝕜 n) = 1) ∧
  Bornology.IsBounded (Set.range (c0Coordinate 𝕜)) ∧
  ∀ (s : ℕ → ℕ), StrictMono s → ∀ x : SequenceC0 𝕜,
    ¬ Tendsto (fun k => c0Coordinate 𝕜 (s k)) atTop (𝓝 x)

def RealExample : Prop := ScalarExample ℝ
def ComplexExample : Prop := ScalarExample ℂ

end Spec
end ExpandedFA.P1.C01UnitVectors

/-! The incomplete finite-support subspaces, with the inherited metrics.
Natural coordinate `n` is manuscript coordinate `j=n+1`. Thus the coefficient
below is exactly `2⁻ʲ`, and truncation at `N` retains `j=1,...,N`.
`IsComplete` on the image set refers to its induced uniformity, equivalently
to completeness of its subtype. No norm on `Finsupp` is silently substituted.
-/
noncomputable section
open Filter
open scoped Topology ENNReal
namespace ExpandedFA.P1.C01UnitVectors
open C01SequenceSpaces

/-- The manuscript's explicit finite truncations. -/
def geometricTruncation (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) : SequenceC00 𝕜 :=
  ∑ n ∈ Finset.range N, Finsupp.single n ((2 : 𝕜)⁻¹ ^ (n + 1))

/-- The identical truncation, now in the subspace `c₀` with its inherited norm. -/
def c0GeometricTruncation (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) : SequenceC0 𝕜 :=
  ⟨C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ (geometricTruncation 𝕜 N), by
    apply tendsto_const_nhds.congr'
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [(geometricTruncation 𝕜 N).hasFiniteSupport.eventually_cofinite_notMem]
      with n hn
    change (0 : 𝕜) = geometricTruncation 𝕜 N n
    simpa [Function.mem_support, eq_comm] using hn⟩

namespace Spec

/-- Every finite real exponent and infinity are included, without imposing a
finite-exponent hypothesis. Convergence is in the actual `lp` norm. -/
def IncompleteLp : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    CauchySeq (fun N => C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p (geometricTruncation 𝕜 N)) ∧
    (¬ ∃ x : SequenceC00 𝕜,
      Tendsto (fun N => C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p (geometricTruncation 𝕜 N))
        atTop (𝓝 (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p x))) ∧
    ¬ IsComplete (Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p))

/-- The explicit Cauchy sequence also witnesses the obstruction in `c₀`. -/
def C0Truncations : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    CauchySeq (c0GeometricTruncation 𝕜) ∧
    ¬ ∃ x : SequenceC0 𝕜,
      (Function.support (fun n => x.val n)).Finite ∧
      Tendsto (c0GeometricTruncation 𝕜) atTop (𝓝 x)

/-- The same finite-support subspace with the norm inherited from `c₀`. -/
def IncompleteC0 : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ IsComplete {x : SequenceC0 𝕜 | (Function.support (fun n => x.val n)).Finite}

end Spec
end ExpandedFA.P1.C01UnitVectors
