import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero

/-!
Independent statements of paper.tex:5494–5502.
The functions use the canonical native Cc interface. Real functions valued in
[0,1] are expressed by pointwise bounds, and support always includes its closure.
Finite index types include the empty family. No countability of X is assumed.
-/

namespace Specs.D11.Ch19.FiniteCompactPartition

universe u v w

/-- A finite open cover of a compact set admits compactly supported real weights,
subordinate to the cover, summing to one on the compact set and at most one globally. -/
def finite_compact_partition : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (ι : Type v) [Fintype ι] (K : Set X) (U : ι → Set X),
    IsCompact K → (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
    ∃ φ : ι → CompactlySupportedContinuousMap X ℝ,
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      (∀ i, closure {x | φ i x ≠ 0} ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, φ i x = 1) ∧
      (∀ x, ∑ i, φ i x ≤ 1)

/-- Every real or complex Cc function whose support lies in the union decomposes
as a finite sum of Cc functions with support in the respective open sets. -/
def compact_support_decomposition : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (𝕜 : Type w) [RCLike 𝕜] (ι : Type v) [Fintype ι]
    (U : ι → Set X) (f : CompactlySupportedContinuousMap X 𝕜),
    (∀ i, IsOpen (U i)) → closure {x | f x ≠ 0} ⊆ ⋃ i, U i →
    ∃ g : ι → CompactlySupportedContinuousMap X 𝕜,
      f = ∑ i, g i ∧ (∀ i, closure {x | g i x ≠ 0} ⊆ U i)

/-- For a nonnegative real function the pieces can be chosen nonnegative.
The additional upper bound makes explicit that no piece exceeds the original. -/
def nonnegative_compact_support_decomposition : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (ι : Type v) [Fintype ι] (U : ι → Set X)
    (f : CompactlySupportedContinuousMap X ℝ),
    (∀ i, IsOpen (U i)) → closure {x | f x ≠ 0} ⊆ ⋃ i, U i →
    (∀ x, 0 ≤ f x) →
    ∃ g : ι → CompactlySupportedContinuousMap X ℝ,
      f = ∑ i, g i ∧ (∀ i, closure {x | g i x ≠ 0} ⊆ U i) ∧
      (∀ i x, 0 ≤ g i x ∧ g i x ≤ f x)

end Specs.D11.Ch19.FiniteCompactPartition
