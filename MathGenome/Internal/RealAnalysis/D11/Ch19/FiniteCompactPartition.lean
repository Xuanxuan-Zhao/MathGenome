import MathGenome.Internal.RealAnalysis.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.FiniteCompactPartition
import Mathlib.Topology.PartitionOfUnity

/-!
# Finite compact-support partitions and decompositions

The locally compact Hausdorff version of the topological partition theorem
provides compact supports without any global normality or paracompactness
assumption. Multiplication by its real weights gives both scalar decompositions.
-/

namespace D11.Ch19

universe u v w

open scoped BigOperators

theorem finite_compact_partition (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (ι : Type v) [Fintype ι] (K : Set X) (U : ι → Set X)
    (hK : IsCompact K) (hU : ∀ i, IsOpen (U i)) (hKU : K ⊆ ⋃ i, U i) :
    ∃ φ : ι → Cc X ℝ,
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      (∀ i, closure {x | φ i x ≠ 0} ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, φ i x = 1) ∧
      (∀ x, ∑ i, φ i x ≤ 1) := by
  obtain ⟨ρ, hρU, hρc⟩ :=
    PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space hK U hU
      (locallyFinite_of_finite U) hKU
  refine ⟨fun i => ⟨ρ i, hρc i⟩, ?_, hρU, ?_, ?_⟩
  · exact fun i x => ⟨ρ.nonneg i x, ρ.le_one i x⟩
  · intro x hx
    change ∑ i, ρ i x = 1
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
  · intro x
    change ∑ i, ρ i x ≤ 1
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x

/-- Multiplying by a real compactly supported weight preserves the canonical Cc space. -/
private def weightedPiece {X : Type u} [TopologicalSpace X]
    {𝕜 : Type w} [RCLike 𝕜] (φ : Cc X ℝ) (f : Cc X 𝕜) : Cc X 𝕜 where
  toFun x := φ x • f x
  continuous_toFun := φ.continuous.smul f.continuous
  hasCompactSupport' := f.hasCompactSupport.smul_left (f := (φ : X → ℝ))

private theorem weightedPiece_support {X : Type u} [TopologicalSpace X]
    {𝕜 : Type w} [RCLike 𝕜] (φ : Cc X ℝ) (f : Cc X 𝕜) :
    tsupport (weightedPiece φ f) ⊆ tsupport φ :=
  tsupport_smul_subset_left _ _

private theorem sum_weightedPiece {X : Type u} [TopologicalSpace X]
    {𝕜 : Type w} [RCLike 𝕜] {ι : Type v} [Fintype ι]
    (φ : ι → Cc X ℝ) (f : Cc X 𝕜)
    (hφ : ∀ x ∈ tsupport f, ∑ i, φ i x = 1) :
    f = ∑ i, weightedPiece (φ i) f := by
  classical
  ext x
  simp only [CompactlySupportedContinuousMap.sum_apply]
  change f x = ∑ i, φ i x • f x
  rw [← Finset.sum_smul]
  by_cases hx : f x = 0
  · simp [hx]
  · rw [hφ x (subset_tsupport _ hx), one_smul]

theorem compact_support_decomposition (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (𝕜 : Type w) [RCLike 𝕜] (ι : Type v) [Fintype ι]
    (U : ι → Set X) (f : Cc X 𝕜) (hU : ∀ i, IsOpen (U i))
    (hfU : closure {x | f x ≠ 0} ⊆ ⋃ i, U i) :
    ∃ g : ι → Cc X 𝕜,
      f = ∑ i, g i ∧ (∀ i, closure {x | g i x ≠ 0} ⊆ U i) := by
  obtain ⟨φ, _, hφU, hφsum, _⟩ :=
    finite_compact_partition X ι (tsupport f) U f.hasCompactSupport hU hfU
  exact ⟨fun i => weightedPiece (φ i) f, sum_weightedPiece φ f hφsum,
    fun i => (weightedPiece_support (φ i) f).trans (hφU i)⟩

theorem nonnegative_compact_support_decomposition (X : Type u)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (ι : Type v) [Fintype ι] (U : ι → Set X) (f : Cc X ℝ)
    (hU : ∀ i, IsOpen (U i)) (hfU : closure {x | f x ≠ 0} ⊆ ⋃ i, U i)
    (hf : ∀ x, 0 ≤ f x) :
    ∃ g : ι → Cc X ℝ,
      f = ∑ i, g i ∧ (∀ i, closure {x | g i x ≠ 0} ⊆ U i) ∧
      (∀ i x, 0 ≤ g i x ∧ g i x ≤ f x) := by
  obtain ⟨φ, hφ, hφU, hφsum, _⟩ :=
    finite_compact_partition X ι (tsupport f) U f.hasCompactSupport hU hfU
  refine ⟨fun i => weightedPiece (φ i) f, sum_weightedPiece φ f hφsum,
    fun i => (weightedPiece_support (φ i) f).trans (hφU i), ?_⟩
  intro i x
  change 0 ≤ φ i x * f x ∧ φ i x * f x ≤ f x
  exact ⟨mul_nonneg (hφ i x).1 (hf x), mul_le_of_le_one_left (hf x) (hφ i x).2⟩

end D11.Ch19
