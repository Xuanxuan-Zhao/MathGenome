import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Monotone
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Nonnegative

/-!
# Nonnegative series and regrouping

For K03.11.nonnegative (paper.tex:995–1001), the ordinary convergence
criterion is proved from monotone convergence of the existing real partial
sums. The extended sum uses canonical ENNReal summation. Its finite-subset
and initial-segment formulas and its limit identify it with the source's
extended sum, including +∞ in the divergent case. Reindexing and disjoint
partition identities use the ENNReal summation API, which requires no
finiteness of the sum. In particular an infinite block is never silently
replaced by a finite real sum.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology ENNReal

universe u v

/-- Extended nonnegative family sum. For nonnegative terms `ofReal` loses no data. -/
noncomputable def nonnegativeExtendedSum {ι : Type u} (a : ι → ℝ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (a i)

theorem nonnegative_partialSums_monotone (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    Monotone (realPartialSum a) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hmn 1)) (fun i _ _ => ha i)

theorem nonnegative_series_converges_iff (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    RealSeriesConverges a ↔ BddAbove (Set.range (realPartialSum a)) := by
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨C, _, hC⟩ := real_convergent_bounded (realPartialSum a) S hS
    exact ⟨C, fun _ ⟨n, hn⟩ => hn ▸ (le_abs_self _).trans (hC n)⟩
  · intro hb
    exact ⟨_, monotone_converges_to_supremum _ (nonnegative_partialSums_monotone a ha) hb⟩

theorem nonnegative_series_hasSum_supremum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hb : BddAbove (Set.range (realPartialSum a))) :
    RealSeriesHasSum a
      (realSupremum (Set.range (realPartialSum a)) (Set.range_nonempty _) hb) :=
  monotone_converges_to_supremum _ (nonnegative_partialSums_monotone a ha) hb

theorem nonnegative_series_diverges_to_posInfinity (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hd : ¬ RealSeriesConverges a) :
    DivergesToPosInfinity (realPartialSum a) :=
  monotone_diverges_to_posInfinity _ (nonnegative_partialSums_monotone a ha)
    (fun hb => hd ((nonnegative_series_converges_iff a ha).mpr hb))

theorem nonnegative_extendedSum_finite_subsets {ι : Type u} (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    nonnegativeExtendedSum a = ⨆ F : Finset ι, ENNReal.ofReal (∑ i ∈ F, a i) := by
  unfold nonnegativeExtendedSum
  rw [ENNReal.tsum_eq_iSup_sum]
  simp only [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i)]

theorem nonnegative_extendedSum_partialSums (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    nonnegativeExtendedSum a = ⨆ N, ENNReal.ofReal (realPartialSum a N) := by
  unfold nonnegativeExtendedSum realPartialSum
  rw [ENNReal.tsum_eq_iSup_sum' (fun N => Finset.range (N + 1))]
  · simp only [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i)]
  · intro F
    obtain ⟨N, hN⟩ := F.exists_nat_subset_range
    exact ⟨N, hN.trans (Finset.range_mono (Nat.le_succ N))⟩

theorem nonnegative_extendedSum_tendsto (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    Filter.Tendsto (fun N => ENNReal.ofReal (realPartialSum a N)) Filter.atTop
      (𝓝 (nonnegativeExtendedSum a)) := by
  rw [nonnegative_extendedSum_partialSums a ha]
  apply tendsto_atTop_iSup
  intro m n hmn
  exact ENNReal.ofReal_le_ofReal (nonnegative_partialSums_monotone a ha hmn)

theorem nonnegative_extendedSum_of_hasSum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (S : ℝ) (hS : RealSeriesHasSum a S) :
    nonnegativeExtendedSum a = ENNReal.ofReal S := by
  exact tendsto_nhds_unique (nonnegative_extendedSum_tendsto a ha)
    (ENNReal.tendsto_ofReal ((realSequenceConverges_iff _ _).mp hS))

theorem nonnegative_extendedSum_eq_top_iff (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    nonnegativeExtendedSum a = ∞ ↔ ¬ RealSeriesConverges a := by
  constructor
  · intro ht ⟨S, hS⟩
    exact ENNReal.ofReal_ne_top (ht ▸ (nonnegative_extendedSum_of_hasSum a ha S hS).symm)
  · intro hd
    apply tendsto_nhds_unique (nonnegative_extendedSum_tendsto a ha)
    exact ENNReal.tendsto_ofReal_atTop.comp
      ((divergesToPosInfinity_iff _).mp (nonnegative_series_diverges_to_posInfinity a ha hd))

theorem nonnegative_extendedSum_reindex {ι : Type u} {κ : Type v}
    (a : κ → ℝ) (_ha : ∀ i, 0 ≤ a i) (e : ι ≃ κ) :
    nonnegativeExtendedSum (fun i => a (e i)) = nonnegativeExtendedSum a :=
  e.tsum_eq (fun i => ENNReal.ofReal (a i))

theorem nonnegative_extendedSum_fiberwise {ι : Type u} (a : ℕ → ℝ)
    (_ha : ∀ n, 0 ≤ a n) (q : ℕ → ι) :
    (∑' i, nonnegativeExtendedSum (fun n : {n // q n = i} => a n)) =
      nonnegativeExtendedSum a := by
  exact ENNReal.tsum_fiberwise (fun n => ENNReal.ofReal (a n)) q

theorem nonnegative_extendedSum_partition {ι : Type u} (a : ℕ → ℝ)
    (_ha : ∀ n, 0 ≤ a n) (B : ι → Set ℕ)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (hu : (⋃ i, B i) = Set.univ) :
    (∑' i, nonnegativeExtendedSum (fun n : B i => a n)) =
      nonnegativeExtendedSum a := by
  have h := ENNReal.tsum_biUnion (f := fun n => ENNReal.ofReal (a n))
    (t := B) (fun i _ j _ hij => hd hij)
  rw [hu] at h
  have he := tsum_univ (fun n : ℕ => ENNReal.ofReal (a n))
  exact h.symm.trans he

end SingleVariableAnalysis
