import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12Mazur
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecificLimits.Basic

/-! Mazur's lemma, with explicit zero-padded real coefficients on each tail. -/

namespace ExpandedFA.P1.C12Mazur

universe u v
open Filter
open scoped Topology BigOperators

/-- A finite convex combination of a tail can be written on an entire interval
of indices by giving every omitted index coefficient zero. -/
theorem convexHull_tail_interval {E : Type v} [AddCommGroup E] [Module ℝ E]
    (xₙ : ℕ → E) (n : ℕ) {y : E}
    (hy : y ∈ convexHull ℝ (Set.range (fun j : {j : ℕ // n ≤ j} => xₙ j))) :
    ∃ (m : ℕ) (a : ℕ → ℝ), n ≤ m ∧ (∀ j, 0 ≤ a j) ∧
      (∀ j, j ∉ Finset.Icc n m → a j = 0) ∧
      (∑ j ∈ Finset.Icc n m, a j = 1) ∧
      (∑ j ∈ Finset.Icc n m, a j • xₙ j) = y := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s, w, hw₀, hw₁, hy⟩ := hy
  let m := max n (s.sup (fun j => j.val))
  let a : ℕ → ℝ := fun j => ∑ i ∈ s, if i.val = j then w i else 0
  have hs : ∀ i ∈ s, i.val ∈ Finset.Icc n m := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨i.property,
      (Finset.le_sup (f := fun j => j.val) hi).trans (le_max_right _ _)⟩
  refine ⟨m, a, le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro j
    exact Finset.sum_nonneg fun i hi => by
      split_ifs
      · exact hw₀ i hi
      · exact le_rfl
  · intro j hj
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i.val ≠ j := by
      intro hij
      exact hj (hij ▸ hs i hi)
    simp [hij]
  · change (∑ j ∈ Finset.Icc n m, ∑ i ∈ s,
        if i.val = j then w i else 0) = 1
    rw [Finset.sum_comm]
    calc
      _ = ∑ i ∈ s, w i := Finset.sum_congr rfl fun i hi => by simp [hs i hi]
      _ = 1 := hw₁
  · change (∑ j ∈ Finset.Icc n m, (∑ i ∈ s,
        if i.val = j then w i else 0) • xₙ j) = y
    simp_rw [Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    rw [Finset.affineCombination_eq_linear_combination s _ _ hw₁] at hy
    calc
      _ = ∑ i ∈ s, w i • xₙ i := Finset.sum_congr rfl fun i hi => by simp [hs i hi]
      _ = y := hy

/-- Weak convergence gives norm-convergent convex combinations from successive
tails, without requiring the ambient normed space to be complete. -/
theorem mazur_tail_combinations :
    Spec.MazurTailCombinations.{u,v} := by
  classical
  intro 𝕜 E _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro xₙ x hx
  have hclosure (n : ℕ) :
      x ∈ closure (convexHull ℝ (Set.range (fun j : {j : ℕ // n ≤ j} => xₙ j))) := by
    rw [← C12ConvexClosure.weak_closure_eq_norm_closure 𝕜 E _ (convex_convexHull ℝ _)]
    let : TopologicalSpace E := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
    apply mem_closure_of_tendsto hx
    filter_upwards [eventually_ge_atTop n] with j hj
    exact subset_convexHull ℝ _ ⟨⟨j, hj⟩, rfl⟩
  have happrox (n : ℕ) : ∃ (m : ℕ) (a : ℕ → ℝ),
      n ≤ m ∧ (∀ j, 0 ≤ a j) ∧
      (∀ j, j ∉ Finset.Icc n m → a j = 0) ∧
      (∑ j ∈ Finset.Icc n m, a j = 1) ∧
      dist x (∑ j ∈ Finset.Icc n m, a j • xₙ j) < 1 / ((n : ℝ) + 1) := by
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp (hclosure n)
      (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨m, a, hm, ha, hzero, hsum, hrep⟩ := convexHull_tail_interval xₙ n hy
    exact ⟨m, a, hm, ha, hzero, hsum, hrep.symm ▸ hdist⟩
  choose m a hm ha hzero hsum hdist using happrox
  refine ⟨m, a, hm, ha, hzero, hsum, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [dist_comm] using (hdist n).le

end ExpandedFA.P1.C12Mazur
