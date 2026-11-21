import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.ExtremeSetTests
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.KreinMilman

/-!
Extreme-set tests, `fa2:p2:extreme-set-tests`.

For a positive barycenter, isolate any entry and normalize the remaining
weights. If there are remaining entries, this expresses the extreme point as
a proper two-point convex combination. For closed extreme subsets, compactness
and the Krein–Milman lemma apply to the subset itself, even without convexity;
transitivity of extremeness transfers the resulting point to the original set.
-/
namespace ExpandedFA.BanachGeometry.ExtremeSetTests

universe u v

/-- The deletion criterion needs only a real vector space. -/
theorem extreme_iff_convex_delete :
    Specs.ExpandedFA.BanachGeometry.ExtremeSetTests.deletionType.{u} := by
  intro E _ _ K a hK ha
  exact hK.mem_extremePoints_iff_convex_sdiff.trans (and_iff_right ha)

/-- Every entry of a strictly positive finite barycenter at an extreme point
is that extreme point. -/
theorem finite_positive_barycenter :
    Specs.ExpandedFA.BanachGeometry.ExtremeSetTests.positiveBarycenterType.{u, v} := by
  intro E _ _ ι K a s w x hK ha hw hsum hx hbar i hi
  classical
  by_cases hempty : s.erase i = ∅
  · have hs : s = {i} := by
      simpa only [hempty, Finset.insert_empty] using (Finset.insert_erase hi).symm
    have hwi : w i = 1 := by simpa [hs] using hsum
    simpa [hs, hwi] using hbar
  · have hpos : 0 < ∑ j ∈ s.erase i, w j :=
      Finset.sum_pos (fun j hj => hw j (Finset.mem_of_mem_erase hj))
        (Finset.nonempty_iff_ne_empty.mpr hempty)
    have htotal : w i + ∑ j ∈ s.erase i, w j = 1 := by
      rw [add_comm, Finset.sum_erase_add _ _ hi, hsum]
    have hrest : (s.erase i).centerMass w x ∈ K :=
      hK.centerMass_mem
        (fun j hj => (hw j (Finset.mem_of_mem_erase hj)).le) hpos
        (fun j hj => hx j (Finset.mem_of_mem_erase hj))
    apply ha.2 (hx i hi) hrest
    refine ⟨w i, ∑ j ∈ s.erase i, w j, hw i hi, hpos, htotal, ?_⟩
    rw [Finset.centerMass, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul,
      add_comm, Finset.sum_erase_add _ _ hi, hbar]

/-- The closed extreme subset is not required to be convex. -/
theorem closed_extreme_subset_contains_extreme_point :
    Specs.ExpandedFA.BanachGeometry.ExtremeSetTests.closedExtremeSubsetType.{u} := by
  intro E _ _ _ _ _ _ _ K A hK _hconv hA hclosed hext
  obtain ⟨a, ha⟩ := (hK.of_isClosed_subset hclosed hext.subset).extremePoints_nonempty hA
  exact ⟨a, ha.1, hext.extremePoints_subset_extremePoints ha⟩

/-- Realification retains the original complex space's topology. -/
theorem complex_closed_extreme_subset_contains_extreme_point :
    Specs.ExpandedFA.BanachGeometry.ExtremeSetTests.complexClosedExtremeSubsetType.{u} := by
  intro E _ _ _ _ _ _ _ K A hK hconv hA hclosed hext
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact closed_extreme_subset_contains_extreme_point K A hK hconv hA hclosed hext

end ExpandedFA.BanachGeometry.ExtremeSetTests
