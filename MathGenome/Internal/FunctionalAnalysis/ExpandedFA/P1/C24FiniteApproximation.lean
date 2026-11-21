import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24FiniteApproximation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Algebra.BigOperators.Field

open Set Metric
open scoped BigOperators

namespace ExpandedFA.P1.C24FiniteApproximation

universe u

/-- Finite convex approximation of any nonempty norm-compact set, without
completeness, convexity, or positive dimension assumptions. -/
theorem finiteConvexApproximation :
    Spec.FiniteConvexApproximation.{u} := by
  classical
  intro E _ _ Q hQne hQ ε hε
  obtain ⟨s, hsQ, hsfin, hscover⟩ := hQ.finite_cover_balls hε
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hQne
    obtain ⟨q, hq, _⟩ := Set.mem_iUnion₂.mp (hscover hx)
    exact ⟨q, hq⟩
  let : Fintype s := hsfin.fintype
  let w : s → Q → ℝ := fun q x => max 0 (ε - ‖(x : E) - (q : E)‖)
  have hw : ∀ q x, 0 ≤ w q x := fun _ _ => le_max_left _ _
  have hwcont : ∀ q, Continuous (w q) := by
    intro q
    exact continuous_const.max (continuous_const.sub
      ((continuous_subtype_val.sub continuous_const).norm))
  let W : Q → ℝ := fun x => ∑ q : s, w q x
  have hW : ∀ x, 0 < W x := by
    intro x
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hscover x.property)
    have hpos : 0 < w ⟨q, hq⟩ x := by
      exact lt_max_of_lt_right (sub_pos.mpr (by simpa [mem_ball, dist_eq_norm] using hxq))
    exact Finset.sum_pos' (fun q _ => hw q x) ⟨⟨q, hq⟩, Finset.mem_univ _, hpos⟩
  have hWcont : Continuous W := continuous_finsetSum _ (fun q _ => hwcont q)
  let a : s → Q → ℝ := fun q x => w q x / W x
  have ha : ∀ q x, 0 ≤ a q x := fun q x => div_nonneg (hw q x) (hW x).le
  have hasum : ∀ x, ∑ q : s, a q x = 1 := by
    intro x
    dsimp [a]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hW x))
  have hacont : ∀ q, Continuous (a q) := by
    intro q
    exact (hwcont q).div hWcont (fun x => ne_of_gt (hW x))
  let f : Q → E := fun x => ∑ q : s, a q x • (q : E)
  have hfcont : Continuous f := by
    exact continuous_finsetSum _ (fun q _ => (hacont q).smul continuous_const)
  have hfmem : ∀ x, f x ∈ convexHull ℝ s := by
    intro x
    exact mem_convexHull_of_exists_fintype (fun q => a q x) (fun q => (q : E))
      (fun q => ha q x) (hasum x) (fun q => q.property) rfl
  have hferror : ∀ x, ‖f x - (x : E)‖ < ε := by
    intro x
    have hball : f x ∈ ball (x : E) ε := by
      have h := (convex_ball (x : E) ε).finsum_mem
        (fun q => ha q x) (by simpa only [finsum_eq_sum_of_fintype] using hasum x)
        (z := fun q : s => (q : E)) ?_
      · simpa only [finsum_eq_sum_of_fintype] using h
      · intro q hq
        have hweight : w q x ≠ 0 := by
          intro hz
          exact hq (by simp [a, hz])
        have hdist : ‖(x : E) - (q : E)‖ < ε := by
          by_contra hn
          exact hweight (max_eq_left (sub_nonpos.mpr (le_of_not_gt hn)))
        simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hdist
    simpa [mem_ball, dist_eq_norm] using hball
  refine ⟨s, hsfin, hsne, hsQ, (fun x => ⟨f x, hfmem x⟩), ?_, ?_⟩
  · exact hfcont.subtype_mk _
  · exact hferror

/-- The same construction for complex normed spaces, using their underlying
real vector space and the unchanged norm topology. -/
theorem finiteConvexApproximationComplex :
    Spec.FiniteConvexApproximationComplex.{u} := by
  intro E _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  exact finiteConvexApproximation E

end ExpandedFA.P1.C24FiniteApproximation
