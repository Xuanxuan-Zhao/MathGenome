import MathGenome.Internal.ExtremalOptimization.Specs.P205.Convex.FiniteHullSupport
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

namespace P205

/-- A nonempty finite convex hull contains every point satisfying all of
its linear upper bounds (Lemma 9.2 of the source). -/
theorem finiteHullSupport : Specs.P205.FiniteHullSupport := by
  intro E _ _ _ F hF x hbound
  let K : Set E := convexHull ℝ (F : Set E)
  have hKconv : Convex ℝ K := convex_convexHull ℝ (F : Set E)
  have hKcompact : IsCompact K := F.finite_toSet.isCompact_convexHull ℝ
  have hKne : K.Nonempty := by
    obtain ⟨z, hz⟩ := hF
    exact ⟨z, subset_convexHull ℝ (F : Set E) hz⟩
  obtain ⟨y, hy, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hKne hKcompact.isComplete hKconv x
  have hprojection : ∀ z ∈ K, inner ℝ (x - y) (z - y) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hKconv hy).mp hmin
  have hmax : F.sup' hF (fun z => inner ℝ (x - y) z) ≤ inner ℝ (x - y) y := by
    apply Finset.sup'_le
    intro z hz
    have hzK : z ∈ K := subset_convexHull ℝ (F : Set E) hz
    have hzle := hprojection z hzK
    rw [inner_sub_right] at hzle
    exact sub_nonpos.mp hzle
  have hself : inner ℝ (x - y) (x - y) ≤ 0 := by
    rw [inner_sub_right]
    exact sub_nonpos.mpr ((hbound (x - y)).trans hmax)
  by_contra hx
  have hne : x ≠ y := by
    intro hxy
    apply hx
    simpa [hxy] using hy
  exact (not_lt_of_ge hself) (real_inner_self_pos.mpr (sub_ne_zero.mpr hne))

end P205
