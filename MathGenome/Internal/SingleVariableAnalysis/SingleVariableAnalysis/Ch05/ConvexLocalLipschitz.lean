import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Convexity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.ConvexLocalLipschitz

/-!
# Local Lipschitz continuity of finite convex functions

The first part of K03.05.convex_onesided. Repeated secant comparisons give an
explicit constant on each interior segment. Openness supplies the exterior
points; Lipschitz continuity on neighborhoods then gives continuity everywhere
on the interval. No differentiability or prior continuity is used.
-/

namespace SingleVariableAnalysis

open Set

/-- Secants inside a segment lie between the two fixed exterior secants. -/
theorem convexFunctionOn_secant_bounds
    (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ) (hf : ConvexFunctionOn I f)
    (u a b v : ℝ) (hu : u ∈ I) (ha : a ∈ I) (hb : b ∈ I) (hv : v ∈ I)
    (hua : u < a) (_hab : a ≤ b) (hbv : b < v)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
    (f a - f u) / (a - u) ≤ (f y - f x) / (y - x) ∧
      (f y - f x) / (y - x) ≤ (f v - f b) / (v - b) := by
  have hc : ConvexOn ℝ I f := (convexFunctionOn_iff_convexOn I hI f).mp hf
  have hxI : x ∈ I := hI.out ha hb hx
  have hyI : y ∈ I := hI.out ha hb hy
  have hux : u < x := hua.trans_le hx.1
  have hyv : y < v := hy.2.trans_lt hbv
  constructor
  · exact (hc.secant_mono hu ha hxI (ne_of_gt hua) (ne_of_gt hux) hx.1).trans
      (hc.slope_mono_adjacent hu hyI hux hxy)
  · have hright : (f v - f y) / (v - y) ≤ (f v - f b) / (v - b) := by
      rcases eq_or_lt_of_le hy.2 with rfl | hyb
      · exact le_rfl
      · exact hc.secant_mono_aux3 hyI hv hyb hbv
    exact (hc.slope_mono_adjacent hxI hv hxy hyv).trans hright

/-- An explicitly quantified real estimate, before packaging it as Lipschitz. -/
private theorem convex_segment_estimate
    (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ) (hf : ConvexFunctionOn I f)
    (u a b v : ℝ) (hu : u ∈ I) (ha : a ∈ I) (hb : b ∈ I) (hv : v ∈ I)
    (hua : u < a) (hab : a ≤ b) (hbv : b < v)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
    |f y - f x| ≤
      max (|(f a - f u) / (a - u)|) (|(f v - f b) / (v - b)|) * |y - x| := by
  obtain ⟨hl, hr⟩ := convexFunctionOn_secant_bounds
    I hI f hf u a b v hu ha hb hv hua hab hbv x y hx hy hxy
  have habs : |(f y - f x) / (y - x)| ≤
      max (|(f a - f u) / (a - u)|) (|(f v - f b) / (v - b)|) := by
    apply abs_le.mpr
    constructor
    · have hl' := neg_abs_le ((f a - f u) / (a - u))
      have hm := le_max_left (|(f a - f u) / (a - u)|)
        (|(f v - f b) / (v - b)|)
      linarith
    · exact hr.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [abs_div, abs_of_pos (sub_pos.mpr hxy)] at habs
  simpa only [abs_of_pos (sub_pos.mpr hxy)] using
    (div_le_iff₀ (sub_pos.mpr hxy)).mp habs

/-- The constant is exactly the maximum of the absolute exterior slopes. -/
theorem convexFunctionOn_lipschitzOnWith_exterior
    (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ) (hf : ConvexFunctionOn I f)
    (u a b v : ℝ) (hu : u ∈ I) (ha : a ∈ I) (hb : b ∈ I) (hv : v ∈ I)
    (hua : u < a) (hab : a ≤ b) (hbv : b < v) :
    LipschitzOnWith
      (Real.toNNReal (max (|(f a - f u) / (a - u)|) (|(f v - f b) / (v - b)|)))
      f (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.coe_toNNReal _ (le_trans (abs_nonneg _) (le_max_left _ _))]
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · simpa only [Real.dist_eq, abs_sub_comm] using
      convex_segment_estimate I hI f hf u a b v hu ha hb hv hua hab hbv x y hx hy hxy
  · simp
  · simpa only [Real.dist_eq] using
      convex_segment_estimate I hI f hf u a b v hu ha hb hv hua hab hbv y x hy hx hyx

/-- Openness provides exterior points for every compact interior segment. -/
theorem convexFunctionOn_lipschitzOnWith_segment
    (I : Set ℝ) (hOpen : IsOpen I) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : ConvexFunctionOn I f)
    (a b : ℝ) (hab : a ≤ b) (ha : a ∈ I) (hb : b ∈ I) :
    ∃ u ∈ I, ∃ v ∈ I, u < a ∧ b < v ∧
      LipschitzOnWith
        (Real.toNNReal (max (|(f a - f u) / (a - u)|) (|(f v - f b) / (v - b)|)))
        f (Icc a b) := by
  obtain ⟨l, r, hla, hsuba⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hOpen.mem_nhds ha)
  obtain ⟨s, t, hbt, hsubb⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hOpen.mem_nhds hb)
  let u := (l + a) / 2
  let v := (b + t) / 2
  have hua : u < a := by dsimp [u]; linarith [hla.1]
  have hbv : b < v := by dsimp [v]; linarith [hbt.2]
  have hu : u ∈ I := hsuba ⟨by dsimp [u]; linarith [hla.1], hua.trans hla.2⟩
  have hv : v ∈ I := hsubb ⟨hbt.1.trans hbv, by dsimp [v]; linarith [hbt.2]⟩
  exact ⟨u, hu, v, hv, hua, hbv,
    convexFunctionOn_lipschitzOnWith_exterior I hI f hf u a b v hu ha hb hv hua hab hbv⟩

/-- Neighborhoods covered by compact interior segments give continuity. -/
theorem convexFunctionOn_continuousOn
    (I : Set ℝ) (hOpen : IsOpen I) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : ConvexFunctionOn I f) : ContinuousOn f I := by
  intro x hx
  obtain ⟨l, r, hxr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hOpen.mem_nhds hx)
  let a := (l + x) / 2
  let b := (x + r) / 2
  have hax : a < x := by dsimp [a]; linarith [hxr.1]
  have hxb : x < b := by dsimp [b]; linarith [hxr.2]
  have ha : a ∈ I := hsub ⟨by dsimp [a]; linarith [hxr.1], hax.trans hxr.2⟩
  have hb : b ∈ I := hsub ⟨hxr.1.trans hxb, by dsimp [b]; linarith [hxr.2]⟩
  obtain ⟨u, _hu, v, _hv, _hua, _hbv, hLip⟩ :=
    convexFunctionOn_lipschitzOnWith_segment I hOpen hI f hf a b (hax.trans hxb).le ha hb
  exact ((hLip.continuousOn x ⟨hax.le, hxb.le⟩).continuousAt
    (Icc_mem_nhds hax hxb)).continuousWithinAt

end SingleVariableAnalysis
