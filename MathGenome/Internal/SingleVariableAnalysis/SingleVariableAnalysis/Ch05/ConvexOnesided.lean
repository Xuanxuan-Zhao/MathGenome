import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.ConvexLocalLipschitz
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.ConvexOnesided
import Mathlib.Analysis.Convex.Deriv

/-!
# Finite one-sided derivatives and supporting slopes of convex functions

K03.05.convex_onesided, paper.tex:941–957. Mathlib's convex secant theorem
constructs the right derivative as the infimum of right secants and the left
derivative as the supremum of left secants, with finiteness proved from exterior
secant bounds. We bridge its slope limits to the shared real-increment
predicates. The supporting-slope characterization uses these extremal formulas;
no ordinary derivative, prior continuity, or assumed certificate is needed.
-/

namespace SingleVariableAnalysis

open Set Filter
open scoped Topology

/-- A slope limit on the right gives the manuscript's positive-increment limit. -/
lemma hasRightRealIncrementDerivativeWithin_of_hasDerivWithinAt
    {f : ℝ → ℝ} {R x : ℝ} {I : Set ℝ}
    (hd : HasDerivWithinAt f R (Ioi x) x) (ha : RightIntervalAvailable I x) :
    HasRightRealIncrementDerivativeWithin f R I x := by
  apply (rightDerivative_epsilon_iff f R I x).mpr
  refine ⟨ha, fun ε hε => ?_⟩
  have ht := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hd
  obtain ⟨δ, hδ, hb⟩ := (Metric.tendsto_nhdsWithin_nhds.mp ht) ε hε
  refine ⟨δ, hδ, fun h _hh hp hlt => ?_⟩
  have hd' : dist (x + h) x < δ := by
    simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hp] using hlt
  have hh' : x + h ∈ Ioi x := by change x < x + h; linarith
  simpa only [dist_eq_norm, slope_def_module, add_sub_cancel_left,
    RealIncrementQuotient] using hb hh' hd'

/-- The corresponding bridge on the negative-increment side. -/
lemma hasLeftRealIncrementDerivativeWithin_of_hasDerivWithinAt
    {f : ℝ → ℝ} {L x : ℝ} {I : Set ℝ}
    (hd : HasDerivWithinAt f L (Iio x) x) (ha : LeftIntervalAvailable I x) :
    HasLeftRealIncrementDerivativeWithin f L I x := by
  apply (leftDerivative_epsilon_iff f L I x).mpr
  refine ⟨ha, fun ε hε => ?_⟩
  have ht := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hd
  obtain ⟨δ, hδ, hb⟩ := (Metric.tendsto_nhdsWithin_nhds.mp ht) ε hε
  refine ⟨δ, hδ, fun h _hh hlo hn => ?_⟩
  have hd' : dist (x + h) x < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_neg hn]
    linarith
  have hh' : x + h ∈ Iio x := by change x + h < x; linarith
  simpa only [dist_eq_norm, slope_def_module, add_sub_cancel_left,
    RealIncrementQuotient] using hb hh' hd'

/-- Both derivative witnesses are actual finite real numbers, with left ≤ right. -/
theorem convexFunctionOn_finite_one_sided
    (I : Set ℝ) (hOpen : IsOpen I) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : ConvexFunctionOn I f) (x : ℝ) (hx : x ∈ I) :
    ∃ L R : ℝ, HasLeftRealIncrementDerivativeWithin f L I x ∧
      HasRightRealIncrementDerivativeWithin f R I x ∧ L ≤ R := by
  have hc := (convexFunctionOn_iff_convexOn I hI f).mp hf
  have hxi : x ∈ interior I := by rwa [hOpen.interior_eq]
  obtain ⟨hr, hl⟩ := interior_sideIntervals I x hxi
  exact ⟨derivWithin f (Iio x) x, derivWithin f (Ioi x) x,
    hasLeftRealIncrementDerivativeWithin_of_hasDerivWithinAt
      (hc.hasDerivWithinAt_leftDeriv_of_mem_interior hxi) hl,
    hasRightRealIncrementDerivativeWithin_of_hasDerivWithinAt
      (hc.hasDerivWithinAt_rightDeriv_of_mem_interior hxi) hr,
    hc.leftDeriv_le_rightDeriv_of_mem_interior hxi⟩

/-- Supporting slopes are exactly the interval between the canonical side
values. The proof includes necessity as well as sufficiency. -/
private theorem convex_supportingSlope_iff_derivWithin
    {I : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hc : ConvexOn ℝ I f) (hx : x ∈ interior I) (p : ℝ) :
    (∀ y ∈ I, f x + p * (y - x) ≤ f y) ↔
      derivWithin f (Iio x) x ≤ p ∧ p ≤ derivWithin f (Ioi x) x := by
  constructor
  · intro hp
    constructor
    · rw [hc.leftDeriv_eq_sSup_slope_of_mem_interior hx]
      apply csSup_le
      · obtain ⟨l, hlx, hli⟩ := Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hx)
        exact ⟨slope f x l, mem_image_of_mem _ ⟨hli, hlx⟩⟩
      · rintro _ ⟨y, ⟨hy, hyx⟩, rfl⟩
        rw [slope_def_field, div_le_iff_of_neg (sub_neg.mpr hyx)]
        linarith [hp y hy]
    · rw [hc.rightDeriv_eq_sInf_slope_of_mem_interior hx]
      apply le_csInf
      · obtain ⟨r, hxr, hri⟩ := Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hx)
        exact ⟨slope f x r, mem_image_of_mem _ ⟨hri, hxr⟩⟩
      · rintro _ ⟨y, ⟨hy, hxy⟩, rfl⟩
        rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)]
        linarith [hp y hy]
  · rintro ⟨hl, hr⟩ y hy
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · have hs := hr.trans (hc.rightDeriv_le_slope_of_mem_interior hx hy hxy)
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hs
      linarith
    · simp
    · have hs := (hc.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans hl
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at hs
      nlinarith

/-- The characterization holds for any witnesses of the shared one-sided
predicates; uniqueness identifies them with the canonical side derivatives. -/
theorem convexFunctionOn_supportingSlope_iff
    (I : Set ℝ) (hOpen : IsOpen I) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : ConvexFunctionOn I f) (x : ℝ) (hx : x ∈ I)
    (L R : ℝ) (hL : HasLeftRealIncrementDerivativeWithin f L I x)
    (hR : HasRightRealIncrementDerivativeWithin f R I x) (p : ℝ) :
    (∀ y ∈ I, f x + p * (y - x) ≤ f y) ↔ L ≤ p ∧ p ≤ R := by
  have hc := (convexFunctionOn_iff_convexOn I hI f).mp hf
  have hxi : x ∈ interior I := by rwa [hOpen.interior_eq]
  obtain ⟨hr, hl⟩ := interior_sideIntervals I x hxi
  have heL := leftDerivative_unique f L (derivWithin f (Iio x) x) I x hL
    (hasLeftRealIncrementDerivativeWithin_of_hasDerivWithinAt
      (hc.hasDerivWithinAt_leftDeriv_of_mem_interior hxi) hl)
  have heR := rightDerivative_unique f R (derivWithin f (Ioi x) x) I x hR
    (hasRightRealIncrementDerivativeWithin_of_hasDerivWithinAt
      (hc.hasDerivWithinAt_rightDeriv_of_mem_interior hxi) hr)
  rw [heL, heR]
  exact convex_supportingSlope_iff_derivWithin hc hxi p

end SingleVariableAnalysis
