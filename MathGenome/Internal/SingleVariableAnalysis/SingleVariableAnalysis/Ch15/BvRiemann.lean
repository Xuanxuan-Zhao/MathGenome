import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.BvRiemann
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.OneSided
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Regulated
import Mathlib.Analysis.Complex.Basic

/-! Proper Riemann integrability of real and complex BV functions.
The real result combines finite one-sided limits with the regulated theorem.
For complex values, projection decreases every partition sum; the finite real
component limits combine to complex limits, without an order on ℂ. -/
namespace SingleVariableAnalysis.BV
open Set Filter
open scoped Topology BigOperators

/-- A pointwise bound on increments gives a bound on total variation. -/
theorem totalVariation_le_of_norm_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℝ → E) (g : ℝ → F) (a b : ℝ)
    (h : ∀ x y, ‖g x - g y‖ ≤ ‖f x - f y‖) :
    totalVariation g a b ≤ totalVariation f a b := by
  apply iSup_le
  intro P
  apply le_trans _ (le_iSup (fun Q : Riemann.Partition a b => partitionSum Q f) P)
  apply Finset.sum_le_sum
  intro i _
  exact ENNReal.ofReal_le_ofReal (h _ _)

theorem component_variations :
    Specs.SingleVariableAnalysis.Ch15.BvRiemann.componentVariations := by
  intro f a b
  constructor
  · apply totalVariation_le_of_norm_sub_le f (fun x => (f x).re) a b
    intro x y
    simpa only [Real.norm_eq_abs, ← Complex.sub_re] using Complex.abs_re_le_norm (f x - f y)
  · apply totalVariation_le_of_norm_sub_le f (fun x => (f x).im) a b
    intro x y
    simpa only [Real.norm_eq_abs, ← Complex.sub_im] using Complex.abs_im_le_norm (f x - f y)

theorem real_bv_regulated :
    Specs.SingleVariableAnalysis.Ch15.BvRiemann.realBvRegulated := by
  intro f a b hab hf
  exact ⟨finite_left_limits f hab hf, finite_right_limits f hab hf⟩

theorem real_bv_riemann :
    Specs.SingleVariableAnalysis.Ch15.BvRiemann.realBvRiemann := by
  intro f a b hab hf
  have hr := real_bv_regulated f hab hf
  obtain ⟨hb, hi⟩ := real_regulated_riemann hab f hr
  exact ⟨hb, hr, hi⟩

/-- The two finite real limits reconstruct a finite complex limit. -/
theorem tendsto_complex_of_components {α : Type*} {l : Filter α}
    {f : α → ℂ} {u v : ℝ}
    (hre : Tendsto (fun x => (f x).re) l (𝓝 u))
    (him : Tendsto (fun x => (f x).im) l (𝓝 v)) :
    Tendsto f l (𝓝 ((u : ℂ) + (v : ℂ) * Complex.I)) := by
  simpa only [Complex.re_add_im] using hre.ofReal.add (him.ofReal.mul_const Complex.I)

/-- Combining limits preserves the nontrivial approach required by RegulatedOn. -/
theorem regulated_complex_of_components {f : ℝ → ℂ} {a b : ℝ}
    (hre : RegulatedOn (fun x => (f x).re) a b)
    (him : RegulatedOn (fun x => (f x).im) a b) : RegulatedOn f a b := by
  constructor
  · intro c hc
    obtain ⟨u, hu⟩ := hre.1 c hc
    obtain ⟨v, hv⟩ := him.1 c hc
    have hu' := (leftRelativeLimit_filter_iff _ _ _ _).mp hu
    have hv' := (leftRelativeLimit_filter_iff _ _ _ _).mp hv
    exact ⟨(u : ℂ) + (v : ℂ) * Complex.I,
      (leftRelativeLimit_filter_iff _ _ _ _).mpr
        ⟨hu'.1, tendsto_complex_of_components hu'.2 hv'.2⟩⟩
  · intro c hc
    obtain ⟨u, hu⟩ := hre.2 c hc
    obtain ⟨v, hv⟩ := him.2 c hc
    have hu' := (rightRelativeLimit_filter_iff _ _ _ _).mp hu
    have hv' := (rightRelativeLimit_filter_iff _ _ _ _).mp hv
    exact ⟨(u : ℂ) + (v : ℂ) * Complex.I,
      (rightRelativeLimit_filter_iff _ _ _ _).mpr
        ⟨hu'.1, tendsto_complex_of_components hu'.2 hv'.2⟩⟩

theorem complex_bv_regulated :
    Specs.SingleVariableAnalysis.Ch15.BvRiemann.complexBvRegulated := by
  intro f a b hab hf
  have hcomp := component_variations f a b
  exact regulated_complex_of_components
    (real_bv_regulated _ hab (lt_of_le_of_lt hcomp.1 hf))
    (real_bv_regulated _ hab (lt_of_le_of_lt hcomp.2 hf))

theorem complex_bv_riemann :
    Specs.SingleVariableAnalysis.Ch15.BvRiemann.complexBvRiemann := by
  intro f a b hab hf
  have hr := complex_bv_regulated f hab hf
  obtain ⟨hb, hi⟩ := complex_regulated_riemann hab f hr
  exact ⟨hb, hr, hi⟩

/-- A complex function is continuous at every point where both real components
are continuous. Consequently its relative discontinuities form a countable set. -/
theorem complex_countable_discontinuities :
    Specs.SingleVariableAnalysis.Ch15.BvRiemann.complexCountableDiscontinuities := by
  intro f a b hab hf
  have hcomp := component_variations f a b
  have hre := countable_discontinuities (fun x => (f x).re) hab
    (lt_of_le_of_lt hcomp.1 hf)
  have him := countable_discontinuities (fun x => (f x).im) hab
    (lt_of_le_of_lt hcomp.2 hf)
  apply (hre.union him).mono
  intro x hx
  by_contra hn
  have hreC : ContinuousWithinAt (fun y => (f y).re) (Icc a b) x := by
    by_contra hn'
    exact hn (Or.inl ⟨hx.1, hn'⟩)
  have himC : ContinuousWithinAt (fun y => (f y).im) (Icc a b) x := by
    by_contra hn'
    exact hn (Or.inr ⟨hx.1, hn'⟩)
  have hT := tendsto_complex_of_components hreC himC
  apply hx.2
  change Tendsto f (𝓝[Icc a b] x) (𝓝 (f x))
  simpa only [Complex.re_add_im] using hT

end SingleVariableAnalysis.BV
