import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06ConjugateExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06FenchelMoreau

/-! Norm and convex-indicator conjugates, paper.tex:1346–1357.
The indicator biconjugate theorem uses the accepted Fenchel–Moreau theorem
after verifying its three hypotheses directly. No completeness is assumed. -/

namespace ExpandedFA.P1.C06ConjugateExamples

open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates ExpandedFA.P1.C06FenchelMoreau

def normFunction : Spec.NormFunctionType :=
  fun _ _ _ x => (‖x‖ : WithTop ℝ)

noncomputable def convexIndicator : Spec.ConvexIndicatorType :=
  Spec.ConvexIndicatorValue

noncomputable def supportFunction : Spec.SupportFunctionType :=
  fun _ _ _ C f => ⨆ x : C, (f x : EReal)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A functional outside the dual unit ball has a strictly positive excess
over the norm in some direction; no norm attainment is required. -/
theorem exists_norm_lt_apply (f : E →L[ℝ] ℝ) (hf : 1 < ‖f‖) :
    ∃ x : E, ‖x‖ < f x := by
  by_contra hn
  push Not at hn
  have hbound : ‖f‖ ≤ 1 := f.opNorm_le_bound zero_le_one fun x => by
    rw [Real.norm_eq_abs, one_mul, abs_le]
    refine ⟨?_, hn x⟩
    have h := hn (-x)
    simp only [map_neg, norm_neg] at h
    linarith
  exact (not_le_of_gt hf) hbound

theorem norm_conjugate : Spec.NormConjugate := by
  intro E _ _ f
  change convexConjugate E (normFunction E) f = _
  split_ifs with hf
  · apply le_antisymm
    · rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl,
        convexConjugate_le_real_iff]
      intro x s hs
      have hs' : ‖x‖ = s := WithTop.coe_inj.mp hs
      have hfx : f x ≤ ‖x‖ :=
        (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using f.le_of_opNorm_le hf x)
      linarith
    · have h := le_iSup (fun x : E =>
        (f x : EReal) - extendedRealValue (normFunction E x)) (0 : E)
      simp only [map_zero, normFunction, norm_zero] at h
      change (0 : EReal) - 0 ≤ convexConjugate E (normFunction E) f at h
      simpa only [sub_zero] using h
  · obtain ⟨x, hx⟩ := exists_norm_lt_apply f (lt_of_not_ge hf)
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro r
    let t : ℝ := (max r 0 + 1) / (f x - ‖x‖)
    have hd : 0 < f x - ‖x‖ := sub_pos.mpr hx
    have ht : 0 < t := div_pos (by positivity) hd
    have hlarge : r < f (t • x) - ‖t • x‖ := by
      rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * (f x - ‖x‖) = max r 0 + 1 := div_mul_cancel₀ _ hd.ne'
      nlinarith [le_max_left r 0]
    have hle := le_iSup (fun y : E =>
      (f y : EReal) - extendedRealValue (normFunction E y)) (t • x)
    exact (EReal.coe_lt_coe_iff.mpr hlarge).trans_le hle

theorem indicator_conjugate : Spec.IndicatorConjugate := by
  intro E _ _ C f
  classical
  change convexConjugate E (convexIndicator E C) f = supportFunction E C f
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : x ∈ C
    · have hi : convexIndicator E C x = (0 : WithTop ℝ) := by
        simp [convexIndicator, Spec.ConvexIndicatorValue, hx]
      rw [hi]
      change (f x : EReal) - 0 ≤ supportFunction E C f
      rw [sub_zero]
      exact le_iSup (fun y : C => (f y : EReal)) ⟨x, hx⟩
    · have hi : convexIndicator E C x = ⊤ := by
        simp [convexIndicator, Spec.ConvexIndicatorValue, hx]
      rw [hi]
      change (f x : EReal) - ⊤ ≤ supportFunction E C f
      rw [EReal.sub_top]
      exact bot_le
  · apply iSup_le
    intro x
    have h := le_iSup (fun y : E =>
      (f y : EReal) - extendedRealValue (convexIndicator E C y)) (x : E)
    have hi : convexIndicator E C x = (0 : WithTop ℝ) := by
      simp [convexIndicator, Spec.ConvexIndicatorValue, x.property]
    rw [hi] at h
    change (f (x : E) : EReal) - 0 ≤ convexConjugate E (convexIndicator E C) f at h
    simpa only [sub_zero] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem indicator_proper (C : Set E) (hC : C.Nonempty) :
    Proper E (convexIndicator E C) := by
  classical
  obtain ⟨x, hx⟩ := hC
  apply (proper_iff_finite_value E _).mpr
  exact ⟨x, 0, by simp [convexIndicator, Spec.ConvexIndicatorValue, hx]⟩

theorem indicator_convex (C : Set E) (hC : Convex ℝ C) :
    ExtendedConvex E (convexIndicator E C) := by
  classical
  intro x y r s a b hx hy ha hb hab
  have hxC : x ∈ C := by
    by_contra hn
    simp [convexIndicator, Spec.ConvexIndicatorValue, hn] at hx
  have hyC : y ∈ C := by
    by_contra hn
    simp [convexIndicator, Spec.ConvexIndicatorValue, hn] at hy
  have hr : r = 0 := by
    simpa [convexIndicator, Spec.ConvexIndicatorValue, hxC] using hx.symm
  have hs : s = 0 := by
    simpa [convexIndicator, Spec.ConvexIndicatorValue, hyC] using hy.symm
  simp [convexIndicator, Spec.ConvexIndicatorValue,
    hC hxC hyC ha hb hab, hr, hs]

omit [NormedSpace ℝ E] in
theorem indicator_lowerSemicontinuous (C : Set E) (hC : IsClosed C) :
    LowerSemicontinuous E (convexIndicator E C) := by
  classical
  intro r
  by_cases hr : 0 ≤ r
  · have heq : {x : E | convexIndicator E C x ≤ (r : WithTop ℝ)} = C := by
      ext x
      by_cases hx : x ∈ C <;>
        simp [convexIndicator, Spec.ConvexIndicatorValue, hx, hr]
    rw [heq]
    exact hC
  · have heq : {x : E | convexIndicator E C x ≤ (r : WithTop ℝ)} = ∅ := by
      ext x
      by_cases hx : x ∈ C <;>
        simp [convexIndicator, Spec.ConvexIndicatorValue, hx, hr]
    rw [heq]
    exact isClosed_empty

theorem indicator_biconjugate : Spec.IndicatorBiconjugate := by
  intro E _ _ C hn hc hv x
  exact fenchel_moreau E (convexIndicator E C) (indicator_proper C hn)
    (indicator_convex C hv) (indicator_lowerSemicontinuous C hc) x

end ExpandedFA.P1.C06ConjugateExamples
