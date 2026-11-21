import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.NormSquareConjugate
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Conjugates
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ExpandedFA.Asplund.NormSquareConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_zero (p : E → ℝ) (hp : EquivalentNorm p) : p 0 = 0 :=
  (hp.1.2 0).2 rfl

lemma unitBall_values_nonempty (p : E → ℝ) (hp : EquivalentNorm p)
    (f : E →L[ℝ] ℝ) :
    ((fun x => |f x|) '' {x : E | p x ≤ 1}).Nonempty := by
  exact ⟨|f 0|, ⟨0, by simp [norm_zero p hp], rfl⟩⟩

lemma unitBall_values_bddAbove (p : E → ℝ) (hp : EquivalentNorm p)
    (f : E →L[ℝ] ℝ) :
    BddAbove ((fun x => |f x|) '' {x : E | p x ≤ 1}) := by
  obtain ⟨a, b, ha, _, hab⟩ := hp.2
  refine ⟨‖f‖ / a, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  change p x ≤ 1 at hx
  have hn : ‖x‖ ≤ 1 / a := (le_div_iff₀ ha).2 (by nlinarith [(hab x).1])
  calc
    |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ ‖f‖ * (1 / a) := mul_le_mul_of_nonneg_left hn (norm_nonneg f)
    _ = ‖f‖ / a := by ring

theorem dualNorm_isLUB : Spec.DualNormIsLUB := by
  intro E _ _ p hp f
  exact isLUB_csSup (unitBall_values_nonempty p hp f) (unitBall_values_bddAbove p hp f)

lemma dualNorm_nonneg (p : E → ℝ) (hp : EquivalentNorm p) (f : E →L[ℝ] ℝ) :
    0 ≤ dualNorm p f := by
  have h := (dualNorm_isLUB E p hp f).1
    (show |f 0| ∈ ((fun x => |f x|) '' {x : E | p x ≤ 1}) from
      ⟨0, by simp [norm_zero p hp], rfl⟩)
  simpa using h

lemma abs_apply_le_dualNorm (p : E → ℝ) (hp : EquivalentNorm p)
    (f : E →L[ℝ] ℝ) (x : E) : |f x| ≤ dualNorm p f * p x := by
  by_cases hx : x = 0
  · simp [hx, norm_zero p hp]
  have hpne : p x ≠ 0 := fun h => hx ((hp.1.2 x).1 h)
  have hpos : 0 < p x := lt_of_le_of_ne (hp.1.1.1 x) (Ne.symm hpne)
  have hunit : p ((p x)⁻¹ • x) ≤ 1 := by
    rw [hp.1.1.2.1, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpne]
  have hv := (dualNorm_isLUB E p hp f).1
    (show |f ((p x)⁻¹ • x)| ∈ ((fun y => |f y|) '' {y : E | p y ≤ 1}) from
      ⟨_, hunit, rfl⟩)
  rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hpos] at hv
  have hm := mul_le_mul_of_nonneg_right hv hpos.le
  calc
    |f x| = ((p x)⁻¹ * |f x|) * p x := by field_simp
    _ ≤ dualNorm p f * p x := hm

/-- Young's scalar inequality bounds every term in the conjugate. -/
lemma normSquare_term_le (p : E → ℝ) (hp : EquivalentNorm p)
    (f : E →L[ℝ] ℝ) (x : E) :
    f x - p x ^ 2 / 2 ≤ dualNorm p f ^ 2 / 2 := by
  have hf := (le_abs_self (f x)).trans (abs_apply_le_dualNorm p hp f x)
  nlinarith [sq_nonneg (p x - dualNorm p f)]

/-- Any upper bound on all conjugate terms bounds half the squared dual norm.
Test at `(f x) • x` for each vector in the closed unit ball, then use the
least-upper-bound property. This avoids any assertion of norm attainment. -/
lemma normSquare_le_of_forall_terms_le (p : E → ℝ) (hp : EquivalentNorm p)
    (f : E →L[ℝ] ℝ) (r : ℝ) (hr : ∀ x, f x - p x ^ 2 / 2 ≤ r) :
    dualNorm p f ^ 2 / 2 ≤ r := by
  have hr0 : 0 ≤ r := by simpa [norm_zero p hp] using hr 0
  have hd : dualNorm p f ≤ Real.sqrt (2 * r) := by
    apply (dualNorm_isLUB E p hp f).2
    rintro _ ⟨x, hx, rfl⟩
    change p x ≤ 1 at hx
    have hpx : p x ^ 2 ≤ 1 := by nlinarith [hp.1.1.1 x]
    have hprod : (|f x| * p x) ^ 2 ≤ f x ^ 2 := by
      calc
        (|f x| * p x) ^ 2 = f x ^ 2 * p x ^ 2 := by rw [mul_pow, sq_abs]
        _ ≤ f x ^ 2 * 1 := mul_le_mul_of_nonneg_left hpx (sq_nonneg _)
        _ = f x ^ 2 := mul_one _
    have ht := hr ((f x) • x)
    rw [map_smul, smul_eq_mul, hp.1.1.2.1, Real.norm_eq_abs] at ht
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    nlinarith
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * r by linarith)
  have hd0 := dualNorm_nonneg p hp f
  have hs0 := Real.sqrt_nonneg (2 * r)
  nlinarith [mul_nonneg (sub_nonneg.mpr hd) (add_nonneg hs0 hd0)]

/-- The half-squared norm and half-squared dual norm are Fenchel conjugates,
on the common continuous dual, even in the zero space. -/
theorem normSquare_conjugate : Spec.Conjugacy := by
  intro E _ _ p hp f
  let c : EReal := P1.C06Conjugates.convexConjugate E (halfNormSquare p) f
  have hterm (x : E) :
      (f x : EReal) - P1.C06Conjugates.extendedRealValue (halfNormSquare p x) =
        ((f x - p x ^ 2 / 2 : ℝ) : EReal) := by
    exact (EReal.coe_sub _ _).symm
  have hc_le : c ≤ ((dualNorm p f ^ 2 / 2 : ℝ) : EReal) := by
    apply iSup_le
    intro x
    rw [hterm]
    exact EReal.coe_le_coe (normSquare_term_le p hp f x)
  have hc_terms (x : E) : ((f x - p x ^ 2 / 2 : ℝ) : EReal) ≤ c := by
    rw [← hterm]
    exact (P1.C06Conjugates.convexConjugate_isLUB E (halfNormSquare p) f).1 ⟨x, rfl⟩
  have hc_zero : (0 : EReal) ≤ c := by
    simpa [norm_zero p hp] using hc_terms 0
  have hc_top : c ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hc_le
  have hc_bot : c ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hc_zero
  have hc_real := EReal.coe_toReal hc_top hc_bot
  have hterms (x : E) : f x - p x ^ 2 / 2 ≤ c.toReal := by
    apply EReal.coe_le_coe_iff.mp
    rw [hc_real]
    exact hc_terms x
  have hlow : ((dualNorm p f ^ 2 / 2 : ℝ) : EReal) ≤ c := by
    rw [← hc_real]
    exact EReal.coe_le_coe (normSquare_le_of_forall_terms_le p hp f c.toReal hterms)
  exact le_antisymm hc_le hlow

end ExpandedFA.Asplund.NormSquareConjugate
