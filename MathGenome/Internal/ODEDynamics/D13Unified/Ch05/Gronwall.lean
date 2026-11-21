import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MeasureTheory
open scoped Interval

namespace D13Unified.Ch05.Gronwall

noncomputable def E : ℝ → ℝ → ℝ := Specs.D13Unified.Ch05.Gronwall.EValue

theorem E_formula : Specs.D13Unified.Ch05.Gronwall.EFormula := by
  constructor
  · intro v; simp [Specs.D13Unified.Ch05.Gronwall.EValue]
  · intro L v hL; simp [Specs.D13Unified.Ch05.Gronwall.EValue, ne_of_gt hL]

private lemma primitive_cont {a z : ℝ} {f : ℝ → ℝ} (haz : a ≤ z)
    (hf : ContinuousOn f (Icc a z)) :
    ContinuousOn (fun x => ∫ r in a..x, f r) (Icc a z) := by
  have hi : IntervalIntegrable f volume a z :=
    (hf.mono (by rw [uIcc_of_le haz])).intervalIntegrable
  simpa [uIcc_of_le haz] using intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc

private lemma primitive_deriv {a z x : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a z)) (hx : x ∈ Ioo a z) :
    HasDerivAt (fun y => ∫ r in a..y, f r) (f x) x := by
  have hc : ContinuousAt f x := hf.continuousAt (Icc_mem_nhds hx.1 hx.2)
  apply intervalIntegral.integral_hasDerivAt_right _ ((hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx) hc
  exact (hf.mono (by rw [uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable

/-- Integrating factor argument on a fixed compact interval. -/
lemma integrating_factor_bound {a z A : ℝ} {u b c : ℝ → ℝ} (haz : a ≤ z)
    (hu : ContinuousOn u (Icc a z)) (hb : ContinuousOn b (Icc a z))
    (hc : ContinuousOn c (Icc a z)) (hb0 : ∀ r ∈ Icc a z, 0 ≤ b r)
    (h : ∀ r ∈ Icc a z, u r ≤ A + ∫ q in a..r, (b q * u q + c q)) :
    u z ≤ Real.exp (∫ r in a..z, b r) *
      (A + ∫ r in a..z, c r * Real.exp (-(∫ q in a..r, b q))) := by
  let B := fun x => ∫ r in a..x, b r
  let V := fun x => A + ∫ r in a..x, (b r * u r + c r)
  let C := fun x => ∫ r in a..x, c r * Real.exp (-B r)
  have hB : ContinuousOn B (Icc a z) := primitive_cont haz hb
  have hV : ContinuousOn V (Icc a z) :=
    continuousOn_const.add (primitive_cont haz ((hb.mul hu).add hc))
  have hCint : ContinuousOn (fun r => c r * Real.exp (-B r)) (Icc a z) :=
    hc.mul (Real.continuous_exp.comp_continuousOn hB.neg)
  have hC : ContinuousOn C (Icc a z) := primitive_cont haz hCint
  let F := fun x => V x * Real.exp (-B x) - C x
  have hF : ContinuousOn F (Icc a z) := (hV.mul (Real.continuous_exp.comp_continuousOn hB.neg)).sub hC
  have hd : ∀ x ∈ Ioo a z, HasDerivAt F
      ((b x * u x + c x) * Real.exp (-B x) +
        V x * (Real.exp (-B x) * (-b x)) - c x * Real.exp (-B x)) x := by
    intro x hx
    exact (((primitive_deriv ((hb.mul hu).add hc) hx).const_add A).mul
      (primitive_deriv hb hx).neg.exp).sub (primitive_deriv hCint hx)
  have hmono : AntitoneOn F (Icc a z) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a z) hF
    · intro x hx
      exact (hd x (by simpa only [interior_Icc] using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo a z := by simpa only [interior_Icc] using hx
      rw [(hd x hx').deriv]
      have hv : u x ≤ V x := h x ⟨hx'.1.le, hx'.2.le⟩
      have hmul := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (hb0 x ⟨hx'.1.le, hx'.2.le⟩) (Real.exp_nonneg (-B x)))
        (sub_nonpos.mpr hv)
      nlinarith
  have hh := hmono ⟨le_rfl, haz⟩ ⟨haz, le_rfl⟩ haz
  have hFa : F a = A := by simp [F, V, B, C]
  rw [hFa] at hh
  have hpos := Real.exp_pos (B z)
  have hid : Real.exp (-B z) * Real.exp (B z) = 1 := by
    rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right hh hpos.le
  change (V z * Real.exp (-B z) - C z) * Real.exp (B z) ≤ A * Real.exp (B z) at hm
  rw [sub_mul, mul_assoc, hid, mul_one] at hm
  have hv : V z ≤ Real.exp (B z) * (A + C z) := by nlinarith
  exact (h z ⟨haz, le_rfl⟩).trans hv

lemma forward_bound {a z A : ℝ} {u b c : ℝ → ℝ} (haz : a ≤ z)
    (hu : ContinuousOn u (Icc a z)) (hb : ContinuousOn b (Icc a z))
    (hc : ContinuousOn c (Icc a z)) (hb0 : ∀ r ∈ Icc a z, 0 ≤ b r)
    (h : ∀ r ∈ Icc a z, u r ≤ A + ∫ q in a..r, (b q * u q + c q)) :
    u z ≤ A * Real.exp (∫ r in a..z, b r) +
      ∫ r in a..z, c r * Real.exp (∫ q in r..z, b q) := by
  have heq : Real.exp (∫ r in a..z, b r) *
      (A + ∫ r in a..z, c r * Real.exp (-(∫ q in a..r, b q))) =
      A * Real.exp (∫ r in a..z, b r) +
        ∫ r in a..z, c r * Real.exp (∫ q in r..z, b q) := by
    rw [mul_add, mul_comm _ A, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    rw [uIcc_of_le haz] at hr
    have hi : IntervalIntegrable b volume a z :=
      (hb.mono (by rw [uIcc_of_le haz])).intervalIntegrable
    have hir : IntervalIntegrable b volume a r :=
      (hb.mono (by rw [uIcc_of_le hr.1]; exact Icc_subset_Icc le_rfl hr.2)).intervalIntegrable
    rw [← intervalIntegral.integral_interval_sub_left hi hir, Real.exp_sub]
    rw [Real.exp_neg]
    ring
  rw [← heq]
  exact integrating_factor_bound haz hu hb hc hb0 h

theorem forward : Specs.D13Unified.Ch05.Gronwall.Forward := by
  intro s T A u b c hsT _ hu hb hc hn h t ht
  have hsub : Icc s t ⊆ Icc s T := Icc_subset_Icc le_rfl ht.2
  exact forward_bound ht.1 (hu.mono hsub) (hb.mono hsub) (hc.mono hsub)
    (fun r hr => (hn r (hsub hr)).2.1) (fun r hr => h r (hsub hr))

theorem backward : Specs.D13Unified.Ch05.Gronwall.Backward := by
  intro T s A u b c hTs hA hu hb hc hn h t ht
  have hm : MapsTo (fun x : ℝ => -x) (Icc (-s) (-T)) (Icc T s) := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  have hneg : ContinuousOn (fun x : ℝ => -x) (Icc (-s) (-T)) :=
    continuous_neg.continuousOn
  have hf := forward (-s) (-T) A (fun x => u (-x)) (fun x => b (-x))
    (fun x => c (-x)) (by linarith) hA (hu.comp hneg hm) (hb.comp hneg hm)
    (hc.comp hneg hm) (fun x hx => hn (-x) (hm hx))
    (by
      intro x hx
      rw [intervalIntegral.integral_comp_neg (fun r => b r * u r + c r)]
      simpa only [neg_neg] using h (-x) (hm hx))
    (-t) (by constructor <;> linarith [ht.1, ht.2])
  simp only [intervalIntegral.integral_comp_neg, neg_neg] at hf
  rw [intervalIntegral.integral_comp_neg (fun r => c r * Real.exp (∫ q in t..r, b q))] at hf
  simpa only [neg_neg] using hf

/-- Elementary exponential kernel evaluation, including the zero coefficient. -/
lemma integral_exp_kernel (L a z : ℝ) :
    (∫ r in a..z, Real.exp (L * (z - r))) = E L (z - a) := by
  by_cases hL : L = 0
  · subst L
    simp [E, Specs.D13Unified.Ch05.Gronwall.EValue]
  · have hd : ∀ x : ℝ, HasDerivAt (fun r : ℝ => -(Real.exp (L * (z-r))) / L)
        (Real.exp (L * (z-x))) x := by
      intro x
      convert (((((hasDerivAt_id x).const_sub z).const_mul L).exp).neg.div_const L) using 1
      dsimp
      field_simp
      rfl
    have hi : IntervalIntegrable (fun r => Real.exp (L * (z-r))) volume a z :=
      (by fun_prop : Continuous (fun r : ℝ => Real.exp (L * (z-r)))).intervalIntegrable a z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
    simp [E, Specs.D13Unified.Ch05.Gronwall.EValue, hL]
    ring

theorem constant_forward : Specs.D13Unified.Ch05.Gronwall.ConstantForward := by
  intro s T A L δ u hsT hA hL hδ hu hn h t ht
  have hf := forward s T A u (fun _ => L) (fun _ => δ) hsT hA hu
    continuousOn_const continuousOn_const (fun r hr => ⟨hn r hr, hL, hδ⟩) h t ht
  have heq : (∫ r in s..t, δ * Real.exp (∫ _q in r..t, L)) = δ * E L (t-s) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    simpa only [mul_comm] using integral_exp_kernel L s t
  rw [heq] at hf
  change u t ≤ A * Real.exp (L * (t-s)) + δ * E L (t-s)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t-s) L] using hf

theorem constant_backward : Specs.D13Unified.Ch05.Gronwall.ConstantBackward := by
  intro T s A L δ u hTs hA hL hδ hu hn h t ht
  have hm : MapsTo (fun x : ℝ => -x) (Icc (-s) (-T)) (Icc T s) := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  have hf := constant_forward (-s) (-T) A L δ (fun x => u (-x))
    (by linarith) hA hL hδ (hu.comp continuous_neg.continuousOn hm)
    (fun x hx => hn (-x) (hm hx))
    (by
      intro x hx
      rw [intervalIntegral.integral_comp_neg (fun r => L * u r + δ)]
      simpa only [neg_neg] using h (-x) (hm hx))
    (-t) (by constructor <;> linarith [ht.1, ht.2])
  have habs : |t-s| = -t - -s := by rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]; ring
  simpa only [neg_neg, habs] using hf

end D13Unified.Ch05.Gronwall
