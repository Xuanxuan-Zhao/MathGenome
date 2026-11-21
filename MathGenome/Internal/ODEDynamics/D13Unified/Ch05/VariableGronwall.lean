import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.VariableGronwall
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.Gronwall
import Batteries.Tactic.OpenPrivate

open Set MeasureTheory
open scoped Interval

namespace D13Unified.Ch05.VariableGronwall

open private primitive_cont primitive_deriv from MathGenome.Internal.ODEDynamics.D13Unified.Ch05.Gronwall

theorem forward : Specs.D13Unified.Ch05.VariableGronwall.Forward := by
  intro s T u b a hsT hu hb ha hn h t ht
  have hsub : Icc s t ⊆ Icc s T := Icc_subset_Icc le_rfl ht.2
  have hub : ContinuousOn (fun r => b r * u r) (Icc s t) :=
    (hb.mul hu).mono hsub
  let v := fun x => ∫ r in s..x, b r * u r
  have hv : ContinuousOn v (Icc s t) := primitive_cont ht.1 hub
  have hba : ContinuousOn (fun r => b r * a r) (Icc s t) :=
    (hb.mul ha).mono hsub
  have hvi : ∀ r ∈ Icc s t,
      v r ≤ 0 + ∫ q in s..r, (b q * v q + b q * a q) := by
    intro r hr
    have hsr : Icc s r ⊆ Icc s t := Icc_subset_Icc le_rfl hr.2
    have hbi : IntervalIntegrable (fun q => b q * u q) volume s r :=
      ((hub.mono hsr).mono (by rw [uIcc_of_le hr.1])).intervalIntegrable
    have hci : IntervalIntegrable (fun q => b q * v q + b q * a q) volume s r :=
      ((((hb.mono hsub).mul hv).add hba).mono hsr |>.mono
        (by rw [uIcc_of_le hr.1])).intervalIntegrable
    simpa only [zero_add] using intervalIntegral.integral_mono_on hr.1 hbi hci
      (fun q hq => by
        have hq' := hsub (hsr hq)
        have hmul := mul_le_mul_of_nonneg_left (h q hq') (hn q hq').2.1
        dsimp [v] at *
        linarith)
  have hvbound := Gronwall.forward_bound ht.1 hv (hb.mono hsub) hba
    (fun r hr => (hn r (hsub hr)).2.1) hvi
  have heq : (∫ r in s..t, b r * a r * Real.exp (∫ q in r..t, b q)) =
      ∫ r in s..t, a r * b r * Real.exp (∫ q in r..t, b q) := by
    apply intervalIntegral.integral_congr
    intro r _
    ring
  simp only [zero_mul, zero_add] at hvbound
  rw [heq] at hvbound
  exact (h t ht).trans (add_le_add le_rfl hvbound)

/-- The exponential resolvent kernel has mass `exp (∫ b) - 1`. -/
lemma integral_exp_kernel {s t : ℝ} {b : ℝ → ℝ} (hst : s ≤ t)
    (hb : ContinuousOn b (Icc s t)) :
    (∫ r in s..t, b r * Real.exp (∫ q in r..t, b q)) =
      Real.exp (∫ r in s..t, b r) - 1 := by
  let B := fun x => ∫ r in s..x, b r
  have hB : ContinuousOn B (Icc s t) := primitive_cont hst hb
  have hF : ContinuousOn (fun x => -Real.exp (B t - B x)) (Icc s t) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.sub hB)).neg
  have hd : ∀ x ∈ Ioo s t, HasDerivAt (fun r => -Real.exp (B t - B r))
      (b x * Real.exp (B t - B x)) x := by
    intro x hx
    convert ((primitive_deriv hb hx).const_sub (B t)).exp.neg using 1
    ring
  have hi : IntervalIntegrable (fun x => b x * Real.exp (B t - B x)) volume s t :=
    ((hb.mul (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.sub hB))).mono (by rw [uIcc_of_le hst])).intervalIntegrable
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hF hd hi
  have heq : (∫ r in s..t, b r * Real.exp (∫ q in r..t, b q)) =
      ∫ r in s..t, b r * Real.exp (B t - B r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hst] at hr
    have hbst : IntervalIntegrable b volume s t :=
      (hb.mono (by rw [uIcc_of_le hst])).intervalIntegrable
    have hbsr : IntervalIntegrable b volume s r :=
      (hb.mono (by rw [uIcc_of_le hr.1]; exact Icc_subset_Icc le_rfl hr.2)).intervalIntegrable
    dsimp only
    rw [← intervalIntegral.integral_interval_sub_left hbst hbsr]
  rw [heq, hcalc]
  simp [B]
  ring

theorem monotone_envelope : Specs.D13Unified.Ch05.VariableGronwall.MonotoneEnvelope := by
  intro s T b a hsT hb ha hn hmono t ht
  have hsub : Icc s t ⊆ Icc s T := Icc_subset_Icc le_rfl ht.2
  have hB : ContinuousOn (fun r => ∫ q in s..r, b q) (Icc s t) :=
    primitive_cont ht.1 (hb.mono hsub)
  have hk : ContinuousOn (fun r => Real.exp (∫ q in r..t, b q)) (Icc s t) := by
    have heq : EqOn (fun r => Real.exp (∫ q in r..t, b q))
        (fun r => Real.exp ((∫ q in s..t, b q) - ∫ q in s..r, b q)) (Icc s t) := by
      intro r hr
      have hbst : IntervalIntegrable b volume s t :=
        ((hb.mono hsub).mono (by rw [uIcc_of_le ht.1])).intervalIntegrable
      have hbsr : IntervalIntegrable b volume s r :=
        (hb.mono (by rw [uIcc_of_le hr.1]; exact Icc_subset_Icc le_rfl (hr.2.trans ht.2))).intervalIntegrable
      dsimp only
      rw [← intervalIntegral.integral_interval_sub_left hbst hbsr]
    exact (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.sub hB)).congr heq
  have hi : IntervalIntegrable (fun r => a r * b r * Real.exp (∫ q in r..t, b q)) volume s t :=
    ((((ha.mul hb).mono hsub).mul hk).mono (by rw [uIcc_of_le ht.1])).intervalIntegrable
  have hj : IntervalIntegrable (fun r => a t * (b r * Real.exp (∫ q in r..t, b q))) volume s t :=
    ((continuousOn_const.mul ((hb.mono hsub).mul hk)).mono
      (by rw [uIcc_of_le ht.1])).intervalIntegrable
  have hle := intervalIntegral.integral_mono_on ht.1 hi hj (fun r hr => by
    have har : a r ≤ a t := hmono (hsub hr) ht hr.2
    have hb0 := (hn r (hsub hr)).1
    have hm := mul_le_mul_of_nonneg_right har
      (mul_nonneg hb0 (Real.exp_nonneg (∫ q in r..t, b q)))
    nlinarith)
  rw [intervalIntegral.integral_const_mul, integral_exp_kernel ht.1 (hb.mono hsub)] at hle
  nlinarith

theorem monotone_bound : Specs.D13Unified.Ch05.VariableGronwall.MonotoneBound := by
  intro s T u b a hsT hu hb ha hn h hmono t ht
  exact (forward s T u b a hsT hu hb ha hn h t ht).trans
    (monotone_envelope s T b a hsT hb ha (fun r hr => (hn r hr).2) hmono t ht)

end D13Unified.Ch05.VariableGronwall
