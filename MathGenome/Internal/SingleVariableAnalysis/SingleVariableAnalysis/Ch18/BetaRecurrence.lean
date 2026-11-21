import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BetaRecurrence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.BetaDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SingleVariableAnalysis.SpecialIntegrals
open Set Filter
open scoped Topology BigOperators
open SingleVariableAnalysis.Riemann SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch18.BetaRecurrence

private def cut (n : ℕ) : ℝ := 1 / ((n : ℝ) + 3)

private theorem cut_pos (n : ℕ) : 0 < cut n := by
  unfold cut
  positivity

private theorem cut_lt_half (n : ℕ) : cut n < 1/2 := by
  unfold cut
  apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

private theorem cut_tendsto : Tendsto cut atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 2)
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (𝓝 (0 : ℝ))
  convert h using 1
  funext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
  congr 1
  ring

private theorem trim_integrable (p q : ℝ) (n : ℕ) :
    RealIntegrable (betaIntegrand p q) (cut n) (1-cut n) := by
  apply beta_local_integrability p q
  · exact WithBot.coe_lt_coe.mpr (cut_pos n)
  · linarith [cut_lt_half n]
  · exact WithTop.coe_lt_coe.mpr (by linarith [cut_pos n])

private def betaTrim (p q : ℝ) (n : ℕ) : ℝ :=
  realIntegral (betaIntegrand p q) (trim_integrable p q n)

/-- A sequence of regular truncations inherits its limit from the two
independently convergent endpoint integrals. This does not use a linked
truncation criterion to establish improper convergence. -/
private theorem betaTrim_tendsto (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (betaTrim p q) atTop (𝓝 (beta p q)) := by
  let c : RegularPoint (0 : WithBot ℝ) (1 : WithTop ℝ) :=
    ⟨1/2, by norm_num, by norm_num⟩
  obtain ⟨l, r, ⟨hl, hL⟩, ⟨hr, hR⟩, he⟩ :=
    beta_independent_endpoints p q hp hq c
  let u (n : ℕ) : LeftIndex (0 : WithBot ℝ) (1/2) :=
    ⟨cut n, WithBot.coe_lt_coe.mpr (cut_pos n), cut_lt_half n⟩
  let v (n : ℕ) : RightIndex (1/2) (1 : WithTop ℝ) :=
    ⟨1-cut n, by linarith [cut_lt_half n],
      WithTop.coe_lt_coe.mpr (by linarith [cut_pos n])⟩
  have hleft : Tendsto (fun n => (LeftTruncation .real _ 0 (1/2) hl (u n) : ℝ))
      atTop (𝓝 l) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := hL ε hε
    have hsmall := (tendsto_order.mp cut_tendsto).2 s.val
      (WithBot.coe_lt_coe.mp s.property.1)
    filter_upwards [hsmall] with n hn
    exact hs (u n) hn
  have hright : Tendsto (fun n => (RightTruncation .real _ (1/2) 1 hr (v n) : ℝ))
      atTop (𝓝 r) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := hR ε hε
    have hsmall := (tendsto_order.mp cut_tendsto).2 (1-s.val)
      (sub_pos.mpr (WithTop.coe_lt_coe.mp s.property.2))
    filter_upwards [hsmall] with n hn
    apply hs (v n)
    change s.val < 1-cut n
    linarith
  change beta p q = l + r at he
  rw [he]
  apply (hleft.add hright).congr
  intro n
  symm
  exact (real_split (betaIntegrand p q) (cut_lt_half n).le
    (by linarith [cut_lt_half n])
    (trim_integrable p q n).bounded).2
      (trim_integrable p q n) (hl.2 (u n)) (hr.2 (v n))

/-- Equality on the regular closed interval suffices for equality of proper
integrals. Endpoint values at 0 and 1 never occur. -/
private theorem darboux_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b)
    (he : ∀ x ∈ Icc a b, f x = g x) :
    realIntegral f hf = realIntegral g hg := by
  apply le_antisymm
  · exact realIntegral_mono f g hf hg (fun x hx => (he x hx).le)
  · exact realIntegral_mono g f hg hf (fun x hx => (he x hx).symm.le)

private theorem integrand_add (p q t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    betaIntegrand (p+1) q t + betaIntegrand p (q+1) t = betaIntegrand p q t := by
  change realPower t (p+1-1) * realPower (1-t) (q-1) +
    realPower t (p-1) * realPower (1-t) (q+1-1) =
      realPower t (p-1) * realPower (1-t) (q-1)
  have h₁ : realPower t (p+1-1) = realPower t (p-1) * t := by
    rw [show p+1-1 = (p-1)+1 by ring, realPower_add t ht,
      realPower_one_exponent t ht]
  have h₂ : realPower (1-t) (q+1-1) = realPower (1-t) (q-1) * (1-t) := by
    rw [show q+1-1 = (q-1)+1 by ring, realPower_add _ (sub_pos.mpr ht1),
      realPower_one_exponent _ (sub_pos.mpr ht1)]
  rw [h₁, h₂]
  ring

private theorem betaTrim_add (p q : ℝ) (n : ℕ) :
    betaTrim (p+1) q n + betaTrim p (q+1) n = betaTrim p q n := by
  obtain ⟨hs, hv⟩ := real_add_value (trim_integrable (p+1) q n)
    (trim_integrable p (q+1) n)
  exact hv.symm.trans (darboux_congr hs (trim_integrable p q n) (fun x hx =>
    integrand_add p q x ((cut_pos n).trans_le hx.1)
      (hx.2.trans_lt (by linarith [cut_pos n]))))

theorem beta_add_parameters (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    beta (p+1) q + beta p (q+1) = beta p q := by
  exact tendsto_nhds_unique ((betaTrim_tendsto (p+1) q (by linarith) hq).add
    (betaTrim_tendsto p (q+1) hp (by linarith)))
      ((betaTrim_tendsto p q hp hq).congr (fun n => (betaTrim_add p q n).symm))

private def betaBoundary (p q t : ℝ) : ℝ :=
  realPower t p * realPower (1-t) q

private theorem betaBoundary_continuous (p q : ℝ) :
    ContinuousOn (betaBoundary p q) (Ioo 0 1) := by
  apply ContinuousOn.mul
  · exact (realPower_continuous_base p).mono (fun _ hx => hx.1)
  · exact (realPower_continuous_base q).comp (continuousOn_const.sub continuousOn_id)
      (fun _ hx => sub_pos.mpr hx.2)

private theorem betaBoundary_derivative (p q x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (betaBoundary p q)
      (p * betaIntegrand p (q+1) x + (-q) * betaIntegrand (p+1) q x) x := by
  have h₁ := realPower_hasDerivAt p x hx.1
  have h₂ := (realPower_hasDerivAt q (1-x) (sub_pos.mpr hx.2)).comp x
    ((hasDerivAt_id x).const_sub 1)
  change HasDerivAt (fun t => realPower t p) (p * realPower x (p-1)) x at h₁
  change HasDerivAt (fun t => realPower (1-t) q)
    (q * realPower (1-x) (q-1) * (-1)) x at h₂
  convert h₁.mul h₂ using 1
  · rfl
  · change p * (realPower x (p-1) * realPower (1-x) (q+1-1)) +
      (-q) * (realPower x (p+1-1) * realPower (1-x) (q-1)) = _
    simp only [add_sub_cancel_right]
    ring

private theorem betaTrim_parts (p q : ℝ) (n : ℕ) :
    p * betaTrim p (q+1) n - q * betaTrim (p+1) q n =
      betaBoundary p q (1-cut n) - betaBoundary p q (cut n) := by
  obtain ⟨h₁, hv₁⟩ := real_mul_value (trim_integrable p (q+1) n) p
  obtain ⟨h₂, hv₂⟩ := real_mul_value (trim_integrable (p+1) q n) (-q)
  obtain ⟨hg, hvg⟩ := real_add_value h₁ h₂
  have hsub : Icc (cut n) (1-cut n) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨(cut_pos n).trans_le hx.1, hx.2.trans_lt (by linarith [cut_pos n])⟩
  have hftc := real_ftc_second (betaBoundary p q) _ (cut n) (1-cut n)
    (by linarith [cut_lt_half n]) ((betaBoundary_continuous p q).mono hsub)
    (fun x hx => betaBoundary_derivative p q x (hsub ⟨hx.1.le, hx.2.le⟩)) hg
  change realIntegral _ hg = _ at hftc
  rw [hvg, hv₁, hv₂] at hftc
  change p * realIntegral _ (trim_integrable p (q+1) n) -
    q * realIntegral _ (trim_integrable (p+1) q n) = _
  linarith

private theorem betaBoundary_limits (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun n => betaBoundary p q (cut n)) atTop (𝓝 0) ∧
    Tendsto (fun n => betaBoundary p q (1-cut n)) atTop (𝓝 0) := by
  let F : ℝ → ℝ := fun t => t ^ p * (1-t) ^ q
  have hF : Continuous F :=
    (Real.continuous_rpow_const hp.le).mul
      ((Real.continuous_rpow_const hq.le).comp (continuous_const.sub continuous_id))
  have hzero : F 0 = 0 := by simp [F, Real.zero_rpow hp.ne']
  have hone : F 1 = 0 := by simp [F, Real.zero_rpow hq.ne']
  have he (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : betaBoundary p q t = F t := by
    simp only [betaBoundary, F, realPower_eq_rpow t ht,
      realPower_eq_rpow (1-t) (sub_pos.mpr ht1)]
  constructor
  · have h := hF.continuousAt.tendsto.comp cut_tendsto
    rw [hzero] at h
    exact h.congr (fun n => (he _ (cut_pos n) (by linarith [cut_lt_half n])).symm)
  · have hc : Tendsto (fun n => 1-cut n) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub cut_tendsto
    have h := hF.continuousAt.tendsto.comp hc
    rw [hone] at h
    exact h.congr (fun n => (he _ (by linarith [cut_lt_half n])
      (by linarith [cut_pos n])).symm)

/-- The second linear relation comes from a proper Newton–Leibniz formula;
both boundary terms vanish for the original positive parameter hypotheses. -/
theorem beta_parts_relation (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    p * beta p (q+1) = q * beta (p+1) q := by
  have hlim := ((betaTrim_tendsto p (q+1) hp (by linarith)).const_mul p).sub
    ((betaTrim_tendsto (p+1) q (by linarith) hq).const_mul q)
  obtain ⟨h₀, h₁⟩ := betaBoundary_limits p q hp hq
  have hb := h₁.sub h₀
  have hz : p * beta p (q+1) - q * beta (p+1) q = 0 :=
    tendsto_nhds_unique hlim (by
      simpa only [sub_zero] using hb.congr (fun n => (betaTrim_parts p q n).symm))
  exact sub_eq_zero.mp hz

theorem beta_add_one_left : betaAddOneLeft := by
  intro p q hp hq
  change beta (p+1) q = p * beta p q / (p+q)
  apply (eq_div_iff (ne_of_gt (add_pos hp hq))).mpr
  have ha := beta_add_parameters p q hp hq
  have hb := beta_parts_relation p q hp hq
  nlinarith

theorem beta_add_one_right : betaAddOneRight := by
  intro p q hp hq
  change beta p (q+1) = q * beta p q / (p+q)
  apply (eq_div_iff (ne_of_gt (add_pos hp hq))).mpr
  have ha := beta_add_parameters p q hp hq
  have hb := beta_parts_relation p q hp hq
  nlinarith

private theorem betaTrim_one (p : ℝ) (hp : 0 < p) (n : ℕ) :
    betaTrim p 1 n = (realPower (1-cut n) p - realPower (cut n) p) / p := by
  have hsub : Icc (cut n) (1-cut n) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact (cut_pos n).trans_le hx.1
  have hf : ContinuousOn (fun t => realPower t p / p) (Icc (cut n) (1-cut n)) :=
    ((realPower_continuous_base p).mono hsub).div_const p
  have hd (x : ℝ) (hx : x ∈ Ioo (cut n) (1-cut n)) :
      HasDerivAt (fun t => realPower t p / p) (betaIntegrand p 1 x) x := by
    have hx0 : 0 < x := (cut_pos n).trans hx.1
    have hx1 : x < 1 := by linarith [hx.2, cut_pos n]
    have hpower : HasDerivAt (fun t => realPower t p) (p * realPower x (p-1)) x :=
      realPower_hasDerivAt p x hx0
    convert hpower.div_const p using 1
    change realPower x (p-1) * realPower (1-x) (1-1) = _
    rw [sub_self, realPower_zero_exponent _ (sub_pos.mpr hx1), mul_one]
    field_simp
  exact (real_ftc_second _ _ _ _ (by linarith [cut_lt_half n]) hf hd
    (trim_integrable p 1 n)).trans (by ring)

theorem beta_one_right : betaOneRight := by
  intro p hp
  have h₀ : Tendsto (fun n => realPower (cut n) p) atTop (𝓝 0) := by
    have h := (Real.continuous_rpow_const hp.le).continuousAt.tendsto.comp cut_tendsto
    rw [Real.zero_rpow hp.ne'] at h
    exact h.congr (fun n => (realPower_eq_rpow _ (cut_pos n) p).symm)
  have h₁ : Tendsto (fun n => realPower (1-cut n) p) atTop (𝓝 1) := by
    have hc : Tendsto (fun n => 1-cut n) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub cut_tendsto
    have h := (Real.continuous_rpow_const hp.le).continuousAt.tendsto.comp hc
    rw [Real.one_rpow] at h
    exact h.congr (fun n => (realPower_eq_rpow _ (by linarith [cut_lt_half n]) p).symm)
  exact tendsto_nhds_unique (betaTrim_tendsto p 1 hp zero_lt_one)
    (by
      have h := ((h₁.sub h₀).div_const p).congr (fun n => (betaTrim_one p hp n).symm)
      simpa only [sub_zero] using h)

/-- Finite induction on the second parameter; no Gamma formula is used. -/
theorem beta_nat_add_one_right : betaNatAddOneRight := by
  intro s hs n
  induction n with
  | zero => simpa using beta_one_right s hs
  | succ n ih =>
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hd : s + ((n : ℝ) + 1) ≠ 0 := ne_of_gt (add_pos hs hn)
    have hprod : (∏ j ∈ Finset.range (n+1), (s + (j : ℝ))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact ne_of_gt (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg j))
    change beta s ((n : ℝ)+1) = _ at ih
    have hrec := beta_add_one_right s ((n : ℝ)+1) hs hn
    change beta s (((n : ℝ)+1)+1) = ((n : ℝ)+1) * beta s ((n : ℝ)+1) /
      (s + ((n : ℝ)+1)) at hrec
    change beta s ((↑(n+1) : ℝ)+1) = _
    rw [Nat.cast_add, Nat.cast_one, hrec, ih,
      Finset.prod_range_succ (fun j : ℕ => s + (j : ℝ)) (n+1),
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hprod, hd]

end SingleVariableAnalysis.SpecialIntegrals
