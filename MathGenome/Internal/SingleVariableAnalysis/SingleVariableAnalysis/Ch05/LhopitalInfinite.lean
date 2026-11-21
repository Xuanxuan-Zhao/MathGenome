import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.LhopitalInfinite
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Algebra
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! K03.05.lhopital_infinite. Cauchy's mean value theorem compares increments
on a fixed approach interval. The constants left by fixing its base point
vanish after division by g. No convergence or divergence assumption on f
is used. The three theorems cover every value of the extended real line. -/
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology
open private algebraApproachFilter approachLimit_filter_iff
  from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Algebra

/-- Absolute divergence forces an eventual nonzero denominator. -/
theorem lhopital_infinite_eventually_nonzero (g : ℝ → ℝ) (J : Set ℝ)
    (q : RealApproach)
    (hg : ∀ B : ℝ, ApproachEventually J q (fun x => B < |g x|)) :
    ApproachEventually J q (fun x => g x ≠ 0) := by
  obtain ⟨r, hr, h⟩ := hg 0
  exact ⟨r, hr, fun x hx hxr => abs_pos.mp (h x hx hxr)⟩

private theorem endpoint_region_ordConnected {J : Set ℝ} {q : RealApproach}
    (hJ : IsOpenIntervalEndpoint J q) (r : ℝ) :
    OrdConnected (ApproachRegion q r) := by
  rcases hJ with ⟨_, _, _, hq⟩
  cases q <;> simp only [ApproachRegion] at *
  all_goals infer_instance

/-- Cauchy's ratio equality on either orientation of a segment. -/
theorem cauchy_ratio_on_interval {S : Set ℝ} (hS : OrdConnected S)
    {f g : ℝ → ℝ} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ S, DifferentiableAt ℝ g x)
    (hgn : ∀ x ∈ S, deriv g x ≠ 0)
    {t x : ℝ} (ht : t ∈ S) (hx : x ∈ S) (hne : x ≠ t) :
    ∃ c ∈ S, (f x - f t) / (g x - g t) = deriv f c / deriv g c := by
  have forward {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      ∃ c ∈ S, (f b - f a) / (g b - g a) = deriv f c / deriv g c := by
    have hsub : Icc a b ⊆ S := hS.out ha hb
    obtain ⟨_, c, hc, _, _, he⟩ := cauchy_mean_value_ratio f g a b hab
      (fun y hy => (hf y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy => (hg y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy => hf y (hsub (Ioo_subset_Icc_self hy)))
      (fun y hy => hg y (hsub (Ioo_subset_Icc_self hy)))
      (fun y hy => hgn y (hsub (Ioo_subset_Icc_self hy)))
    exact ⟨c, hsub (Ioo_subset_Icc_self hc), he⟩
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨c, hc, he⟩ := forward hx ht h
    refine ⟨c, hc, ?_⟩
    rw [← neg_sub (f t) (f x), ← neg_sub (g t) (g x), neg_div_neg_eq]
    exact he
  · exact forward ht hx h

private theorem inverse_tendsto_zero {g : ℝ → ℝ} {J : Set ℝ} {q : RealApproach}
    (hg : ∀ B : ℝ, ApproachEventually J q (fun x => B < |g x|)) :
    Tendsto (fun x => (g x)⁻¹) (algebraApproachFilter J q) (𝓝 0) := by
  have htop : Tendsto (fun x => ‖g x‖) (algebraApproachFilter J q) atTop := by
    apply tendsto_atTop.2
    intro B
    have h : ∀ᶠ x in algebraApproachFilter J q, B < |g x| := hg B
    exact h.mono (fun x hx => le_of_lt hx)
  exact tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp htop)

/-- Every eventual derivative-ratio condition holds for increments from
some fixed base point, on an approach neighborhood, once x ≠ that point. -/
private theorem eventual_secant_condition {f g : ℝ → ℝ} {J : Set ℝ}
    {q : RealApproach} (hJ : IsOpenIntervalEndpoint J q)
    (hf : ∀ x ∈ J, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ J, DifferentiableAt ℝ g x)
    (hgn : ∀ x ∈ J, deriv g x ≠ 0)
    {P : ℝ → Prop}
    (hP : ApproachEventually J q (fun x => P (deriv f x / deriv g x))) :
    ∃ t ∈ J, ∀ᶠ x in algebraApproachFilter J q,
      x ≠ t → P ((f x - f t) / (g x - g t)) := by
  obtain ⟨r, hr, h⟩ := hP
  obtain ⟨t, ht, htr⟩ := hJ.2.2.1 r hr
  refine ⟨t, ht, ?_⟩
  change ApproachEventually J q _
  refine ⟨r, hr, fun x hx hxr hne => ?_⟩
  have hS := hJ.2.1.inter (endpoint_region_ordConnected hJ r)
  obtain ⟨c, hc, he⟩ := cauchy_ratio_on_interval hS
    (fun y hy => hf y hy.1) (fun y hy => hg y hy.1)
    (fun y hy => hgn y hy.1) ⟨ht, htr⟩ ⟨hx, hxr⟩ hne
  rw [he]
  exact h c hc.1 hc.2

private theorem eventually_denominator_separated {g : ℝ → ℝ} {J : Set ℝ}
    {q : RealApproach}
    (hg : ∀ B : ℝ, ApproachEventually J q (fun x => B < |g x|)) (t : ℝ) :
    ∀ᶠ x in algebraApproachFilter J q, g x ≠ 0 ∧ g x ≠ g t ∧ x ≠ t := by
  have h : ∀ᶠ x in algebraApproachFilter J q, |g t| + 1 < |g x| := hg _
  filter_upwards [h] with x hx
  have hn : g x ≠ 0 := abs_pos.mp (by linarith [abs_nonneg (g t)])
  have hnt : g x ≠ g t := by intro he; rw [he] at hx; linarith
  exact ⟨hn, hnt, fun he => hnt (congrArg g he)⟩

private theorem quotient_increment_identity (f g : ℝ → ℝ) (x t L : ℝ)
    (hg : g x ≠ 0) (hgt : g x ≠ g t) :
    f x / g x - L =
      ((f x - f t) / (g x - g t) - L) * (1 - g t / g x) +
        (f t - L * g t) / g x := by
  field_simp [hg, sub_ne_zero.mpr hgt]
  ring

/-- Infinite-denominator L'Hôpital with an arbitrary finite real limit. -/
theorem lhopital_infinite_finite (f g : ℝ → ℝ) (J : Set ℝ)
    (q : RealApproach) (L : ℝ) (hJ : IsOpenIntervalEndpoint J q)
    (hf : ∀ x ∈ J, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ J, DifferentiableAt ℝ g x)
    (hgn : ∀ x ∈ J, deriv g x ≠ 0)
    (hgi : ∀ B : ℝ, ApproachEventually J q (fun x => B < |g x|))
    (hratio : FiniteApproachLimit (fun x => deriv f x / deriv g x) J q L) :
    ApproachEventually J q (fun x => g x ≠ 0) ∧
      FiniteApproachLimit (fun x => f x / g x) J q L := by
  refine ⟨lhopital_infinite_eventually_nonzero g J q hgi, hratio.1, ?_⟩
  intro ε hε
  have hδ : 0 < ε / 2 := half_pos hε
  have hP : ApproachEventually J q (fun x => |deriv f x / deriv g x - L| < ε / 2) := by
    simpa only [Real.dist_eq] using hratio.2 (ε / 2) hδ
  obtain ⟨t, _, hsec⟩ := eventual_secant_condition hJ hf hg hgn
    (P := fun r => |r - L| < ε / 2) hP
  have hinv := inverse_tendsto_zero hgi
  have hconst (C : ℝ) :
      Tendsto (fun x => C / g x) (algebraApproachFilter J q) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul C
  have hK : Tendsto (fun x => 1 - g t / g x)
      (algebraApproachFilter J q) (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (hconst (g t))
  have hb : Tendsto (fun x => (ε / 2) * |1 - g t / g x| +
      |(f t - L * g t) / g x|) (algebraApproachFilter J q) (𝓝 (ε / 2)) := by
    simpa using (hK.abs.const_mul (ε / 2)).add (hconst (f t - L * g t)).abs
  have hsmall := hb.eventually (gt_mem_nhds (by linarith : ε / 2 < ε))
  have hresult : ∀ᶠ x in algebraApproachFilter J q, |f x / g x - L| < ε := by
    filter_upwards [hsec, eventually_denominator_separated hgi t, hsmall] with x hs hn hb
    rw [quotient_increment_identity f g x t L hn.1 hn.2.1]
    calc
      _ ≤ |((f x - f t) / (g x - g t) - L) * (1 - g t / g x)| +
          |(f t - L * g t) / g x| := abs_add_le _ _
      _ = |(f x - f t) / (g x - g t) - L| * |1 - g t / g x| +
          |(f t - L * g t) / g x| := by rw [abs_mul]
      _ ≤ (ε / 2) * |1 - g t / g x| + |(f t - L * g t) / g x| :=
        add_le_add (mul_le_mul_of_nonneg_right (le_of_lt (hs hn.2.2))
          (abs_nonneg _)) le_rfl
      _ < ε := hb
  change ∀ᶠ x in algebraApproachFilter J q, dist (f x / g x) L < ε
  filter_upwards [hresult] with x hx
  simpa only [Real.dist_eq] using hx

/-- Infinite-denominator L'Hôpital with derivative ratio tending to +∞. -/
theorem lhopital_infinite_posInfinity (f g : ℝ → ℝ) (J : Set ℝ)
    (q : RealApproach) (hJ : IsOpenIntervalEndpoint J q)
    (hf : ∀ x ∈ J, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ J, DifferentiableAt ℝ g x)
    (hgn : ∀ x ∈ J, deriv g x ≠ 0)
    (hgi : ∀ B : ℝ, ApproachEventually J q (fun x => B < |g x|))
    (hratio : RealLimitToPosInfinity (fun x => deriv f x / deriv g x) J q) :
    ApproachEventually J q (fun x => g x ≠ 0) ∧
      RealLimitToPosInfinity (fun x => f x / g x) J q := by
  refine ⟨lhopital_infinite_eventually_nonzero g J q hgi, hratio.1, ?_⟩
  intro B
  let A : ℝ := 2 * (|B| + 2)
  have hA : 0 < A := by dsimp [A]; linarith [abs_nonneg B]
  obtain ⟨t, _, hsec⟩ := eventual_secant_condition hJ hf hg hgn (hratio.2 A)
  have hinv := inverse_tendsto_zero hgi
  have hconst (C : ℝ) :
      Tendsto (fun x => C / g x) (algebraApproachFilter J q) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul C
  have hK : Tendsto (fun x => 1 - g t / g x)
      (algebraApproachFilter J q) (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (hconst (g t))
  have hKpos := hK.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hV := (hconst (f t)).eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  have hresult : ∀ᶠ x in algebraApproachFilter J q, B < f x / g x := by
    filter_upwards [hsec, eventually_denominator_separated hgi t, hKpos, hV]
      with x hs hn hk hv
    have hs' := hs hn.2.2
    have hspos : 0 < (f x - f t) / (g x - g t) := hA.trans hs'
    have hm : A / 2 < ((f x - f t) / (g x - g t)) * (1 - g t / g x) := by
      nlinarith [mul_pos hspos (sub_pos.mpr hk)]
    have he := quotient_increment_identity f g x t 0 hn.1 hn.2.1
    simp only [sub_zero, zero_mul] at he
    rw [he]
    dsimp [A] at hm
    linarith [le_abs_self B]
  exact hresult

/-- Infinite-denominator L'Hôpital with derivative ratio tending to -∞. -/
theorem lhopital_infinite_negInfinity (f g : ℝ → ℝ) (J : Set ℝ)
    (q : RealApproach) (hJ : IsOpenIntervalEndpoint J q)
    (hf : ∀ x ∈ J, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ J, DifferentiableAt ℝ g x)
    (hgn : ∀ x ∈ J, deriv g x ≠ 0)
    (hgi : ∀ B : ℝ, ApproachEventually J q (fun x => B < |g x|))
    (hratio : RealLimitToNegInfinity (fun x => deriv f x / deriv g x) J q) :
    ApproachEventually J q (fun x => g x ≠ 0) ∧
      RealLimitToNegInfinity (fun x => f x / g x) J q := by
  have hneg : RealLimitToPosInfinity (fun x => deriv (fun y => -f y) x / deriv g x) J q := by
    refine ⟨hratio.1, fun B => ?_⟩
    obtain ⟨r, hr, h⟩ := hratio.2 (-B)
    refine ⟨r, hr, fun x hx hxr => ?_⟩
    change B < deriv (-f) x / deriv g x
    rw [(hf x hx).hasDerivAt.neg.deriv, neg_div]
    linarith [h x hx hxr]
  obtain ⟨hn, hlim⟩ := lhopital_infinite_posInfinity (fun x => -f x) g J q hJ
    (fun x hx => (hf x hx).neg) hg hgn hgi hneg
  refine ⟨hn, hlim.1, fun B => ?_⟩
  obtain ⟨r, hr, h⟩ := hlim.2 (-B)
  refine ⟨r, hr, fun x hx hxr => ?_⟩
  have hh := h x hx hxr
  change -B < -f x / g x at hh
  change f x / g x < B
  rw [neg_div] at hh
  linarith

end SingleVariableAnalysis
