import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Laurent
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric Filter
open scoped Topology NNReal ENNReal

namespace D12Complex.Laurent

/-- The center is excluded on every annulus in the original theorem. -/
theorem sub_ne_zero_of_mem_annulus {a z : ℂ} {r₀ : ℝ} {R₀ : ℝ≥0∞}
    (hr₀ : 0 ≤ r₀) (hz : z ∈ annulus a r₀ R₀) : z - a ≠ 0 :=
  norm_pos_iff.mp (hr₀.trans_lt hz.1)

/-- A closed subannulus with strictly interior radii is contained in the open annulus. -/
theorem closedSubannulus_subset {a : ℂ} {r₀ s t : ℝ} {R₀ : ℝ≥0∞}
    (hs : r₀ < s) (ht : ENNReal.ofReal t < R₀) :
    closedSubannulus a s t ⊆ annulus a r₀ R₀ := by
  intro z hz
  refine ⟨hs.trans_le hz.1, ?_⟩
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_le_ofReal hz.2).trans_lt ht

/-- Holomorphy of the integer-power coefficient integrand on the annulus. -/
theorem differentiableAt_coefficientIntegrand {a z : ℂ} {r₀ : ℝ} {R₀ : ℝ≥0∞}
    {f : ℂ → ℂ} (hr₀ : 0 ≤ r₀) (hf : HolomorphicOn (annulus a r₀ R₀) f)
    (hz : z ∈ annulus a r₀ R₀) (n : ℤ) :
    DifferentiableAt ℂ (fun w => f w / (w - a) ^ (n + 1)) z :=
  (hf.2 z hz).div ((differentiableAt_id.sub_const a).zpow
    (Or.inl (sub_ne_zero_of_mem_annulus hr₀ hz)))
    (zpow_ne_zero _ (sub_ne_zero_of_mem_annulus hr₀ hz))

private theorem coefficientIntegral_eq_of_le {a : ℂ} {r₀ ρ σ : ℝ} {R₀ : ℝ≥0∞}
    {f : ℂ → ℂ} (hr₀ : 0 ≤ r₀) (hf : HolomorphicOn (annulus a r₀ R₀) f)
    (hρ : r₀ < ρ) (hσ : ENNReal.ofReal σ < R₀) (hρσ : ρ ≤ σ) (n : ℤ) :
    coefficientIntegral f a σ n = coefficientIntegral f a ρ n := by
  have hK : closedBall a σ \ ball a ρ ⊆ annulus a r₀ R₀ := by
    intro z hz
    exact closedSubannulus_subset hρ hσ
      ⟨by simpa only [mem_ball, dist_eq_norm, not_lt] using hz.2,
        by simpa only [mem_closedBall, dist_eq_norm] using hz.1⟩
  have hc : ContinuousOn (fun w => f w / (w - a) ^ (n + 1))
      (closedBall a σ \ ball a ρ) := by
    intro z hz
    exact (differentiableAt_coefficientIntegrand hr₀ hf (hK hz) n).continuousAt.continuousWithinAt
  have hd : ∀ z ∈ (ball a σ \ closedBall a ρ) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w => f w / (w - a) ^ (n + 1)) z := by
    intro z hz
    apply differentiableAt_coefficientIntegrand hr₀ hf _ n
    apply hK
    exact ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩
  unfold coefficientIntegral
  rw [Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (hr₀.trans_lt hρ) hρσ countable_empty hc hd]

theorem coefficientIntegral_independent :
    Specs.D12Complex.Ch07.Laurent.coefficientIntegral_independent_type := by
  intro a r₀ R₀ f hr₀ hf ρ σ hρ hρR hσ hσR n
  rcases le_total ρ σ with h | h
  · exact (coefficientIntegral_eq_of_le hr₀ hf hρ hσR h n).symm
  · exact coefficientIntegral_eq_of_le hr₀ hf hσ hρR h n

theorem coefficientIntegral_bound :
    Specs.D12Complex.Ch07.Laurent.coefficientIntegral_bound_type := by
  intro f a ρ M hρ hf n
  have hb : ∀ w ∈ sphere a ρ, ‖f w / (w - a) ^ (n + 1)‖ ≤ M / ρ ^ (n + 1) := by
    intro w hw
    rw [norm_div, norm_zpow, mem_sphere_iff_norm.mp hw]
    exact div_le_div_of_nonneg_right (hf w hw) (le_of_lt (zpow_pos hρ _))
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le hb
  change ‖coefficientIntegral f a ρ n‖ ≤ _ at h
  convert h using 1
  calc
    M * ρ ^ (-n) = M * ρ ^ (-(n + 1) + 1) := by congr 2; omega
    _ = M * (ρ ^ (-(n + 1)) * ρ ^ (1 : ℤ)) := by rw [zpow_add₀ hρ.ne']
    _ = ρ * (M / ρ ^ (n + 1)) := by rw [zpow_one, zpow_neg]; ring

theorem coefficientIntegral_monomial :
    Specs.D12Complex.Ch07.Laurent.coefficientIntegral_monomial_type := by
  intro a ρ hρ m n
  have hi : circleIntegral (fun w => (w - a) ^ m / (w - a) ^ (n + 1)) a ρ =
      circleIntegral (fun w => (w - a) ^ (m - n - 1)) a ρ := by
    apply circleIntegral.integral_congr hρ.le
    intro w hw
    have hw0 : w - a ≠ 0 := norm_ne_zero_iff.mp (by
      rw [mem_sphere_iff_norm.mp hw]; exact hρ.ne')
    dsimp only
    rw [← zpow_sub₀ hw0]
    congr 1
    ring
  unfold coefficientIntegral
  rw [hi]
  split_ifs with hmn
  · subst m
    simp only [sub_self, zero_sub, zpow_neg_one]
    rw [circleIntegral.integral_sub_center_inv a hρ.ne']
    apply inv_mul_cancel₀
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  · rw [circleIntegral.integral_sub_zpow_of_ne (by omega)]
    simp

theorem iteratedDeriv_monomial :
    Specs.D12Complex.Ch07.Laurent.iteratedDeriv_monomial_type := by
  intro a b z m k
  rw [iteratedDeriv_const_mul_field]
  have h := congrFun (iteratedDeriv_comp_sub_const (n := k)
    (f := fun w : ℂ => w ^ m) (s := a)) z
  rw [h, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  ring

/-- The Weierstrass majorant test, with absolute uniform convergence explicit. -/
theorem absoluteUniformSeriesOn_of_majorant {u : ℕ → ℂ → ℂ} {K : Set ℂ}
    {b : ℕ → ℝ} (hb : Summable b) (hu : ∀ n z, z ∈ K → ‖u n z‖ ≤ b n) :
    AbsoluteUniformSeriesOn u K := by
  refine ⟨fun z hz => hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hu n z hz),
    tendstoUniformlyOn_tsum_nat hb hu, ?_⟩
  exact tendstoUniformlyOn_tsum_nat hb (by simpa only [norm_norm] using hu)

/-- The two geometric majorants from the inner and outer coefficient estimates. -/
theorem exists_geometric_majorants_of_bounds (c : ℤ → ℂ) (a : ℂ) (s t ρ₁ ρ₂ M₁ M₂ : ℝ)
    (hs : 0 < s) (hst : s ≤ t) (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (htρ₂ : t < ρ₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hcpos : ∀ n : ℕ, ‖c n‖ ≤ M₂ * ρ₂ ^ (-(n : ℤ)))
    (hcneg : ∀ n : ℕ, ‖c (-(n : ℤ) - 1)‖ ≤ M₁ * ρ₁ ^ (n + 1)) :
    (∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t →
      ‖positiveTerm c a n z‖ ≤ b n) ∧
    (∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t →
      ‖negativeTerm c a n z‖ ≤ b n) := by
  have ht : 0 ≤ t := hs.le.trans hst
  have hρ₂ : 0 < ρ₂ := hs.trans_le hst |>.trans htρ₂
  constructor
  · have hq : t / ρ₂ < 1 := (div_lt_one hρ₂).mpr htρ₂
    refine ⟨_, ((summable_geometric_of_lt_one (div_nonneg ht hρ₂.le) hq).mul_left M₂), ?_⟩
    intro n z hz
    change ‖c (n : ℤ) * (z - a) ^ n‖ ≤ M₂ * (t / ρ₂) ^ n
    rw [norm_mul, norm_pow]
    calc
      ‖c (n : ℤ)‖ * ‖z - a‖ ^ n ≤ (M₂ * ρ₂ ^ (-(n : ℤ))) * t ^ n := by
        gcongr
        exacts [hcpos n, hz.2]
      _ = M₂ * (t / ρ₂) ^ n := by
        rw [zpow_neg, zpow_natCast, div_pow]
        ring
  · have hq : ρ₁ / s < 1 := (div_lt_one hs).mpr hρ₁s
    have hsum : Summable (fun n : ℕ => M₁ * (ρ₁ / s) ^ (n + 1)) := by
      simpa only [pow_succ, mul_left_comm, mul_comm, mul_assoc] using
        ((summable_geometric_of_lt_one (div_nonneg hρ₁.le hs.le) hq).mul_left (M₁ * (ρ₁ / s)))
    refine ⟨_, hsum, ?_⟩
    intro n z hz
    have hzpos : 0 < ‖z - a‖ := hs.trans_le hz.1
    change ‖c (-(n : ℤ) - 1) * (z - a) ^ (-(n : ℤ) - 1)‖ ≤ M₁ * (ρ₁ / s) ^ (n + 1)
    rw [norm_mul, norm_zpow]
    have hn : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hn, zpow_neg, zpow_natCast]
    calc
      ‖c (-((n + 1 : ℕ) : ℤ))‖ * (‖z - a‖ ^ (n + 1))⁻¹ ≤
          (M₁ * ρ₁ ^ (n + 1)) * (s ^ (n + 1))⁻¹ := by
        gcongr
        · simpa only [hn] using hcneg n
        · exact hz.1
      _ = M₁ * (ρ₁ / s) ^ (n + 1) := by rw [div_pow]; ring

/-- Geometric bounds imply absolute uniform convergence of both parts. -/
theorem normalConvergence_of_bounds (c : ℤ → ℂ) (a : ℂ) (s t ρ₁ ρ₂ M₁ M₂ : ℝ)
    (hs : 0 < s) (hst : s ≤ t) (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (htρ₂ : t < ρ₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hcpos : ∀ n : ℕ, ‖c n‖ ≤ M₂ * ρ₂ ^ (-(n : ℤ)))
    (hcneg : ∀ n : ℕ, ‖c (-(n : ℤ) - 1)‖ ≤ M₁ * ρ₁ ^ (n + 1)) :
    AbsoluteUniformSeriesOn (positiveTerm c a) (closedSubannulus a s t) ∧
    AbsoluteUniformSeriesOn (negativeTerm c a) (closedSubannulus a s t) := by
  obtain ⟨⟨b, hb, hbp⟩, ⟨d, hd, hdn⟩⟩ := exists_geometric_majorants_of_bounds c a s t
    ρ₁ ρ₂ M₁ M₂ hs hst hρ₁ hρ₁s htρ₂ hM₁ hM₂ hcpos hcneg
  exact ⟨absoluteUniformSeriesOn_of_majorant hb hbp, absoluteUniformSeriesOn_of_majorant hd hdn⟩

/-- A real radius strictly between a finite nonnegative lower bound and an
extended upper bound exists also when the upper radius is infinity. -/
theorem exists_admissible_radius {t : ℝ} {R₀ : ℝ≥0∞} (ht : 0 ≤ t)
    (hR : ENNReal.ofReal t < R₀) : ∃ ρ : ℝ, t < ρ ∧ ENNReal.ofReal ρ < R₀ := by
  obtain ⟨ρ, _, htρ, hρR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hR
  refine ⟨ρ, ?_, hρR⟩
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp htρ

/-- A continuous holomorphic function is bounded on each admissible circle. -/
theorem exists_circle_bound {a : ℂ} {r₀ ρ : ℝ} {R₀ : ℝ≥0∞} {f : ℂ → ℂ}
    (hf : HolomorphicOn (annulus a r₀ R₀) f)
    (hρ : r₀ < ρ) (hρR : ENNReal.ofReal ρ < R₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ sphere a ρ, ‖f w‖ ≤ M := by
  have hK : sphere a ρ ⊆ annulus a r₀ R₀ := by
    intro z hz
    apply closedSubannulus_subset hρ hρR
    exact ⟨(mem_sphere_iff_norm.mp hz).ge, (mem_sphere_iff_norm.mp hz).le⟩
  have hc : ContinuousOn f (sphere a ρ) :=
    fun w hw => (hf.2 w (hK hw)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_sphere a ρ).exists_bound_of_continuousOn hc
  exact ⟨max M 0, le_max_right _ _, fun w hw => (hM w hw).trans (le_max_left _ _)⟩

theorem normalConvergence_of_coefficientFormula :
    Specs.D12Complex.Ch07.Laurent.normalConvergence_of_coefficientFormula_type := by
  intro a r₀ R₀ f c hr₀ hf hc s t hs hst ht
  obtain ⟨ρ₁, hρ₁, hρ₁s⟩ := exists_between hs
  obtain ⟨ρ₂, htρ₂, hρ₂R⟩ := exists_admissible_radius ((hr₀.trans_lt hs).le.trans hst) ht
  have hρ₁R : ENNReal.ofReal ρ₁ < R₀ :=
    (ENNReal.ofReal_le_ofReal (hρ₁s.le.trans hst)).trans_lt ht
  have hρ₂ : r₀ < ρ₂ := hs.trans_le hst |>.trans htρ₂
  obtain ⟨M₁, hM₁, hf₁⟩ := exists_circle_bound hf hρ₁ hρ₁R
  obtain ⟨M₂, hM₂, hf₂⟩ := exists_circle_bound hf hρ₂ hρ₂R
  apply normalConvergence_of_bounds c a s t ρ₁ ρ₂ M₁ M₂ (hr₀.trans_lt hs) hst
    (hr₀.trans_lt hρ₁) hρ₁s htρ₂ hM₁ hM₂
  · intro n
    rw [hc ρ₂ hρ₂ hρ₂R]
    exact coefficientIntegral_bound f a ρ₂ M₂ (hr₀.trans_lt hρ₂) hf₂ n
  · intro n
    rw [hc ρ₁ hρ₁ hρ₁R]
    have hn : -(-(n : ℤ) - 1) = ((n + 1 : ℕ) : ℤ) := by omega
    simpa only [hn, zpow_natCast] using
      coefficientIntegral_bound f a ρ₁ M₁ (hr₀.trans_lt hρ₁) hf₁ (-(n : ℤ) - 1)

/-- The reciprocal kernel has zero integral when its pole is outside the disk. -/
theorem circleIntegral_sub_inv_of_exterior (a z : ℂ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hz : ρ < ‖z - a‖) :
    circleIntegral (fun w => (w - z)⁻¹) a ρ = 0 := by
  have hne : ∀ w ∈ closedBall a ρ, w - z ≠ 0 := by
    intro w hw
    apply sub_ne_zero.mpr
    intro hwz
    subst w
    exact (not_le_of_gt hz) (mem_closedBall_iff_norm.mp hw)
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ countable_empty
    ((continuousOn_id.sub continuousOn_const).inv₀ hne)
    (fun w hw => (differentiableAt_id.sub_const z).inv (hne w (ball_subset_closedBall hw.1)))

/-- Off the pole circle, the regularized slope integral is the kernel integral
minus the constant-value reciprocal integral. -/
theorem circleIntegral_dslope (f : ℂ → ℂ) (a z : ℂ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hne : ∀ w ∈ sphere a ρ, w ≠ z)
    (hf : ContinuousOn f (sphere a ρ)) :
    circleIntegral (dslope f z) a ρ = circleIntegral (fun w => f w / (w - z)) a ρ -
      f z * circleIntegral (fun w => (w - z)⁻¹) a ρ := by
  have hc : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere a ρ) :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun w hw => sub_ne_zero.mpr (hne w hw))
  calc
    circleIntegral (dslope f z) a ρ =
        circleIntegral (fun w => f w / (w - z) - f z * (w - z)⁻¹) a ρ := by
      apply circleIntegral.integral_congr hρ
      intro w hw
      rw [dslope_of_ne _ (hne w hw)]
      simp only [slope_def_module, smul_eq_mul, div_eq_mul_inv]
      ring
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [circleIntegral.integral_sub (f := fun w => f w * (w - z)⁻¹)
        (g := fun w => f z * (w - z)⁻¹) ((hf.mul hc).circleIntegrable hρ)
        ((continuousOn_const.mul hc).circleIntegrable hρ), circleIntegral.integral_const_mul]

theorem annular_cauchy_formula : Specs.D12Complex.Ch07.Laurent.annular_cauchy_formula_type := by
  intro a z r₀ ρ σ R₀ f hr₀ hf hρ hρz hzσ hσR
  have hρpos : 0 < ρ := hr₀.trans_lt hρ
  have hσpos : 0 < σ := (hρpos.trans hρz).trans hzσ
  have hK : closedBall a σ \ ball a ρ ⊆ annulus a r₀ R₀ := by
    intro w hw
    apply closedSubannulus_subset hρ hσR
    exact ⟨by simpa only [mem_ball, dist_eq_norm, not_lt] using hw.2,
      mem_closedBall_iff_norm.mp hw.1⟩
  have hzA : z ∈ annulus a r₀ R₀ := hK
    ⟨mem_closedBall_iff_norm.mpr hzσ.le, by simpa only [mem_ball, dist_eq_norm, not_lt] using hρz.le⟩
  have hc : ContinuousOn (dslope f z) (closedBall a σ \ ball a ρ) := by
    intro w hw
    have hh : ContinuousAt (dslope f z) w := by
      by_cases hwz : w = z
      · subst w
        exact continuousAt_dslope_same.mpr (hf.2 z hzA)
      · exact (continuousAt_dslope_of_ne hwz).mpr (hf.2 w (hK hw)).continuousAt
    exact hh.continuousWithinAt
  have hd : ∀ w ∈ (ball a σ \ closedBall a ρ) \ ({z} : Set ℂ),
      DifferentiableAt ℂ (dslope f z) w := by
    intro w hw
    apply (differentiableAt_dslope_of_ne (by simpa only [mem_singleton_iff] using hw.2)).mpr
    apply hf.2 w
    apply hK
    exact ⟨ball_subset_closedBall hw.1.1, fun h => hw.1.2 (ball_subset_closedBall h)⟩
  have heq := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hρpos (hρz.trans hzσ).le (countable_singleton z) hc hd
  have hsphere (r : ℝ) (hr : ρ ≤ r) (hrσ : r ≤ σ) : sphere a r ⊆ annulus a r₀ R₀ := by
    intro w hw
    apply hK
    exact ⟨mem_closedBall_iff_norm.mpr ((mem_sphere_iff_norm.mp hw).le.trans hrσ),
      by simpa only [mem_ball, dist_eq_norm, not_lt, mem_sphere_iff_norm.mp hw] using hr⟩
  have hρne : ∀ w ∈ sphere a ρ, w ≠ z := by
    intro w hw hwz
    subst w
    exact (ne_of_gt hρz) (mem_sphere_iff_norm.mp hw)
  have hσne : ∀ w ∈ sphere a σ, w ≠ z := by
    intro w hw hwz
    subst w
    exact (ne_of_lt hzσ) (mem_sphere_iff_norm.mp hw)
  rw [circleIntegral_dslope f a z σ hσpos.le hσne
        (fun w hw => (hf.2 w (hsphere σ (hρz.trans hzσ).le le_rfl hw)).continuousAt.continuousWithinAt),
      circleIntegral_dslope f a z ρ hρpos.le hρne
        (fun w hw => (hf.2 w (hsphere ρ le_rfl (hρz.trans hzσ).le hw)).continuousAt.continuousWithinAt),
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_iff_norm.mpr hzσ),
      circleIntegral_sub_inv_of_exterior a z ρ hρpos.le hρz, mul_zero, sub_zero] at heq
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  apply (eq_inv_mul_iff_mul_eq₀ hπ).mpr
  linear_combination -heq

/-- The outer geometric expansion, for an arbitrary circle-integrable f. -/
theorem hasSum_positive_coefficientIntegral (f : ℂ → ℂ) (a z : ℂ) (ρ : ℝ)
    (hf : CircleIntegrable f a ρ) (hz : ‖z - a‖ < ρ) :
    HasSum (fun n : ℕ => coefficientIntegral f a ρ (n : ℤ) * (z - a) ^ n)
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (fun w => f w / (w - z)) a ρ) := by
  have hterm (n : ℕ) : cauchyPowerSeries f a ρ n (fun _ => z - a) =
      coefficientIntegral f a ρ (n : ℤ) * (z - a) ^ n := by
    simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
      smul_eq_mul, coefficientIntegral, ← Int.natCast_one, ← Int.natCast_add, zpow_natCast,
      div_eq_mul_inv, pow_succ, mul_inv, inv_pow, mul_comm, mul_assoc]
  convert hasSum_cauchyPowerSeries_integral hf hz using 1
  · exact funext (fun n => (hterm n).symm)
  · simp only [smul_eq_mul, add_sub_cancel]
    congr 1
    apply circleIntegral.integral_congr (norm_nonneg (z - a) |>.trans hz.le)
    intro w hw
    simp only [div_eq_mul_inv, mul_comm]

/-- Uniformly summable continuous integrands may be integrated term by term. -/
theorem hasSum_circleIntegral_of_majorant {u : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (a : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) {b : ℕ → ℝ} (hb : Summable b)
    (hbound : ∀ n w, w ∈ sphere a ρ → ‖u n w‖ ≤ b n)
    (hc : ∀ n, ContinuousOn (u n) (sphere a ρ))
    (hs : ∀ w ∈ sphere a ρ, HasSum (fun n => u n w) (g w)) :
    HasSum (fun n => circleIntegral (u n) a ρ) (circleIntegral g a ρ) := by
  have habs : Summable (fun n => ‖circleIntegral (u n) a ρ‖) := by
    apply (hb.mul_left (2 * Real.pi * ρ)).of_nonneg_of_le (fun _ => norm_nonneg _)
    exact fun n => circleIntegral.norm_integral_le_of_norm_le_const hρ (hbound n)
  apply (hasSum_iff_tendsto_nat_of_summable_norm habs).mpr
  have hu := (absoluteUniformSeriesOn_of_majorant hb hbound).2.1
  have hu' := hu.congr_right (fun w hw => (hs w hw).tsum_eq)
  have hi := hu'.tendsto_circleIntegral_of_continuousOn hρ
    (Eventually.of_forall (fun N => continuousOn_finsetSum (Finset.range N) (fun n _ => hc n)))
  simpa only [circleIntegral.integral_fun_sum (fun n _ => (hc n).circleIntegrable hρ)] using hi

/-- The inner geometric expansion has the minus sign dictated by the inner
boundary orientation. No holomorphy inside the circle is assumed. -/
theorem hasSum_negative_coefficientIntegral (f : ℂ → ℂ) (a z : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hf : ContinuousOn f (sphere a ρ)) (hz : ρ < ‖z - a‖) :
    HasSum (fun n : ℕ => coefficientIntegral f a ρ (-(n : ℤ) - 1) *
      (z - a) ^ (-(n : ℤ) - 1))
      (-((2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (fun w => f w / (w - z)) a ρ)) := by
  have hzpos : 0 < ‖z - a‖ := hρ.trans hz
  have hz0 : z - a ≠ 0 := norm_pos_iff.mp hzpos
  obtain ⟨M₀, hM₀⟩ := (isCompact_sphere a ρ).exists_bound_of_continuousOn hf
  let M := max M₀ 0
  have hM : ∀ w ∈ sphere a ρ, ‖f w‖ ≤ M :=
    fun w hw => (hM₀ w hw).trans (le_max_left _ _)
  let u : ℕ → ℂ → ℂ := fun n w => f w * ((w - a) / (z - a)) ^ n / (z - a)
  have hb : Summable (fun n : ℕ => (M / ‖z - a‖) * (ρ / ‖z - a‖) ^ n) :=
    (summable_geometric_of_lt_one (div_nonneg hρ.le hzpos.le)
      ((div_lt_one hzpos).mpr hz)).mul_left _
  have hbound : ∀ n w, w ∈ sphere a ρ →
      ‖u n w‖ ≤ (M / ‖z - a‖) * (ρ / ‖z - a‖) ^ n := by
    intro n w hw
    dsimp only [u]
    rw [norm_div, norm_mul, norm_pow, norm_div, mem_sphere_iff_norm.mp hw]
    calc
      ‖f w‖ * (ρ / ‖z - a‖) ^ n / ‖z - a‖ ≤ M * (ρ / ‖z - a‖) ^ n / ‖z - a‖ := by
        gcongr; exact hM w hw
      _ = _ := by ring
  have hcu : ∀ n, ContinuousOn (u n) (sphere a ρ) := fun n =>
    (hf.mul (((continuousOn_id.sub continuousOn_const).div_const (z - a)).pow n)).div_const (z - a)
  have hsu : ∀ w ∈ sphere a ρ, HasSum (fun n => u n w) (-(f w / (w - z))) := by
    intro w hw
    have hq : ‖(w - a) / (z - a)‖ < 1 := by
      rw [norm_div, mem_sphere_iff_norm.mp hw]
      exact (div_lt_one hzpos).mpr hz
    have hw0 : w - z ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hwz
      subst w
      exact (ne_of_gt hz) (mem_sphere_iff_norm.mp hw)
    convert (hasSum_geometric_of_norm_lt_one hq).mul_left (f w / (z - a)) using 1
    · funext n
      dsimp only [u]
      ring
    · have hid : 1 - (w - a) / (z - a) = -(w - z) / (z - a) := by
        field_simp
        ring
      rw [hid, inv_div]
      field_simp [hz0, hw0]
  have hsum := (hasSum_circleIntegral_of_majorant a ρ hρ.le hb hbound hcu hsu).mul_left
    (2 * Real.pi * Complex.I : ℂ)⁻¹
  have hterm (n : ℕ) :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (u n) a ρ =
      coefficientIntegral f a ρ (-(n : ℤ) - 1) * (z - a) ^ (-(n : ℤ) - 1) := by
    have hn : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    have hcoef : coefficientIntegral f a ρ (-(n : ℤ) - 1) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          circleIntegral (fun w => f w * (w - a) ^ n) a ρ := by
      unfold coefficientIntegral
      simp only [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by omega,
        zpow_neg, zpow_natCast, div_inv_eq_mul]
    rw [hcoef, hn, zpow_neg, zpow_natCast]
    calc
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          circleIntegral (fun w => ((z - a) ^ (n + 1))⁻¹ * (f w * (w - a) ^ n)) a ρ := by
        congr 1
        apply circleIntegral.integral_congr hρ.le
        intro w hw
        dsimp only [u]
        rw [div_pow, pow_succ]
        field_simp [hz0]
      _ = _ := by rw [circleIntegral.integral_const_mul]; ring
  convert hsum using 1
  · exact funext (fun n => (hterm n).symm)
  · have hneg : circleIntegral (fun w => -(f w / (w - z))) a ρ =
        -circleIntegral (fun w => f w / (w - z)) a ρ := by
      simpa only [neg_one_mul] using
        (circleIntegral.integral_const_mul (-1) (fun w => f w / (w - z)) a ρ)
    rw [hneg]
    ring

/-- Continuity on an admissible circle follows from the given weak holomorphy. -/
theorem continuousOn_circle {a : ℂ} {r₀ ρ : ℝ} {R₀ : ℝ≥0∞} {f : ℂ → ℂ}
    (hf : HolomorphicOn (annulus a r₀ R₀) f)
    (hρ : r₀ < ρ) (hρR : ENNReal.ofReal ρ < R₀) : ContinuousOn f (sphere a ρ) := by
  intro w hw
  apply (hf.2 w _).continuousAt.continuousWithinAt
  exact closedSubannulus_subset hρ hρR
    ⟨(mem_sphere_iff_norm.mp hw).ge, (mem_sphere_iff_norm.mp hw).le⟩

theorem laurent_exists : Specs.D12Complex.Ch07.Laurent.laurent_exists_type := by
  intro a r₀ R₀ f hr₀ hR hf
  obtain ⟨ρ₀, hρ₀, hρ₀R⟩ := exists_admissible_radius hr₀ hR
  let c : ℤ → ℂ := coefficientIntegral f a ρ₀
  have hc : ∀ ρ : ℝ, r₀ < ρ → ENNReal.ofReal ρ < R₀ →
      ∀ n : ℤ, c n = coefficientIntegral f a ρ n := by
    intro ρ hρ hρR n
    exact coefficientIntegral_independent a r₀ R₀ f hr₀ hf ρ₀ ρ hρ₀ hρ₀R hρ hρR n
  refine ⟨c, ?_, hc, normalConvergence_of_coefficientFormula a r₀ R₀ f c hr₀ hf hc⟩
  intro z hz
  obtain ⟨ρ, hρ, hρz⟩ := exists_between hz.1
  have hzR : ENNReal.ofReal ‖z - a‖ < R₀ := by
    change ENNReal.ofReal (‖z - a‖₊ : ℝ) < R₀
    rw [ENNReal.ofReal_coe_nnreal]
    exact hz.2
  obtain ⟨σ, hzσ, hσR⟩ := exists_admissible_radius (norm_nonneg _) hzR
  have hσ : r₀ < σ := hz.1.trans hzσ
  have hρR : ENNReal.ofReal ρ < R₀ :=
    (ENNReal.ofReal_le_ofReal hρz.le).trans_lt hzR
  have hp : HasSum (fun n => positiveTerm c a n z)
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (fun w => f w / (w - z)) a σ) := by
    convert hasSum_positive_coefficientIntegral f a z σ
      ((continuousOn_circle hf hσ hσR).circleIntegrable (hr₀.trans_lt hσ).le) hzσ using 1
    funext n
    dsimp only [positiveTerm]
    rw [hc σ hσ hσR]
  have hn : HasSum (fun n => negativeTerm c a n z)
      (-((2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (fun w => f w / (w - z)) a ρ)) := by
    convert hasSum_negative_coefficientIntegral f a z ρ (hr₀.trans_lt hρ)
      (continuousOn_circle hf hρ hρR) hρz using 1
    funext n
    dsimp only [negativeTerm]
    rw [hc ρ hρ hρR]
  refine ⟨hp.summable, hn.summable, ?_⟩
  change f z = (∑' n, positiveTerm c a n z) + ∑' n, negativeTerm c a n z
  rw [hp.tsum_eq, hn.tsum_eq]
  have heq := annular_cauchy_formula a z r₀ ρ σ R₀ f hr₀ hf hρ hρz hzσ hσR
  rw [mul_sub] at heq
  simpa only [sub_eq_add_neg] using heq

/-- Absolute summability in a representation implies ordinary convergence of
both one-sided partial sums; competitors in uniqueness need only the latter. -/
theorem convergent_of_hasLaurentSeriesOn {f : ℂ → ℂ} {a : ℂ} {r₀ : ℝ} {R₀ : ℝ≥0∞}
    {c : ℤ → ℂ} (h : HasLaurentSeriesOn f a r₀ R₀ c) :
    ConvergentLaurentSeriesOn f a r₀ R₀ c := by
  intro z hz
  obtain ⟨hp, hn, heq⟩ := h z hz
  exact ⟨positivePart c a z, negativePart c a z,
    hp.hasSum.tendsto_sum_nat, hn.hasSum.tendsto_sum_nat, heq⟩

/-- Convergence of ordered partial sums bounds the individual terms, without
assuming absolute convergence. -/
theorem exists_term_bound_of_partialSum_tendsto {u : ℕ → ℂ} {p : ℂ}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, u n) atTop (𝓝 p)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖u n‖ ≤ M := by
  obtain ⟨B, hB⟩ := h.cauchySeq.isBounded_range.exists_norm_le
  let M := max B 0
  have hb (n : ℕ) : ‖∑ j ∈ Finset.range n, u j‖ ≤ M :=
    (hB _ (mem_range_self n)).trans (le_max_left _ _)
  refine ⟨2 * M, by dsimp [M]; positivity, fun n => ?_⟩
  have heq : u n = (∑ j ∈ Finset.range (n + 1), u j) -
      (∑ j ∈ Finset.range n, u j) := by rw [Finset.sum_range_succ]; ring
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith [hb (n + 1), hb n])

/-- Ordinary convergence at one point of each radius already gives the
coefficient bounds needed on every smaller closed subannulus. -/
theorem coefficient_bounds_of_convergent {f : ℂ → ℂ} {c : ℤ → ℂ}
    {a : ℂ} {r₀ ρ : ℝ} {R₀ : ℝ≥0∞} (hr₀ : 0 ≤ r₀)
    (h : ConvergentLaurentSeriesOn f a r₀ R₀ c)
    (hρ : r₀ < ρ) (hρR : ENNReal.ofReal ρ < R₀) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖c n‖ ≤ M * ρ ^ (-(n : ℤ))) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖c (-(n : ℤ) - 1)‖ ≤ M * ρ ^ (n + 1)) := by
  have hρpos := hr₀.trans_lt hρ
  have hw : ‖(a + (ρ : ℂ)) - a‖ = ρ := by
    simp [Complex.norm_real, abs_of_pos hρpos]
  have hwA : a + (ρ : ℂ) ∈ annulus a r₀ R₀ := by
    refine ⟨by rw [hw]; exact hρ, ?_⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ‖(a + (ρ : ℂ)) - a‖ < R₀
    rw [hw]
    exact hρR
  obtain ⟨p, q, hp, hq, _⟩ := h _ hwA
  obtain ⟨P, hP, hp⟩ := exists_term_bound_of_partialSum_tendsto hp
  obtain ⟨Q, hQ, hq⟩ := exists_term_bound_of_partialSum_tendsto hq
  constructor
  · refine ⟨P, hP, fun n => ?_⟩
    have hn := hp n
    simp only [positiveTerm, norm_mul, norm_pow, hw] at hn
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos hρpos n)).mpr hn
  · refine ⟨Q, hQ, fun n => ?_⟩
    have hn := hq n
    have he : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    simp only [negativeTerm, norm_mul, norm_zpow, hw] at hn
    simp only [he, zpow_neg, zpow_natCast, ← div_eq_mul_inv] at hn
    simpa only [he] using (div_le_iff₀ (pow_pos hρpos (n + 1))).mp hn

/-- Ordinary convergent representations converge absolutely uniformly on every
strictly interior closed subannulus. -/
theorem exists_majorants_of_convergent {f : ℂ → ℂ} {c : ℤ → ℂ}
    {a : ℂ} {r₀ s t : ℝ} {R₀ : ℝ≥0∞} (hr₀ : 0 ≤ r₀)
    (h : ConvergentLaurentSeriesOn f a r₀ R₀ c)
    (hs : r₀ < s) (hst : s ≤ t) (ht : ENNReal.ofReal t < R₀) :
    (∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t →
      ‖positiveTerm c a n z‖ ≤ b n) ∧
    (∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t →
      ‖negativeTerm c a n z‖ ≤ b n) := by
  obtain ⟨ρ₁, hρ₁, hρ₁s⟩ := exists_between hs
  obtain ⟨ρ₂, htρ₂, hρ₂R⟩ := exists_admissible_radius ((hr₀.trans_lt hs).le.trans hst) ht
  have hρ₁R : ENNReal.ofReal ρ₁ < R₀ :=
    (ENNReal.ofReal_le_ofReal (hρ₁s.le.trans hst)).trans_lt ht
  obtain ⟨M₁, hM₁, hcneg⟩ := (coefficient_bounds_of_convergent hr₀ h hρ₁ hρ₁R).2
  obtain ⟨M₂, hM₂, hcpos⟩ :=
    (coefficient_bounds_of_convergent hr₀ h (hs.trans_le hst |>.trans htρ₂) hρ₂R).1
  exact exists_geometric_majorants_of_bounds c a s t ρ₁ ρ₂ M₁ M₂ (hr₀.trans_lt hs) hst
    (hr₀.trans_lt hρ₁) hρ₁s htρ₂ hM₁ hM₂ hcpos hcneg

/-- Absolute uniform convergence follows without assuming it of a competitor. -/
theorem normalConvergence_of_convergent {f : ℂ → ℂ} {c : ℤ → ℂ}
    {a : ℂ} {r₀ s t : ℝ} {R₀ : ℝ≥0∞} (hr₀ : 0 ≤ r₀)
    (h : ConvergentLaurentSeriesOn f a r₀ R₀ c)
    (hs : r₀ < s) (hst : s ≤ t) (ht : ENNReal.ofReal t < R₀) :
    AbsoluteUniformSeriesOn (positiveTerm c a) (closedSubannulus a s t) ∧
    AbsoluteUniformSeriesOn (negativeTerm c a) (closedSubannulus a s t) := by
  obtain ⟨⟨b, hb, hbp⟩, ⟨d, hd, hdn⟩⟩ := exists_majorants_of_convergent hr₀ h hs hst ht
  exact ⟨absoluteUniformSeriesOn_of_majorant hb hbp, absoluteUniformSeriesOn_of_majorant hd hdn⟩

/-- The unordered sums agree with the given ordinary limits after deriving
absolute convergence in the interior. -/
theorem hasLaurentSeriesOn_of_convergent {f : ℂ → ℂ} {c : ℤ → ℂ}
    {a : ℂ} {r₀ : ℝ} {R₀ : ℝ≥0∞} (hr₀ : 0 ≤ r₀)
    (h : ConvergentLaurentSeriesOn f a r₀ R₀ c) : HasLaurentSeriesOn f a r₀ R₀ c := by
  intro z hz
  have hzR : ENNReal.ofReal ‖z - a‖ < R₀ := by
    change ENNReal.ofReal (‖z - a‖₊ : ℝ) < R₀
    rw [ENNReal.ofReal_coe_nnreal]
    exact hz.2
  obtain ⟨hp, hn⟩ := normalConvergence_of_convergent hr₀ h hz.1 le_rfl hzR
  have hzK : z ∈ closedSubannulus a ‖z - a‖ ‖z - a‖ := ⟨le_rfl, le_rfl⟩
  have hsp := (hp.1 z hzK).of_norm
  have hsn := (hn.1 z hzK).of_norm
  obtain ⟨p, q, hpl, hql, heq⟩ := h z hz
  refine ⟨hsp, hsn, ?_⟩
  exact heq.trans (congrArg₂ (· + ·)
    (tendsto_nhds_unique hpl hsp.hasSum.tendsto_sum_nat)
    (tendsto_nhds_unique hql hsn.hasSum.tendsto_sum_nat))

/-- Continuity of every Laurent monomial on a positive circle. -/
theorem continuousOn_monomial_circle (a b : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (m : ℤ) :
    ContinuousOn (fun w : ℂ => b * (w - a) ^ m) (sphere a ρ) := by
  intro w hw
  have hw0 : w - a ≠ 0 := norm_ne_zero_iff.mp (by rw [mem_sphere_iff_norm.mp hw]; exact hρ.ne')
  exact (((differentiableAt_id.sub_const a).zpow (Or.inl hw0)).const_mul b).continuousAt.continuousWithinAt

/-- Coefficient extraction is linear in a constant multiplier. -/
theorem coefficientIntegral_const_mul (f : ℂ → ℂ) (a b : ℂ) (ρ : ℝ) (m : ℤ) :
    coefficientIntegral (fun w => b * f w) a ρ m = b * coefficientIntegral f a ρ m := by
  unfold coefficientIntegral
  simp_rw [mul_div_assoc]
  rw [circleIntegral.integral_const_mul]
  ring

/-- A summably majorized continuous series may be integrated against any fixed
integer Laurent kernel on a positive circle. -/
theorem hasSum_coefficientIntegral_of_majorant {u : ℕ → ℂ → ℂ}
    (a : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (m : ℤ) {b : ℕ → ℝ} (hb : Summable b)
    (hbound : ∀ n w, w ∈ sphere a ρ → ‖u n w‖ ≤ b n)
    (hc : ∀ n, ContinuousOn (u n) (sphere a ρ)) :
    HasSum (fun n => coefficientIntegral (u n) a ρ m)
      (coefficientIntegral (fun w => ∑' n, u n w) a ρ m) := by
  have hne : ∀ w ∈ sphere a ρ, (w - a) ^ (m + 1) ≠ 0 := by
    intro w hw
    apply zpow_ne_zero
    exact norm_ne_zero_iff.mp (by rw [mem_sphere_iff_norm.mp hw]; exact hρ.ne')
  have hi := hasSum_circleIntegral_of_majorant a ρ hρ.le
    (hb.div_const (ρ ^ (m + 1))) (u := fun n w => u n w / (w - a) ^ (m + 1))
    (g := fun w => (∑' n, u n w) / (w - a) ^ (m + 1))
    (by
      intro n w hw
      rw [norm_div, norm_zpow, mem_sphere_iff_norm.mp hw]
      exact div_le_div_of_nonneg_right (hbound n w hw) (zpow_pos hρ _).le)
    (fun n => (hc n).div (by
      simpa only [one_mul] using continuousOn_monomial_circle a 1 ρ hρ (m + 1)) hne)
    (by
      intro w hw
      exact (((hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbound n w hw)).of_norm).hasSum).div_const _)
  exact hi.mul_left (2 * Real.pi * Complex.I : ℂ)⁻¹

/-- A general ordinary convergent representation has the required coefficient
formula; normal convergence is derived before integrating it. -/
theorem coefficientFormula_of_convergent {f : ℂ → ℂ} {c : ℤ → ℂ}
    {a : ℂ} {r₀ ρ : ℝ} {R₀ : ℝ≥0∞} (hr₀ : 0 ≤ r₀)
    (h : ConvergentLaurentSeriesOn f a r₀ R₀ c)
    (hρ : r₀ < ρ) (hρR : ENNReal.ofReal ρ < R₀) (m : ℤ) :
    c m = coefficientIntegral f a ρ m := by
  have hρpos := hr₀.trans_lt hρ
  have hrep := hasLaurentSeriesOn_of_convergent hr₀ h
  obtain ⟨⟨bp, hbp, hp⟩, ⟨bn, hbn, hn⟩⟩ :=
    exists_majorants_of_convergent hr₀ h hρ le_rfl hρR
  have hK : sphere a ρ ⊆ closedSubannulus a ρ ρ := fun w hw =>
    ⟨(mem_sphere_iff_norm.mp hw).ge, (mem_sphere_iff_norm.mp hw).le⟩
  have hpc : ∀ n, ContinuousOn (positiveTerm c a n) (sphere a ρ) := by
    intro n
    change ContinuousOn (fun w => c n * (w - a) ^ n) _
    simpa only [zpow_natCast] using continuousOn_monomial_circle a (c n) ρ hρpos (n : ℤ)
  have hnc : ∀ n, ContinuousOn (negativeTerm c a n) (sphere a ρ) :=
    fun n => continuousOn_monomial_circle a (c (-(n : ℤ) - 1)) ρ hρpos _
  have hpint := hasSum_coefficientIntegral_of_majorant a ρ hρpos m hbp
    (fun n w hw => hp n w (hK hw)) hpc
  have hnint := hasSum_coefficientIntegral_of_majorant a ρ hρpos m hbn
    (fun n w hw => hn n w (hK hw)) hnc
  have hpt (n : ℕ) : coefficientIntegral (positiveTerm c a n) a ρ m =
      if (n : ℤ) = m then c m else 0 := by
    change coefficientIntegral (fun w => c n * (w - a) ^ n) a ρ m = _
    simp_rw [← zpow_natCast]
    rw [coefficientIntegral_const_mul, coefficientIntegral_monomial a ρ hρpos]
    split_ifs with he
    · simp [he]
    · simp
  have hnt (n : ℕ) : coefficientIntegral (negativeTerm c a n) a ρ m =
      if -(n : ℤ) - 1 = m then c m else 0 := by
    change coefficientIntegral (fun w => c (-(n : ℤ) - 1) * (w - a) ^ (-(n : ℤ) - 1)) a ρ m = _
    rw [coefficientIntegral_const_mul, coefficientIntegral_monomial a ρ hρpos]
    split_ifs with he
    · simp [he]
    · simp
  have hsum : coefficientIntegral (positivePart c a) a ρ m +
      coefficientIntegral (negativePart c a) a ρ m = c m := by
    cases m with
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast] at *
      have hpval : coefficientIntegral (positivePart c a) a ρ (j : ℤ) = c j := by
        apply hpint.unique
        simpa only [hpt, Int.natCast_inj] using hasSum_ite_eq j (c (j : ℤ))
      have hnval : coefficientIntegral (negativePart c a) a ρ (j : ℤ) = 0 := by
        apply hnint.unique
        convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
        funext n
        rw [hnt, ite_eq_right (by omega)]
      rw [hpval, hnval, add_zero]
    | negSucc j =>
      have hpval : coefficientIntegral (positivePart c a) a ρ (Int.negSucc j) = 0 := by
        apply hpint.unique
        convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
        funext n
        rw [hpt, ite_eq_right (by omega)]
      have hnval : coefficientIntegral (negativePart c a) a ρ (Int.negSucc j) = c (Int.negSucc j) := by
        apply hnint.unique
        convert hasSum_ite_eq j (c (Int.negSucc j)) using 1
        funext n
        rw [hnt]
        simp only [Int.negSucc_eq]
        simp only [show (- (n : ℤ) - 1 = -((j : ℤ) + 1)) ↔ n = j by omega]
      rw [hpval, hnval, zero_add]
  rw [← hsum]
  unfold coefficientIntegral
  rw [← mul_add]
  congr 1
  have hcpos : ContinuousOn (positivePart c a) (sphere a ρ) :=
    ((absoluteUniformSeriesOn_of_majorant hbp (fun n w hw => hp n w (hK hw))).2.1).continuousOn
      (Eventually.of_forall (fun N => continuousOn_finsetSum (Finset.range N) (fun n _ => hpc n))).frequently
  have hcneg : ContinuousOn (negativePart c a) (sphere a ρ) :=
    ((absoluteUniformSeriesOn_of_majorant hbn (fun n w hw => hn n w (hK hw))).2.1).continuousOn
      (Eventually.of_forall (fun N => continuousOn_finsetSum (Finset.range N) (fun n _ => hnc n))).frequently
  have hkernel : ContinuousOn (fun w : ℂ => ((w - a) ^ (m + 1))⁻¹) (sphere a ρ) := by
    simpa only [one_mul, zpow_neg] using continuousOn_monomial_circle a 1 ρ hρpos (-(m + 1))
  rw [← circleIntegral.integral_add (f := fun w => positivePart c a w / (w - a) ^ (m + 1))
    (g := fun w => negativePart c a w / (w - a) ^ (m + 1))
    (by
      simp only [div_eq_mul_inv]
      exact (hcpos.fun_mul hkernel).circleIntegrable hρpos.le)
    (by
      simp only [div_eq_mul_inv]
      exact (hcneg.fun_mul hkernel).circleIntegrable hρpos.le)]
  apply circleIntegral.integral_congr hρpos.le
  intro w hw
  dsimp only
  rw [← add_div, (hrep w (closedSubannulus_subset hρ hρR (hK hw))).2.2]

/-- All derivatives of a holomorphic scalar function remain holomorphic. -/
theorem differentiableOn_iteratedDeriv {U : Set ℂ} {g : ℂ → ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k g) U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

/-- A fixed disk radius works uniformly around a closed subannulus when its
radii lie strictly between those of a larger closed subannulus. -/
theorem exists_disk_radius_in_subannulus (a : ℂ) {s₁ s t t₁ : ℝ}
    (h₁ : s₁ < s) (h₂ : t < t₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ closedSubannulus a s t,
      closedBall z δ ⊆ closedSubannulus a s₁ t₁ := by
  let δ := min (s - s₁) (t₁ - t) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδs : δ ≤ s - s₁ := by
    have := min_le_left (s - s₁) (t₁ - t)
    dsimp [δ] at *
    linarith
  have hδt : δ ≤ t₁ - t := by
    have := min_le_right (s - s₁) (t₁ - t)
    dsimp [δ] at *
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro z hz w hw
  have hwδ := mem_closedBall_iff_norm.mp hw
  have ht : ‖w - a‖ ≤ ‖w - z‖ + ‖z - a‖ := by simpa only [dist_eq_norm] using dist_triangle w z a
  have hs : ‖z - a‖ ≤ ‖w - z‖ + ‖w - a‖ := by
    simpa only [norm_sub_rev z w] using (show ‖z - a‖ ≤ ‖z - w‖ + ‖w - a‖ by
      simpa only [dist_eq_norm] using dist_triangle z w a)
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- Cauchy's estimate transfers a summable majorant on larger subannuli to
summable majorants for every derivative order on smaller subannuli. -/
theorem exists_derivative_majorant {a : ℂ} {r₀ : ℝ} {R₀ : ℝ≥0∞}
    {u : ℕ → ℂ → ℂ}
    (hu : ∀ n, DifferentiableOn ℂ (u n) (annulus a r₀ R₀))
    (hm : ∀ s t : ℝ, r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ →
      ∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t → ‖u n z‖ ≤ b n)
    (hr₀ : 0 ≤ r₀) (s t : ℝ) (hs : r₀ < s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < R₀) (k : ℕ) :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t →
      ‖iteratedDeriv k (u n) z‖ ≤ b n := by
  obtain ⟨s₁, hs₁, hs₁s⟩ := exists_between hs
  obtain ⟨t₁, htt₁, ht₁R⟩ := exists_admissible_radius ((hr₀.trans_lt hs).le.trans hst) ht
  obtain ⟨δ, hδ, hδK⟩ := exists_disk_radius_in_subannulus a hs₁s htt₁
  obtain ⟨b, hb, hbound⟩ := hm s₁ t₁ hs₁ (hs₁s.le.trans (hst.trans htt₁.le)) ht₁R
  refine ⟨fun n => (k.factorial : ℝ) / δ ^ k * b n, hb.mul_left _, ?_⟩
  intro n z hz
  have hball : closedBall z δ ⊆ annulus a r₀ R₀ :=
    (hδK z hz).trans (closedSubannulus_subset hs₁ ht₁R)
  have hd : DiffContOnCl ℂ (u n) (ball z δ) :=
    ((hu n).mono (closure_ball_subset_closedBall.trans hball)).diffContOnCl
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hδ hd
    (fun w hw => hbound n w (hδK z hz (sphere_subset_closedBall hw)))
  convert hc using 1; ring

/-- Uniform convergence on all closed subannuli implies local uniform convergence
on the original open annulus, also for an infinite outer radius. -/
theorem locallyUniform_of_subannuli {a : ℂ} {r₀ : ℝ} {R₀ : ℝ≥0∞}
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hU : IsOpen (annulus a r₀ R₀))
    (h : ∀ s t : ℝ, r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ →
      TendstoUniformlyOn F g atTop (closedSubannulus a s t)) :
    TendstoLocallyUniformlyOn F g atTop (annulus a r₀ R₀) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn hne ((continuous_id.sub continuous_const).norm.continuousOn)
  obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn hne ((continuous_id.sub continuous_const).norm.continuousOn)
  have hqR : ENNReal.ofReal ‖q - a‖ < R₀ := by
    change ENNReal.ofReal (‖q - a‖₊ : ℝ) < R₀
    rw [ENNReal.ofReal_coe_nnreal]
    exact (hKU hq).2
  exact (h ‖p - a‖ ‖q - a‖ (hKU hp).1 (hpmin hq) hqR).mono
    (fun z hz => ⟨hpmin hz, hqmax hz⟩)

/-- Locally uniformly convergent holomorphic functions retain local uniform
convergence after any number of differentiations. -/
theorem locallyUniform_iteratedDeriv {U : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hU : IsOpen U) (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlim : TendstoLocallyUniformlyOn F g atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n)) (iteratedDeriv k g) atTop U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hlim
  | succ k ih =>
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      ih.deriv (Eventually.of_forall (fun n => differentiableOn_iteratedDeriv hU (hF n) k)) hU

/-- A normally convergent holomorphic series can be differentiated at every
order; summability is proved separately from the ordered limit identity. -/
theorem termwise_calculus_of_majorants {a : ℂ} {r₀ : ℝ} {R₀ : ℝ≥0∞}
    {u : ℕ → ℂ → ℂ} (hU : IsOpen (annulus a r₀ R₀)) (hr₀ : 0 ≤ r₀)
    (hu : ∀ n, DifferentiableOn ℂ (u n) (annulus a r₀ R₀))
    (hm : ∀ s t : ℝ, r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ →
      ∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t → ‖u n z‖ ≤ b n) :
    ∀ k : ℕ, ∀ z ∈ annulus a r₀ R₀,
      DifferentiableAt ℂ (iteratedDeriv k (fun w => ∑' n, u n w)) z ∧
      Summable (fun n => iteratedDeriv k (u n) z) ∧
      iteratedDeriv k (fun w => ∑' n, u n w) z = ∑' n, iteratedDeriv k (u n) z := by
  have hlim : TendstoLocallyUniformlyOn (fun N w => ∑ n ∈ Finset.range N, u n w)
      (fun w => ∑' n, u n w) atTop (annulus a r₀ R₀) := by
    apply locallyUniform_of_subannuli hU
    intro s t hs hst ht
    obtain ⟨b, hb, hbound⟩ := hm s t hs hst ht
    exact tendstoUniformlyOn_tsum_nat hb hbound
  have hpartial (N : ℕ) : DifferentiableOn ℂ (fun w => ∑ n ∈ Finset.range N, u n w)
      (annulus a r₀ R₀) := DifferentiableOn.fun_sum (fun n _ => hu n)
  have hsumdiff := hlim.differentiableOn (Eventually.of_forall hpartial) hU
  intro k z hz
  have hzR : ENNReal.ofReal ‖z - a‖ < R₀ := by
    change ENNReal.ofReal (‖z - a‖₊ : ℝ) < R₀
    rw [ENNReal.ofReal_coe_nnreal]
    exact hz.2
  obtain ⟨b, hb, hbound⟩ := exists_derivative_majorant hu hm hr₀ ‖z - a‖ ‖z - a‖ hz.1 le_rfl hzR k
  have habs : Summable (fun n => ‖iteratedDeriv k (u n) z‖) :=
    hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbound n z ⟨le_rfl, le_rfl⟩)
  refine ⟨(differentiableOn_iteratedDeriv hU hsumdiff k).differentiableAt (hU.mem_nhds hz),
    habs.of_norm, ?_⟩
  symm
  apply HasSum.tsum_eq
  apply (hasSum_iff_tendsto_nat_of_summable_norm habs).mpr
  have hk := (locallyUniform_iteratedDeriv hU hpartial hlim k).tendsto_at hz
  convert hk using 1
  funext N
  exact (iteratedDeriv_fun_sum (fun n _ => (hu n).contDiffOn hU |>.contDiffAt (hU.mem_nhds hz))).symm

/-- Coefficient extraction proves uniqueness without extra assumptions on the
convergence of the competing representation. -/
theorem laurent_unique : Specs.D12Complex.Ch07.Laurent.laurent_unique_type := by
  intro a r₀ R₀ f c d hr₀ hR hc hd
  obtain ⟨ρ, hρ, hρR⟩ := exists_admissible_radius hr₀ hR
  funext m
  exact (coefficientFormula_of_convergent hr₀ hc hρ hρR m).trans
    (coefficientFormula_of_convergent hr₀ hd hρ hρR m).symm

theorem laurent_calculus : Specs.D12Complex.Ch07.Laurent.laurent_calculus_type := by
  intro a r₀ R₀ f c hr₀ hf h
  have hrep := hasLaurentSeriesOn_of_convergent hr₀ h
  have hup (n : ℕ) : DifferentiableOn ℂ (positiveTerm c a n) (annulus a r₀ R₀) := by
    intro z hz
    exact (((differentiableAt_id.sub_const a).pow n).const_mul (c n)).differentiableWithinAt
  have hun (n : ℕ) : DifferentiableOn ℂ (negativeTerm c a n) (annulus a r₀ R₀) := by
    intro z hz
    exact (((differentiableAt_id.sub_const a).zpow
      (Or.inl (sub_ne_zero_of_mem_annulus hr₀ hz))).const_mul (c (-(n : ℤ) - 1))).differentiableWithinAt
  have hmp : ∀ s t : ℝ, r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ →
      ∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t → ‖positiveTerm c a n z‖ ≤ b n :=
    fun s t hs hst ht => (exists_majorants_of_convergent hr₀ h hs hst ht).1
  have hmn : ∀ s t : ℝ, r₀ < s → s ≤ t → ENNReal.ofReal t < R₀ →
      ∃ b : ℕ → ℝ, Summable b ∧ ∀ n z, z ∈ closedSubannulus a s t → ‖negativeTerm c a n z‖ ≤ b n :=
    fun s t hs hst ht => (exists_majorants_of_convergent hr₀ h hs hst ht).2
  have hp := termwise_calculus_of_majorants hf.1 hr₀ hup hmp
  have hn := termwise_calculus_of_majorants hf.1 hr₀ hun hmn
  have hpd : DifferentiableOn ℂ (positivePart c a) (annulus a r₀ R₀) :=
    fun z hz => (hp 0 z hz).1.differentiableWithinAt
  have hnd : DifferentiableOn ℂ (negativePart c a) (annulus a r₀ R₀) :=
    fun z hz => (hn 0 z hz).1.differentiableWithinAt
  constructor
  · intro k z hz
    obtain ⟨hpdiff, hpsum, hpeq⟩ := hp k z hz
    obtain ⟨hndiff, hnsum, hneq⟩ := hn k z hz
    refine ⟨hpdiff, hndiff,
      (differentiableOn_iteratedDeriv hf.1 (fun w hw => (hf.2 w hw).differentiableWithinAt) k).differentiableAt
        (hf.1.mem_nhds hz), hpsum, hnsum, hpeq, hneq, ?_⟩
    have heq : f =ᶠ[𝓝 z] (fun w => positivePart c a w + negativePart c a w) := by
      filter_upwards [hf.1.mem_nhds hz] with w hw
      exact (hrep w hw).2.2
    rw [heq.iteratedDeriv_eq k]
    change iteratedDeriv k (fun w => positivePart c a w + negativePart c a w) z =
      (∑' n, iteratedDeriv k (positiveTerm c a n) z) +
      (∑' n, iteratedDeriv k (negativeTerm c a n) z)
    have hadd := iteratedDeriv_fun_add (n := k)
      (hpd.contDiffOn hf.1 |>.contDiffAt (hf.1.mem_nhds hz))
      (hnd.contDiffOn hf.1 |>.contDiffAt (hf.1.mem_nhds hz))
    exact hadd.trans (congrArg₂ (· + ·) hpeq hneq)
  · intro s t hs hst ht k
    obtain ⟨bp, hbp, hpbound⟩ := exists_derivative_majorant hup hmp hr₀ s t hs hst ht k
    obtain ⟨bn, hbn, hnbound⟩ := exists_derivative_majorant hun hmn hr₀ s t hs hst ht k
    exact ⟨absoluteUniformSeriesOn_of_majorant hbp hpbound,
      absoluteUniformSeriesOn_of_majorant hbn hnbound⟩

/-- The full Laurent theorem on an annulus with possibly infinite outer radius. -/
theorem laurent_expansion : Specs.D12Complex.Ch07.Laurent.laurent_expansion_type := by
  intro a r₀ R₀ f hr₀ hR hf
  obtain ⟨c, hc, hcoeff, _⟩ := laurent_exists a r₀ R₀ f hr₀ hR hf
  have hconv := convergent_of_hasLaurentSeriesOn hc
  obtain ⟨hcalc, hnormal⟩ := laurent_calculus a r₀ R₀ f c hr₀ hf hconv
  exact ⟨c, hc, fun d hd => laurent_unique a r₀ R₀ f d c hr₀ hR hd hconv,
    hcoeff, hcalc, hnormal⟩

end D12Complex.Laurent

/-! Candidate-owned exports of the independent canonical definitions. -/
namespace D12Complex.Laurent.Definitions
abbrev annulus : Specs.D12Complex.Ch07.Laurent.annulus_type :=
  _root_.D12Complex.Laurent.annulus

abbrev closedSubannulus : Specs.D12Complex.Ch07.Laurent.closedSubannulus_type :=
  _root_.D12Complex.Laurent.closedSubannulus

abbrev coefficientIntegral : Specs.D12Complex.Ch07.Laurent.coefficientIntegral_type :=
  _root_.D12Complex.Laurent.coefficientIntegral

abbrev positiveTerm : Specs.D12Complex.Ch07.Laurent.positiveTerm_type :=
  _root_.D12Complex.Laurent.positiveTerm

abbrev negativeTerm : Specs.D12Complex.Ch07.Laurent.negativeTerm_type :=
  _root_.D12Complex.Laurent.negativeTerm

abbrev positivePart : Specs.D12Complex.Ch07.Laurent.positivePart_type :=
  _root_.D12Complex.Laurent.positivePart

abbrev negativePart : Specs.D12Complex.Ch07.Laurent.negativePart_type :=
  _root_.D12Complex.Laurent.negativePart

abbrev HasLaurentSeriesOn : Specs.D12Complex.Ch07.Laurent.HasLaurentSeriesOn_type :=
  _root_.D12Complex.Laurent.HasLaurentSeriesOn

abbrev ConvergentLaurentSeriesOn : Specs.D12Complex.Ch07.Laurent.ConvergentLaurentSeriesOn_type :=
  _root_.D12Complex.Laurent.ConvergentLaurentSeriesOn

abbrev AbsoluteUniformSeriesOn : Specs.D12Complex.Ch07.Laurent.AbsoluteUniformSeriesOn_type :=
  _root_.D12Complex.Laurent.AbsoluteUniformSeriesOn

abbrev derivativePositiveTerm : Specs.D12Complex.Ch07.Laurent.derivativePositiveTerm_type :=
  _root_.D12Complex.Laurent.derivativePositiveTerm

abbrev derivativeNegativeTerm : Specs.D12Complex.Ch07.Laurent.derivativeNegativeTerm_type :=
  _root_.D12Complex.Laurent.derivativeNegativeTerm

abbrev TermwiseDerivativesOn : Specs.D12Complex.Ch07.Laurent.TermwiseDerivativesOn_type :=
  _root_.D12Complex.Laurent.TermwiseDerivativesOn

end D12Complex.Laurent.Definitions
