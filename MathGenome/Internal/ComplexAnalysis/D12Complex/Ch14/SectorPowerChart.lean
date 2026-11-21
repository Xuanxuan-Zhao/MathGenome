import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SectorPowerChart
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.ChosenPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite

/-!
Selected powers straighten the canonical counterclockwise sector, for all
angles strictly between zero and 2π. The polar calculations keep the centered
arguments inside the principal slit and do not use a general power-of-product
rule. Continuity of the inverse at zero follows from the positive real power.

The real differential norm is obtained by restricting the complex differential
and preserving its operator norm. Closed upper-half-plane points are limits of
interior points; the extended inverse law then identifies the diameter with the
sector frontier. No harmonic regularity or decay assertion is used.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace D12Complex.SectorPowerChart

/-- Implementation-owned representative of the canonical selected power map.
The canonical definition stays in the independent Spec for downstream statements. -/
abbrev powerMap : Specs.D12Complex.Ch14.SectorPowerChart.P_type := P

/-- Implementation-owned representative of the canonical inverse power map. -/
abbrev inverseMap : Specs.D12Complex.Ch14.SectorPowerChart.Q_type := Q

lemma principalPower_eq_cpow (a z : ℂ) (hz : z ≠ 0) :
    principalPower a z = z ^ a := by
  change E (a * Complex.log z) = z ^ a
  rw [Exponential.E_eq_exp, Complex.cpow_def_of_ne_zero hz, mul_comm]

lemma norm_principalPower_real (a : ℝ) (z : ℂ) (hz : z ≠ 0) :
    ‖principalPower (a : ℂ) z‖ = ‖z‖ ^ a := by
  rw [principalPower_eq_cpow _ _ hz, Complex.norm_cpow_real]

lemma norm_rotation (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp]

theorem zero_values : Specs.D12Complex.Ch14.SectorPowerChart.zero_values_type := by
  intro θ
  simp [P, Q]

theorem power_norm : Specs.D12Complex.Ch14.SectorPowerChart.power_norm_type := by
  intro θ hθ z
  by_cases hz : z = 0
  · simp [P, hz, Real.zero_rpow (div_pos Real.pi_pos hθ).ne']
  · rw [P, ite_eq_right hz, norm_mul, Complex.norm_I, one_mul,
      norm_principalPower_real _ _ (mul_ne_zero (Complex.exp_ne_zero _) hz), norm_mul]
    simp [Complex.norm_exp]

theorem inverse_norm : Specs.D12Complex.Ch14.SectorPowerChart.inverse_norm_type := by
  intro θ hθ w
  by_cases hw : w = 0
  · simp [Q, hw, Real.zero_rpow (div_pos hθ Real.pi_pos).ne']
  · rw [Q, ite_eq_right hw, norm_mul, norm_rotation, one_mul,
      norm_principalPower_real _ _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw),
      norm_mul]
    simp

/-- Polar formulas are used only in the indicated principal-log interval. -/
lemma log_polar (ρ t : ℝ) (hρ : 0 < ρ) (ht : -Real.pi < t) (ht' : t ≤ Real.pi) :
    Complex.log ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      (Real.log ρ : ℂ) + (t : ℂ) * Complex.I := by
  have he : (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) =
      Complex.exp ((Real.log ρ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ]
  rw [he, Complex.log_exp] <;> simpa using ‹_›

lemma principalPower_polar (a ρ t : ℝ) (hρ : 0 < ρ)
    (ht : -Real.pi < t) (ht' : t ≤ Real.pi) :
    principalPower (a : ℂ) ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      (ρ ^ a : ℝ) * Complex.exp (((a * t : ℝ) : ℂ) * Complex.I) := by
  change E ((a : ℂ) * Complex.log _) = _
  rw [Exponential.E_eq_exp, log_polar ρ t hρ ht ht']
  rw [show (a : ℂ) * ((Real.log ρ : ℂ) + (t : ℂ) * Complex.I) =
    ((Real.log ρ * a : ℝ) : ℂ) + ((a*t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.rpow_def_of_pos hρ]

lemma rotate_polar (c ρ t : ℝ) :
    Complex.exp ((c : ℂ) * Complex.I) *
      ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      (ρ : ℂ) * Complex.exp (((t+c : ℝ) : ℂ) * Complex.I) := by
  rw [show ((t+c : ℝ) : ℂ) * Complex.I =
    (c : ℂ) * Complex.I + (t : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]
  ring

lemma polar_ne_zero (ρ t : ℝ) (hρ : 0 < ρ) :
    (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') (Complex.exp_ne_zero _)

lemma P_polar (θ ρ t : ℝ) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (ht' : t ≤ θ) :
    P θ ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      (ρ ^ (Real.pi / θ) : ℝ) *
        Complex.exp (((Real.pi / θ * t : ℝ) : ℂ) * Complex.I) := by
  rw [P, ite_eq_right (polar_ne_zero ρ t hρ)]
  have hrot : -((θ / 2 : ℝ) : ℂ) * Complex.I =
      ((-(θ/2) : ℝ) : ℂ) * Complex.I := by push_cast; rfl
  rw [hrot, rotate_polar, principalPower_polar]
  · have hi : Complex.I = Complex.exp (((Real.pi/2 : ℝ) : ℂ) * Complex.I) := by
      simp
    nth_rw 1 [hi]
    rw [rotate_polar]
    have he : Real.pi / θ * (t + -(θ/2)) + Real.pi/2 = Real.pi / θ * t := by
      field_simp
      ring
    rw [he]
  · exact hρ
  · linarith
  · linarith

lemma Q_polar (θ ρ t : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (ht' : t ≤ Real.pi) :
    Q θ ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      (ρ ^ (θ / Real.pi) : ℝ) *
        Complex.exp (((θ / Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  rw [Q, ite_eq_right (polar_ne_zero ρ t hρ)]
  have hi : -Complex.I = Complex.exp (((-(Real.pi/2) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]
    have he : Complex.exp (((Real.pi/2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
      simp
    rw [he]
    simp
  rw [hi, rotate_polar, principalPower_polar]
  · rw [rotate_polar]
    have he : θ / Real.pi * (t + -(Real.pi/2)) + θ/2 = θ / Real.pi * t := by
      field_simp
      ring
    rw [he]
  · exact hρ
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

lemma sector_ne_zero {θ : ℝ} {z : ℂ} (hz : z ∈ CircularExhaustion.sector θ) : z ≠ 0 := by
  obtain ⟨ρ, t, hρ, ht, ht', rfl⟩ := hz
  exact polar_ne_zero ρ t hρ

lemma arg_polar (ρ t : ℝ) (hρ : 0 < ρ) (ht : -Real.pi < t) (ht' : t ≤ Real.pi) :
    (((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I))).arg = t := by
  have h := congrArg Complex.im (log_polar ρ t hρ ht ht')
  simpa [Complex.log_im] using h

lemma centered_polar (θ ρ t : ℝ) :
    Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) *
      ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      (ρ : ℂ) * Complex.exp (((t-θ/2 : ℝ) : ℂ) * Complex.I) := by
  simpa only [Complex.ofReal_neg, sub_eq_add_neg] using rotate_polar (-(θ/2)) ρ t

lemma centered_branch {θ : ℝ} (_hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    {z : ℂ} (hz : z ∈ CircularExhaustion.sector θ) :
    let v := Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * z
    v ∈ PrincipalSlitPlane ∧ -(θ / 2) < v.arg ∧ v.arg < θ / 2 := by
  obtain ⟨ρ, t, hρ, ht, ht', rfl⟩ := hz
  dsimp
  rw [centered_polar]
  have ha := arg_polar ρ (t-θ/2) hρ (by linarith) (by linarith)
  refine ⟨?_, by rw [ha]; linarith, by rw [ha]; linarith⟩
  rw [PrincipalLogarithm.principalSlitPlane_eq_slitPlane, Complex.mem_slitPlane_iff_arg]
  exact ⟨by rw [ha]; linarith, polar_ne_zero _ _ hρ⟩

lemma right_branch {w : ℂ} (hw : 0 ≤ w.im) (hw0 : w ≠ 0) :
    -Complex.I * w ∈ PrincipalSlitPlane ∧
      -(Real.pi / 2) ≤ (-Complex.I * w).arg ∧
      (-Complex.I * w).arg ≤ Real.pi / 2 := by
  have hr : 0 ≤ (-Complex.I * w).re := by simpa using hw
  have hn : -Complex.I * w ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw0
  refine ⟨?_, (abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hr)).1,
    (abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hr)).2⟩
  rw [PrincipalLogarithm.mem_principalSlitPlane_iff]
  rcases lt_or_eq_of_le hr with h | h
  · exact Or.inl h
  · right
    intro hi
    exact hn (Complex.ext h.symm hi)

theorem branch_domains : Specs.D12Complex.Ch14.SectorPowerChart.branch_domains_type := by
  intro θ hθ hθ'
  exact ⟨fun _ hz => centered_branch hθ hθ' hz, fun _ hw hw0 => right_branch hw hw0⟩

lemma sector_iff_centered {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) (z : ℂ) :
    z ∈ CircularExhaustion.sector θ ↔
    let v := Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * z
    v ∈ PrincipalSlitPlane ∧ -(θ/2) < v.arg ∧ v.arg < θ/2 := by
  constructor
  · exact centered_branch hθ hθ'
  · dsimp
    intro hz
    let v := Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * z
    have hv : v ≠ 0 := PrincipalLogarithm.principalSlitPlane_ne_zero _ hz.1
    refine ⟨‖v‖, v.arg + θ/2, norm_pos_iff.mpr hv, by dsimp [v]; linarith [hz.2.1],
      by dsimp [v]; linarith [hz.2.2], ?_⟩
    have he : Complex.exp (((θ/2 : ℝ) : ℂ) * Complex.I) * v = z := by
      dsimp [v]
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    rw [← rotate_polar, Complex.norm_mul_exp_arg_mul_I, he]

lemma isOpen_sector {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    IsOpen (CircularExhaustion.sector θ) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hb := centered_branch hθ hθ' hz
  let f : ℂ → ℂ := fun z => Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * z
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hslit : f z ∈ Complex.slitPlane := by
    rw [← PrincipalLogarithm.principalSlitPlane_eq_slitPlane]
    exact hb.1
  have ha := (Complex.continuousAt_arg hslit).comp hc.continuousAt
  have he : ∀ᶠ w in 𝓝 z, f w ∈ PrincipalSlitPlane ∧
      -(θ/2) < (f w).arg ∧ (f w).arg < θ/2 :=
    (hc.continuousAt.eventually (PrincipalLogarithm.isOpen_principalSlitPlane.mem_nhds hb.1)).and
      (ha.eventually (Ioo_mem_nhds hb.2.1 hb.2.2))
  exact mem_of_superset he (fun w hw => (sector_iff_centered hθ hθ' w).mpr hw)

lemma upper_polar {w : ℂ} (hw : 0 ≤ w.im) (hw0 : w ≠ 0) :
    ∃ ρ t : ℝ, 0 < ρ ∧ 0 ≤ t ∧ t ≤ Real.pi ∧
      w = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  exact ⟨‖w‖, w.arg, norm_pos_iff.mpr hw0, Complex.arg_nonneg_iff.mpr hw,
    Complex.arg_le_pi _, (Complex.norm_mul_exp_arg_mul_I w).symm⟩

lemma upper_polar_strict {w : ℂ} (hw : 0 < w.im) :
    ∃ ρ t : ℝ, 0 < ρ ∧ 0 < t ∧ t < Real.pi ∧
      w = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  refine ⟨‖w‖, w.arg, norm_pos_iff.mpr hw0, ?_,
    Complex.arg_lt_pi_iff.mpr (Or.inr hw.ne'), (Complex.norm_mul_exp_arg_mul_I w).symm⟩
  have ha : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hw.le
  rcases eq_or_lt_of_le ha with h | h
  · have hi := Complex.norm_mul_sin_arg w
    rw [← h, Real.sin_zero, mul_zero] at hi
    linarith
  · exact h

lemma im_polar_pos {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (ht' : t < Real.pi) :
    0 < ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)).im := by
  rw [Complex.exp_mul_I]
  simpa [← Complex.ofReal_sin, ← Complex.ofReal_cos] using
    mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi ht ht')

lemma P_im_pos {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    {z : ℂ} (hz : z ∈ CircularExhaustion.sector θ) : 0 < (P θ z).im := by
  obtain ⟨ρ, t, hρ, ht, ht', rfl⟩ := hz
  rw [P_polar θ ρ t hθ hθ' hρ ht.le ht'.le]
  apply im_polar_pos (Real.rpow_pos_of_pos hρ _)
  · exact mul_pos (div_pos Real.pi_pos hθ) ht
  · have he : Real.pi / θ * θ = Real.pi := div_mul_cancel₀ _ hθ.ne'
    nlinarith [mul_lt_mul_of_pos_left ht' (div_pos Real.pi_pos hθ)]

lemma Q_mem_sector {θ : ℝ} (hθ : 0 < θ) {w : ℂ} (hw : 0 < w.im) :
    Q θ w ∈ CircularExhaustion.sector θ := by
  obtain ⟨ρ, t, hρ, ht, ht', rfl⟩ := upper_polar_strict hw
  rw [Q_polar θ ρ t hρ ht.le ht'.le]
  refine ⟨ρ ^ (θ/Real.pi), θ/Real.pi*t, Real.rpow_pos_of_pos hρ _,
    mul_pos (div_pos hθ Real.pi_pos) ht, ?_, rfl⟩
  have he : θ / Real.pi * Real.pi = θ := div_mul_cancel₀ _ Real.pi_ne_zero
  nlinarith [mul_lt_mul_of_pos_left ht' (div_pos hθ Real.pi_pos)]

lemma Q_P {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    {z : ℂ} (hz : z ∈ CircularExhaustion.sector θ) : Q θ (P θ z) = z := by
  obtain ⟨ρ, t, hρ, ht, ht', rfl⟩ := hz
  rw [P_polar θ ρ t hθ hθ' hρ ht.le ht'.le]
  rw [Q_polar θ _ _ (Real.rpow_pos_of_pos hρ _) (by positivity) (by
    nlinarith [mul_le_mul_of_nonneg_left ht'.le (div_pos Real.pi_pos hθ).le,
      div_mul_cancel₀ Real.pi hθ.ne'])]
  have hab : Real.pi / θ * (θ/Real.pi) = 1 := by field_simp
  have hba : θ/Real.pi * (Real.pi / θ) = 1 := by rw [mul_comm]; exact hab
  rw [← Real.rpow_mul hρ.le, hab, Real.rpow_one, ← mul_assoc, hba, one_mul]

lemma P_Q {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    {w : ℂ} (hw : 0 < w.im) : P θ (Q θ w) = w := by
  obtain ⟨ρ, t, hρ, ht, ht', rfl⟩ := upper_polar_strict hw
  rw [Q_polar θ ρ t hρ ht.le ht'.le]
  rw [P_polar θ _ _ hθ hθ' (Real.rpow_pos_of_pos hρ _) (by positivity) (by
    nlinarith [mul_le_mul_of_nonneg_left ht'.le (div_pos hθ Real.pi_pos).le,
      div_mul_cancel₀ θ Real.pi_ne_zero])]
  have hab : Real.pi / θ * (θ/Real.pi) = 1 := by field_simp
  have hba : θ/Real.pi * (Real.pi / θ) = 1 := by rw [mul_comm]; exact hab
  rw [← Real.rpow_mul hρ.le, hba, Real.rpow_one, ← mul_assoc, hab, one_mul]

lemma hasDerivAt_P {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    {z : ℂ} (hz : z ∈ CircularExhaustion.sector θ) :
    HasDerivAt (P θ)
      (Complex.I * ((((Real.pi / θ : ℝ) : ℂ) *
        principalPower (((Real.pi / θ : ℝ) : ℂ) - 1)
          (Complex.exp (-((θ/2 : ℝ) : ℂ) * Complex.I) * z)) *
          Complex.exp (-((θ/2 : ℝ) : ℂ) * Complex.I))) z := by
  have hd := (ChosenPowers.hasDerivAt_principalPower ((Real.pi/θ : ℝ) : ℂ) _ (centered_branch hθ hθ' hz).1).comp z
    ((hasDerivAt_id z).const_mul (Complex.exp (-((θ/2 : ℝ) : ℂ) * Complex.I)))
  apply HasDerivAt.congr_of_eventuallyEq (by simpa only [mul_one] using hd.const_mul Complex.I)
  filter_upwards [eventually_ne_nhds (sector_ne_zero hz)] with w hw
  simp [P, hw]

lemma hasDerivAt_Q {θ : ℝ} {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (Q θ)
      (Complex.exp (((θ/2 : ℝ) : ℂ) * Complex.I) *
        (((θ/Real.pi : ℝ) : ℂ) * principalPower (((θ/Real.pi : ℝ) : ℂ) - 1)
          (-Complex.I * w) * -Complex.I)) w := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hd := (ChosenPowers.hasDerivAt_principalPower ((θ/Real.pi : ℝ) : ℂ) _ (right_branch hw.le hw0).1).comp w
    ((hasDerivAt_id w).const_mul (-Complex.I))
  apply HasDerivAt.congr_of_eventuallyEq (by
    simpa only [mul_one] using hd.const_mul (Complex.exp (((θ/2 : ℝ) : ℂ) * Complex.I)))
  filter_upwards [eventually_ne_nhds hw0] with z hz
  simp [Q, hz]

theorem differential_norm : Specs.D12Complex.Ch14.SectorPowerChart.differential_norm_type := by
  intro θ hθ hθ' z hz
  have hd := hasDerivAt_P hθ hθ' hz
  rw [hd.differentiableAt.fderiv_restrictScalars ℝ,
    ContinuousLinearMap.norm_restrictScalars, ← norm_deriv_eq_norm_fderiv, hd.deriv]
  have hcast : ((Real.pi / θ : ℝ) : ℂ) - 1 = (((Real.pi/θ-1 : ℝ)) : ℂ) := by push_cast; rfl
  rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_mul, hcast,
    norm_principalPower_real _ _ (mul_ne_zero (Complex.exp_ne_zero _) (sector_ne_zero hz)),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos Real.pi_pos hθ)]
  simp [Complex.norm_exp]

lemma norm_Q_lt {θ R : ℝ} (hθ : 0 < θ) (hR : 0 < R) {w : ℂ}
    (hw : ‖w‖ < R ^ (Real.pi/θ)) : ‖Q θ w‖ < R := by
  rw [inverse_norm θ hθ]
  have h := Real.rpow_lt_rpow (norm_nonneg w) hw (div_pos hθ Real.pi_pos)
  have he : Real.pi / θ * (θ/Real.pi) = 1 := by field_simp
  rwa [← Real.rpow_mul hR.le, he, Real.rpow_one] at h

theorem biholomorphic : Specs.D12Complex.Ch14.SectorPowerChart.biholomorphic_type := by
  intro θ R hθ hθ' hR
  refine ⟨⟨(isOpen_sector hθ hθ').inter isOpen_ball, fun z hz =>
    (hasDerivAt_P hθ hθ' hz.1).differentiableAt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im), fun w hw => ?_⟩
    exact (hasDerivAt_Q hw.2).differentiableAt
  · intro z hz
    refine ⟨?_, P_im_pos hθ hθ' hz.1⟩
    rw [power_norm θ hθ]
    exact Real.rpow_lt_rpow (norm_nonneg _) (by simpa using hz.2) (div_pos Real.pi_pos hθ)
  · intro w hw
    exact ⟨Q_mem_sector hθ hw.2, by simpa using norm_Q_lt hθ hR hw.1⟩
  · intro z hz
    exact Q_P hθ hθ' hz.1
  · intro w hw
    exact P_Q hθ hθ' hw.2

lemma Q_eq_cpow {θ : ℝ} (hθ : 0 < θ) (w : ℂ) :
    Q θ w = Complex.exp (((θ/2 : ℝ) : ℂ) * Complex.I) *
      (-Complex.I * w) ^ ((θ/Real.pi : ℝ) : ℂ) := by
  by_cases hw : w = 0
  · simp [Q, hw, hθ.ne']
  · rw [Q, ite_eq_right hw, principalPower_eq_cpow _ _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw)]

lemma continuousAt_Q {θ : ℝ} (hθ : 0 < θ) {w : ℂ} (hw : 0 ≤ w.im) :
    ContinuousAt (Q θ) w := by
  have hc := Complex.continuousAt_cpow_const_of_re_pos
    (z := -Complex.I*w) (w := ((θ/Real.pi : ℝ) : ℂ))
    (Or.inl (by simpa using hw)) (by simpa using div_pos hθ Real.pi_pos)
  have hd := (hc.comp (continuousAt_const.mul continuousAt_id)).const_mul
    (Complex.exp (((θ/2 : ℝ) : ℂ) * Complex.I))
  have he := funext (Q_eq_cpow hθ)
  rw [he]
  exact hd

theorem inverse_continuous : Specs.D12Complex.Ch14.SectorPowerChart.inverse_continuous_type := by
  intro θ R hθ _ _ w hw
  exact (continuousAt_Q hθ hw.2).continuousWithinAt

lemma P_Q_closed {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    {w : ℂ} (hw : 0 ≤ w.im) : P θ (Q θ w) = w := by
  by_cases hw0 : w = 0
  · simp [hw0, P, Q]
  obtain ⟨ρ, t, hρ, ht, ht', rfl⟩ := upper_polar hw hw0
  rw [Q_polar θ ρ t hρ ht ht']
  rw [P_polar θ _ _ hθ hθ' (Real.rpow_pos_of_pos hρ _) (by positivity) (by
    nlinarith [mul_le_mul_of_nonneg_left ht' (div_pos hθ Real.pi_pos).le,
      div_mul_cancel₀ θ Real.pi_ne_zero])]
  have hab : Real.pi / θ * (θ/Real.pi) = 1 := by field_simp
  have hba : θ/Real.pi * (Real.pi / θ) = 1 := by rw [mul_comm]; exact hab
  rw [← Real.rpow_mul hρ.le, hba, Real.rpow_one, ← mul_assoc, hab, one_mul]

lemma upper_mem_closure {w : ℂ} (hw : 0 ≤ w.im) :
    w ∈ closure {z : ℂ | 0 < z.im} := by
  let f : ℝ → ℂ := fun t => w + (t : ℂ) * Complex.I
  have hc : Continuous f := by dsimp [f]; fun_prop
  have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by simpa only [closure_Ioi, mem_Ici] using (le_refl (0 : ℝ))
  have hm := mem_closure_image hc.continuousAt h0
  have hs : f '' Ioi (0 : ℝ) ⊆ {z : ℂ | 0 < z.im} := by
    rintro _ ⟨t, ht, rfl⟩
    dsimp [f]
    simpa using add_pos_of_nonneg_of_pos hw ht
  simpa [f] using closure_mono hs hm

lemma Q_mem_closure {θ : ℝ} (hθ : 0 < θ) {w : ℂ} (hw : 0 ≤ w.im) :
    Q θ w ∈ closure (CircularExhaustion.sector θ) := by
  apply closure_mono (s := Q θ '' {z : ℂ | 0 < z.im}) ?_
    (mem_closure_image (continuousAt_Q hθ hw) (upper_mem_closure hw))
  rintro _ ⟨v, hv, rfl⟩
  exact Q_mem_sector hθ hv

theorem inverse_mapsTo_closure :
    Specs.D12Complex.Ch14.SectorPowerChart.inverse_mapsTo_closure_type := by
  intro θ R hθ _ hR w hw
  exact ⟨Q_mem_closure hθ hw.2, by simpa using norm_Q_lt hθ hR hw.1⟩

theorem diameter_frontier : Specs.D12Complex.Ch14.SectorPowerChart.diameter_frontier_type := by
  intro θ R hθ hθ' _ w hw _
  rw [frontier, (isOpen_sector hθ hθ').interior_eq]
  refine ⟨Q_mem_closure hθ hw.ge, ?_⟩
  intro hz
  have hp := P_im_pos hθ hθ' hz
  rw [P_Q_closed hθ hθ' hw.ge, hw] at hp
  exact lt_irrefl _ hp

/-- The inverse laws are available without choosing a truncation radius. -/
theorem inverse_laws : Specs.D12Complex.Ch14.SectorPowerChart.inverse_laws_type := by
  intro θ hθ hθ'
  exact ⟨fun _ hz => Q_P hθ hθ' hz, fun _ hw => P_Q_closed hθ hθ' hw⟩

end D12Complex.SectorPowerChart
