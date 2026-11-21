import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConvexEnergyEndpoints
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.ConvexEnergySubendpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
universe u
namespace ExpandedFA.PartIV.ConvexEnergyEndpoints
open ExpandedFA.PartIV.ConvexEnergySubendpoint
open ExpandedFA.PartIV.ConvexEnergySubendpoint.Spec

/-- Monotonicity removes the ambiguity in the absolute lower growth bound. -/
theorem signed_lower_growth {r α C : ℝ} {g : ℝ → ℝ} (hm : Monotone g)
    (hlo : ∀ t : ℝ, α * |t| ^ r - C ≤ |g t|) {t : ℝ} (ht : 0 ≤ t) :
    α * t ^ r - (C + 2 * |g 0|) ≤ g t := by
  have hg0 := hm ht
  have habs : |g t| ≤ g t + 2 * |g 0| := by
    rcases le_total 0 (g t) with h | h
    · rw [abs_of_nonneg h]; linarith [abs_nonneg (g 0)]
    · rw [abs_of_nonpos h]
      linarith [neg_abs_le (g 0)]
  have := hlo t
  rw [abs_of_nonneg ht] at this
  linarith

/-- Integrating the signed lower growth on a positive interval. -/
theorem primitive_lower_nonneg {r α C : ℝ} (hr : 1 < r) {g : ℝ → ℝ}
    (hg : Continuous g) (hm : Monotone g)
    (hlo : ∀ t : ℝ, α * |t| ^ (r - 1) - C ≤ |g t|)
    {t : ℝ} (ht : 0 ≤ t) :
    α / r * t ^ r - (C + 2 * |g 0|) * t ≤ primitive g t := by
  have hpow : Continuous (fun s : ℝ => s ^ (r - 1)) :=
    Real.continuous_rpow_const (by linarith)
  have hi : (∫ s in (0 : ℝ)..t, (α * s ^ (r - 1) - (C + 2 * |g 0|))) ≤
      primitive g t := intervalIntegral.integral_mono_on ht
    (((hpow.const_mul α).sub continuous_const).intervalIntegrable 0 t)
    (hg.intervalIntegrable 0 t)
    (fun s hs => signed_lower_growth hm hlo hs.1)
  have heq : (∫ s in (0 : ℝ)..t, (α * s ^ (r - 1) - (C + 2 * |g 0|))) =
      α / r * t ^ r - (C + 2 * |g 0|) * t := by
    rw [intervalIntegral.integral_sub
      ((hpow.const_mul α).intervalIntegrable 0 t) (continuous_const.intervalIntegrable 0 t),
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    simp only [sub_add_cancel, Real.zero_rpow (by linarith : r ≠ 0), sub_zero,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [heq] at hi
  exact hi

/-- The negative half line is handled by reflection, with the original oriented primitive. -/
theorem primitive_lower {r α C : ℝ} (hr : 1 < r) {g : ℝ → ℝ}
    (hg : Continuous g) (hm : Monotone g)
    (hlo : ∀ t : ℝ, α * |t| ^ (r - 1) - C ≤ |g t|) (t : ℝ) :
    α / r * |t| ^ r - (C + 2 * |g 0|) * |t| ≤ primitive g t := by
  rcases le_total 0 t with ht | ht
  · simpa only [abs_of_nonneg ht] using primitive_lower_nonneg hr hg hm hlo ht
  · let h : ℝ → ℝ := fun s => -g (-s)
    have hh : Continuous h := (hg.comp continuous_neg).neg
    have hhm : Monotone h := fun a b hab => neg_le_neg (hm (neg_le_neg hab))
    have hhl : ∀ s : ℝ, α * |s| ^ (r - 1) - C ≤ |h s| := by
      intro s
      simpa only [h, abs_neg] using hlo (-s)
    have hi := primitive_lower_nonneg hr hh hhm hhl (neg_nonneg.mpr ht)
    have heq : primitive h (-t) = primitive g t := by
      unfold primitive
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg]
      simp only [neg_neg, neg_zero]
      rw [intervalIntegral.integral_symm, neg_neg]
    rw [heq] at hi
    simpa only [h, neg_zero, abs_neg, abs_of_nonpos ht] using hi

/-- Scaled Young inequality, with an arbitrarily small leading coefficient. -/
theorem young_absorb {r : ℝ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a * b ≤ ε * a ^ r + K * b ^ (r / (r - 1)) := by
  let q := r / (r - 1)
  let s := (ε * r) ^ (1 / r)
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := Real.rpow_pos_of_pos (mul_pos hε hr0) _
  have hsr : s ^ r = ε * r := by
    dsimp [s]
    rw [one_div, Real.rpow_inv_rpow (mul_nonneg hε.le hr0.le) hr0.ne']
  have hq : 0 < q := div_pos hr0 (sub_pos.mpr hr)
  refine ⟨s⁻¹ ^ q / q, by positivity, fun a b ha hb => ?_⟩
  have h := Real.young_inequality_of_nonneg (mul_nonneg hs.le ha)
    (div_nonneg hb hs.le) (Real.HolderConjugate.conjExponent hr)
  change s * a * (b / s) ≤ (s * a) ^ r / r + (b / s) ^ q / q at h
  rw [Real.mul_rpow hs.le ha, hsr, Real.div_rpow hb hs.le] at h
  have heq : s * a * (b / s) = a * b := by
    calc
      _ = (a * b) * s / s := by ring
      _ = _ := mul_div_cancel_right₀ _ hs.ne'
  rw [heq] at h
  have heq' : (ε * r * a ^ r) / r = ε * a ^ r := by
    calc
      _ = (ε * a ^ r) * r / r := by ring
      _ = _ := mul_div_cancel_right₀ _ hr0.ne'
  rw [heq'] at h
  change a * b ≤ ε * a ^ r + (s⁻¹ ^ q / q) * b ^ q
  calc
    a * b ≤ ε * a ^ r + b ^ q / s ^ q / q := h
    _ = _ := by rw [Real.inv_rpow hs.le]; ring

/-- A simple power estimate, valid also when the base is zero. -/
theorem one_add_rpow_le {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) :
    (1 + x) ^ s ≤ 2 ^ s * (1 + x ^ s) := by
  rcases le_total x 1 with h | h
  · have ht := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + x)
      (show 1 + x ≤ 2 by linarith) hs
    exact ht.trans (le_mul_of_one_le_right (by positivity)
      (by linarith [Real.rpow_nonneg hx s]))
  · calc
      (1 + x) ^ s ≤ (2 * x) ^ s :=
        Real.rpow_le_rpow (by positivity) (by linarith) hs
      _ = 2 ^ s * x ^ s := Real.mul_rpow (by norm_num) hx
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Upper growth controls powers of any fixed translate of the slope. -/
theorem slope_power_bound {r : ℝ} (hr : 1 < r) {g : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hgr : ∀ t : ℝ, |g t| ≤ C * (1 + |t| ^ (r - 1)))
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t : ℝ,
      (L + |g t|) ^ (r / (r - 1)) ≤ H * (1 + |t| ^ r) := by
  let q := r / (r - 1)
  have hq : 0 < q := div_pos (by linarith) (by linarith)
  refine ⟨(L + C) ^ q * 2 ^ q, by positivity, fun t => ?_⟩
  have ht : L + |g t| ≤ (L + C) * (1 + |t| ^ (r - 1)) := by
    nlinarith [hgr t, Real.rpow_nonneg (abs_nonneg t) (r - 1)]
  calc
    (L + |g t|) ^ q ≤ ((L + C) * (1 + |t| ^ (r - 1))) ^ q :=
      Real.rpow_le_rpow (by positivity) ht hq.le
    _ = (L + C) ^ q * (1 + |t| ^ (r - 1)) ^ q :=
      Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (L + C) ^ q * (2 ^ q * (1 + (|t| ^ (r - 1)) ^ q)) :=
      mul_le_mul_of_nonneg_left (one_add_rpow_le (by positivity) hq.le) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul (abs_nonneg t)]
      have hexp : (r - 1) * q = r := by
        dsimp [q]
        exact mul_div_cancel₀ r (by linarith : r - 1 ≠ 0)
      rw [hexp]
      ring

/-- The first power and the mixed growth product are dominated by 1+|t|^r. -/
theorem mixed_growth_bound {r L C : ℝ} (hr : 1 < r) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (t : ℝ) :
    |t| * (L + C * (1 + |t| ^ (r - 1))) ≤ (L + 2 * C) * (1 + |t| ^ r) := by
  have ht : |t| ≤ 1 + |t| ^ r := by
    rcases le_total |t| 1 with h | h
    · linarith [Real.rpow_nonneg (abs_nonneg t) r]
    · linarith [Real.self_le_rpow_of_one_le h hr.le]
  have heq : |t| * |t| ^ (r - 1) = |t| ^ r := by
    simpa only [add_sub_cancel] using
      (Real.rpow_one_add' (abs_nonneg t) (show 1 + (r - 1) ≠ 0 by linarith)).symm
  have := mul_le_mul_of_nonneg_left ht (show 0 ≤ L + C by positivity)
  nlinarith [Real.rpow_nonneg (abs_nonneg t) r]

/-- The required scalar remainder coercivity follows from both growth bounds. -/
theorem remainder_coercivity : Spec.RemainderCoercivity := by
  intro p hp hptop g hg hm hu hl
  obtain ⟨C, hC, hgr⟩ := hu
  obtain ⟨α, C₀, hα, hlo⟩ := hl
  let r := p.toReal
  have hr : 1 < r := toReal_gt_one hp hptop
  let c := α / r
  let L := abs (C₀ + 2 * |g 0|)
  have hc : 0 < c := div_pos hα (by linarith)
  obtain ⟨J, hJ, hy⟩ := young_absorb hr (half_pos hc)
  obtain ⟨H, hH, hpow⟩ := slope_power_bound hr hC hgr (abs_nonneg (C₀ + 2 * |g 0|))
  let T := |g 0| + 4 * C
  let B := T + J * H
  refine ⟨2 / c, (2 / c) * B, by positivity, by dsimp [B, T]; positivity,
    fun a b => ?_⟩
  have hprimitive := primitive_lower hr hg hm hlo a
  have hL : C₀ + 2 * |g 0| ≤ L := le_abs_self _
  have hprim : c * |a| ^ r ≤ primitive g a + L * |a| := by
    have := mul_le_mul_of_nonneg_right hL (abs_nonneg a)
    dsimp [c, r] at *
    linarith
  have htangent : g b * (a - b) ≤ |g b| * (|a| + |b|) := by
    calc
      _ ≤ |g b * (a - b)| := le_abs_self _
      _ = |g b| * |a - b| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_sub a b) (abs_nonneg _)
  have hid : primitive g a = remainder g a b + primitive g b + g b * (a - b) := by
    unfold remainder
    ring
  have hgb := mul_le_mul_of_nonneg_left (hgr b) (abs_nonneg b)
  have hG := primitive_abs_le hm b
  have hmix₁ := mixed_growth_bound hr (abs_nonneg (g 0)) hC b
  have hmix₂ := mixed_growth_bound hr (show (0 : ℝ) ≤ 0 by rfl) hC b
  have hb : |primitive g b| + |g b| * |b| ≤ T * (1 + |b| ^ r) := by
    have hh : |b| * (|g 0| + |g b|) ≤
        |b| * (|g 0| + C * (1 + |b| ^ (r - 1))) := by gcongr; exact hgr b
    dsimp [T]
    nlinarith [Real.rpow_nonneg (abs_nonneg b) r]
  have hyab := hy |a| (L + |g b|) (abs_nonneg a) (by dsimp [L]; positivity)
  have hpowb := mul_le_mul_of_nonneg_left (hpow b) hJ
  have hmain : c / 2 * |a| ^ r ≤ remainder g a b + B * (1 + |b| ^ r) := by
    have hGb := le_abs_self (primitive g b)
    dsimp [B]
    rw [hid] at hprim
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 2 / c by positivity)
  have heq : (2 / c) * (c / 2 * |a| ^ r) = |a| ^ r := by
    field_simp [hc.ne']
  rw [heq] at hscale
  convert hscale using 1
  ring

/-- Multiplication by a fixed scalar preserves uniform integrability. -/
theorem unifIntegrable_const_mul {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} {f : ℕ → X → ℝ} (hf : UnifIntegrable f p μ) (C : ℝ) :
    UnifIntegrable (fun n x => C * f n x) p μ := by
  change UnifIntegrable (fun n => C • f n) p μ
  unfold UnifIntegrable at *
  have ht := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hf (Or.inr enorm_ne_top)
  simpa only [ENNReal.mul_iSup, mul_zero, ← eLpNorm_const_smul] using ht

/-- Uniform integrability of p-th powers is exactly the small-set estimate
needed for the Lp form of Vitali. -/
theorem unifIntegrable_of_powers {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} (hp : 0 < p) (hptop : p ≠ ∞) {f : ℕ → X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hui : UnifIntegrable (fun n x => |f n x| ^ p.toReal) 1 μ) :
    UnifIntegrable f p μ := by
  have hr := ENNReal.toReal_pos hp.ne' hptop
  apply unifIntegrable_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := unifIntegrable_iff.mp hui (ε ^ p.toReal)
    (ENNReal.rpow_pos_of_nonneg hε hr.le)
  refine ⟨δ, hδ, fun n s hs => ?_⟩
  apply (ENNReal.rpow_le_rpow_iff hr).mp
  have h := hδbound n s hs
  simpa only [← Real.norm_eq_abs,
    eLpNorm_norm_rpow (f n) (hf n).restrict hr, one_mul, ENNReal.ofReal_toReal hptop] using h

/-- The coercivity estimate transfers the L¹ remainder limit to uniform
integrability of the p-th powers. -/
theorem power_uniform_integrability : Spec.PowerUniformIntegrability.{u} := by
  intro X _ μ _ p _ g v u h hlo
  obtain ⟨hiD, _htD, hD⟩ := remainder_convergence μ p g v u h
  obtain ⟨hp, hptop, hg, hm, hu, _hw, _hsup⟩ := h
  obtain ⟨A, B, hA, hB, hab⟩ := remainder_coercivity p hp hptop g hg hm hu hlo
  have huiD : UnifIntegrable (fun n x => remainder g (v n x) (u x)) 1 μ :=
    unifIntegrable_of_tendsto_Lp_zero le_rfl ENNReal.one_ne_top
      (fun n => memLp_one_iff_integrable.mpr (hiD n)) hD
  have hiU : Integrable (fun x => 1 + |u x| ^ p.toReal) μ := by
    have hi := (integrable_const (1 : ℝ) (μ := μ)).add
      (Lp.memLp u).integrable_norm_rpow'
    exact hi.congr (Eventually.of_forall (fun x => by
      simp only [Pi.add_apply, Real.norm_eq_abs]))
  have huiU := unifIntegrable_const (ι := ℕ) le_rfl ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hiU)
  have hui := (unifIntegrable_const_mul huiD A).add
    (unifIntegrable_const_mul huiU B) le_rfl
  apply hui.ae_mono
  · intro n
    simpa only [Real.norm_eq_abs] using
      (Real.continuous_rpow_const p.toReal_nonneg).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (v n)).norm
  · intro n
    apply Eventually.of_forall
    intro x
    simp only [Real.enorm_eq_ofReal_abs, Pi.add_apply]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg (by positivity : 0 ≤ |v n x| ^ p.toReal),
      abs_of_nonneg (show 0 ≤ A * remainder g (v n x) (u x) +
        B * (1 + |u x| ^ p.toReal) from
          add_nonneg (mul_nonneg hA.le (remainder_nonnegative g hg hm _ _))
            (mul_nonneg hB (by positivity)))]
    exact hab _ _

/-- Upper growth carries uniform integrability of |v|^p to that of
|g(v)|^{p′}, at the exact conjugate exponent. -/
theorem image_power_uniform_integrability {X : Type u} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {p : ℝ≥0∞}
    (hp : 1 < p) (hptop : p ≠ ∞) {g : ℝ → ℝ} (hg : Continuous g)
    (hu : UpperGrowth p g) {f : ℕ → X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hui : UnifIntegrable (fun n x => |f n x| ^ p.toReal) 1 μ) :
    UnifIntegrable (fun n x => |g (f n x)| ^ (conjugate p).toReal) 1 μ := by
  obtain ⟨C, hC, hgr⟩ := hu
  have hr := toReal_gt_one hp hptop
  obtain ⟨H, hH, hbound⟩ := slope_power_bound hr hC hgr (show (0 : ℝ) ≤ 0 by rfl)
  have hq : (conjugate p).toReal = p.toReal / (p.toReal - 1) := by
    rw [conjugate, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]
  have hui1 : UnifIntegrable (fun _ : ℕ => fun _ : X => (1 : ℝ)) 1 μ :=
    unifIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const (1 : ℝ))
  have huiMajor := unifIntegrable_const_mul (hui1.add hui le_rfl) H
  apply huiMajor.ae_mono
  · intro n
    simpa only [Real.norm_eq_abs] using
      (Real.continuous_rpow_const (conjugate p).toReal_nonneg).comp_aestronglyMeasurable
        (hg.comp_aestronglyMeasurable (hf n)).norm
  · intro n
    apply Eventually.of_forall
    intro x
    simp only [Real.enorm_eq_ofReal_abs, Pi.add_apply]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg (by positivity : 0 ≤ |g (f n x)| ^ (conjugate p).toReal),
      abs_of_nonneg (show 0 ≤ H * (1 + |f n x| ^ p.toReal) by positivity), hq]
    simpa only [zero_add] using hbound (f n x)

/-- Nonlinear convergence at the endpoint p′. Strict monotonicity is not needed. -/
theorem image_endpoint : Spec.ImageEndpoint.{u} := by
  intro X _ μ _ p _ g v u h hlo
  have huiP := power_uniform_integrability μ p g v u h hlo
  have hmeasure := (image_subendpoint μ p g v u h).1
  obtain ⟨hp, hptop, hg, _hm, hu, _hw, _hsup⟩ := h
  have hq := conjugate_gt_one hp hptop
  have hqt := conjugate_ne_top p
  have huiGP := image_power_uniform_integrability hp hptop hg hu
    (fun n => Lp.aestronglyMeasurable (v n)) huiP
  have huiG := unifIntegrable_of_powers (zero_lt_one.trans hq) hqt
    (fun n => hg.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (v n))) huiGP
  refine ⟨fun n => image_memLp hp hptop hg hu (Lp.memLp (v n)),
    image_memLp hp hptop hg hu (Lp.memLp u), ?_⟩
  exact tendsto_Lp_finite_of_tendstoInMeasure hq.le hqt
    (fun n => hg.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (v n)))
    (image_memLp hp hptop hg hu (Lp.memLp u)) huiG hmeasure

/-- Strict increase identifies the original limit in measure; the same power
uniform integrability then supplies convergence at p itself. -/
theorem strict_endpoint : Spec.StrictEndpoint.{u} := by
  intro X _ μ _ p _ g v u h hlo hstrict
  have huiP := power_uniform_integrability μ p g v u h hlo
  have hmeasure := (strict_subendpoint μ p g v u h hstrict).1
  obtain ⟨hp, hptop, _hg, _hm, _hu, _hw, _hsup⟩ := h
  have hui := unifIntegrable_of_powers (zero_lt_one.trans hp) hptop
    (fun n => Lp.aestronglyMeasurable (v n)) huiP
  exact tendsto_Lp_finite_of_tendstoInMeasure hp.le hptop
    (fun n => Lp.aestronglyMeasurable (v n)) (Lp.memLp u) hui hmeasure

end ExpandedFA.PartIV.ConvexEnergyEndpoints
