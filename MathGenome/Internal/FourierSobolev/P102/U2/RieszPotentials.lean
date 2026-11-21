import MathGenome.Internal.FourierSobolev.Specs.P102.U2.RieszPotentials
import MathGenome.Internal.FourierSobolev.P102.U2.MaximalStrong
import MathGenome.Internal.RealAnalysis.D11.Ch11.ConvolutionBound
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace P102.U2.RieszPotentials
open D11.Ch03 D11.Ch03.LebesgueMeasures D11.Ch03.EuclideanRegularity
open RieszPotentialsSpec
open D11.Ch13.AveragesMaximalDefinition
abbrev nativeSpace (d : ℕ) : MeasurableSpace (Point d) := inferInstance

lemma kernelValue_measurable {d : ℕ} (α : ℝ) : Measurable (kernelValue (d := d) α) :=
  measurable_norm.pow_const _

/-- The original unnormalized kernel, with its usual total real-power convention. -/
def kernel {d : ℕ} (α : ℝ) (z : Point d) : ℝ := kernelValue α z
/-- The actual Bochner integral, not an assumed bounded operator. -/
def potential {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (f : Point d → 𝕜) (x : Point d) : 𝕜 := potentialValue α f x
/-- The absolute integral, allowed to be infinite. -/
def absolutePotential {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (f : Point d → 𝕜) (x : Point d) : ℝ≥0∞ := absoluteValue α f x

section BorelHelpers
variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

omit [NeZero d] in
lemma kernel_measurable_borel (α : ℝ) :
    @Measurable (Point d) ℝ (nativeSpace d) _ (kernel α) := by
  exact kernelValue_measurable α

/-- Scalar integrands are jointly measurable for Borel input versions. -/
lemma integrand_measurable_borel (α : ℝ) {f : Point d → 𝕜}
    (hf : @Measurable _ _ (nativeSpace d) _ f) :
    @Measurable (Point d × Point d) 𝕜 ((lebesgueSpace d).prod (lebesgueSpace d)) _
      (fun z => kernel α (z.1-z.2) • f z.2) := by
  have hi : @Measurable (Point d) (Point d) (lebesgueSpace d) (nativeSpace d) id :=
    measurable_id'' (native_borel_le d)
  let : MeasurableSpace (Point d × Point d) := (lebesgueSpace d).prod (lebesgueSpace d)
  have hx : @Measurable (Point d × Point d) (Point d) _ (nativeSpace d) Prod.fst :=
    hi.comp measurable_fst
  have hy : @Measurable (Point d × Point d) (Point d) _ (nativeSpace d) Prod.snd :=
    hi.comp measurable_snd
  have hsub : @Measurable (Point d × Point d) (Point d) _ (nativeSpace d)
      (fun z => z.1-z.2) := hx.sub hy
  exact ((kernel_measurable_borel α).comp hsub).smul (hf.comp hy)

/-- The singularity is locally integrable exactly in the needed range α > 0. -/
lemma kernel_integrableOn_ball_borel (α : ℝ) (hα : 0 < α) (R : ℝ) :
    IntegrableOn (kernel (d := d) α) (Metric.ball 0 R) volume := by
  apply integrableOn_ball_of_norm_le_rpow
    (show 1 ≤ Module.finrank ℝ (Point d) by
      simpa [Point] using Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    (α := (d : ℝ) - α) (C := 1)
  · simpa [Point] using (sub_lt_self (d : ℝ) hα)
  · exact Eventually.of_forall (fun z => by
      simp only [kernel, kernelValue, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul, neg_sub]
      exact le_rfl)
  · exact (kernel_measurable_borel α).aestronglyMeasurable

lemma nearKernel_integrable_borel (α : ℝ) (hα : 0 < α) (R : ℝ) :
    Integrable ((Metric.ball (0 : Point d) R).indicator (kernel α)) volume :=
  (integrable_indicator_iff measurableSet_ball).mpr
    (kernel_integrableOn_ball_borel α hα R)

lemma nearKernel_stronglyMeasurable_borel (α R : ℝ) :
    @StronglyMeasurable (Point d) ℝ _ (nativeSpace d)
      ((Metric.ball 0 R).indicator (kernel α)) :=
  ((kernel_measurable_borel α).indicator measurableSet_ball).stronglyMeasurable

/-- Dilation law for the mass of the truncated, unnormalized kernel. -/
lemma nearKernel_integral_borel (α R : ℝ) (hR : 0 < R) :
    (∫ z : Point d, (Metric.ball 0 R).indicator (kernel α) z) =
      R ^ α * ∫ z : Point d, (Metric.ball 0 1).indicator (kernel α) z := by
  have hscale : (fun z : Point d => (Metric.ball 0 R).indicator (kernel α) z) =
      fun z => R ^ (α - (d : ℝ)) *
        (Metric.ball 0 1).indicator (kernel α) (R⁻¹ • z) := by
    funext z
    have hn : ‖R⁻¹ • z‖ = R⁻¹ * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hb : R⁻¹ • z ∈ Metric.ball (0 : Point d) 1 ↔ z ∈ Metric.ball 0 R := by
      simp only [Metric.mem_ball, dist_zero_right, hn]
      rw [← div_eq_inv_mul, div_lt_one hR]
    by_cases hz : z ∈ Metric.ball (0 : Point d) R
    · simp only [indicator_of_mem hz, indicator_of_mem (hb.mpr hz), kernel,
        kernelValue, hn, Real.mul_rpow (inv_nonneg.mpr hR.le) (norm_nonneg _),
        Real.inv_rpow hR.le]
      rw [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hR _).ne', one_mul]
    · simp only [indicator_of_notMem hz, indicator_of_notMem (mt hb.mp hz), mul_zero]
  rw [hscale, integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ hR.le]
  simp only [smul_eq_mul, finrank_euclideanSpace, Point, Fintype.card_fin]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hR]
  congr 2
  ring

/-- A homogeneous power is integrable outside a positive radius when its
exponent is strictly below minus the Euclidean dimension. -/
lemma tail_rpow_integrable_borel (s R : ℝ) (hs : s < -(d : ℝ)) (hR : 0 < R) :
    Integrable (({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s)) volume := by
  let g : ℝ → ℝ := (Ici R).indicator (fun r => r ^ s)
  have hd : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hi : Integrable ((Ici R).indicator (fun r : ℝ => r ^ ((d : ℝ) - 1 + s))) volume := by
    apply (integrable_indicator_iff measurableSet_Ici).mpr
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) hR).congr_set_ae Ioi_ae_eq_Ici.symm
  have hrad : IntegrableOn (fun r : ℝ => r ^ (Module.finrank ℝ (Point d) - 1) • g r)
      (Ioi 0) volume := by
    apply (hi.restrict (s := Ioi 0)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases hmem : R ≤ r
    · simp only [g, indicator_apply, mem_Ici, if_pos hmem, smul_eq_mul]
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]
      congr 2
      simp only [Point, finrank_euclideanSpace, Fintype.card_fin]
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hd.ne')]
      simp
    · simp only [g, indicator_apply, mem_Ici, if_neg hmem, smul_zero]
  have h := (integrable_fun_norm_addHaar volume (f := g)).mpr hrad
  apply h.congr
  exact Eventually.of_forall fun z => by
    by_cases hz : R ≤ ‖z‖ <;> simp [g, hz]

/-- The exponent relation in the manuscript gives precisely the moment
identity used after the Hedberg inequality. Positivity of q is derived. -/
lemma exponent_identity (α p q : ℝ) (hα : 0 < α) (hp : 1 < p)
    (hpd : p < (d : ℝ) / α) (hq : 1 / q = 1 / p - α / (d : ℝ)) :
    0 < q ∧ q * (1 - α * p / (d : ℝ)) = p := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hprod : p * α < d := (lt_div_iff₀ hα).mp hpd
  have hr : α / (d : ℝ) < 1 / p :=
    (div_lt_div_iff₀ hd hp0).mpr (by nlinarith)
  have hq0 : 0 < q := one_div_pos.mp (by rw [hq]; exact sub_pos.mpr hr)
  refine ⟨hq0, ?_⟩
  field_simp [hp0.ne', hq0.ne', hd.ne'] at hq ⊢
  nlinarith

/-- The cutoff which makes the far contribution half the requested level. -/
lemma endpoint_radius (b α N t : ℝ) (hb : 0 < b) (hN : 0 < N) (ht : 0 < t) :
    let R := (2 * N / t) ^ (1 / b)
    0 < R ∧ R ^ (-b) * N = t / 2 ∧
      R ^ α * N / (t / 2) = (2 * N / t) ^ ((b + α) / b) := by
  dsimp only
  have hu : 0 < 2 * N / t := by positivity
  refine ⟨Real.rpow_pos_of_pos hu _, ?_, ?_⟩
  · rw [← Real.rpow_mul hu.le, show 1 / b * -b = -1 by field_simp,
      Real.rpow_neg_one]
    field_simp
  · rw [← Real.rpow_mul hu.le]
    calc
      (2 * N / t) ^ (1 / b * α) * N / (t / 2) =
          (2 * N / t) ^ (1 / b * α) * (2 * N / t) := by ring
      _ = (2 * N / t) ^ (1 / b * α + 1) := by
        rw [Real.rpow_add hu, Real.rpow_one]
      _ = _ := by congr 1; field_simp; ring

end BorelHelpers

section BorelTail
variable {d : ℕ} [NeZero d]
lemma tail_rpow_integral_borel (s R : ℝ) (hR : 0 < R) :
    (∫ z : Point d, ({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) z) =
      R ^ (s + (d : ℝ)) * ∫ z : Point d,
        ({z : Point d | 1 ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) z := by
  have hscale : (fun z : Point d => ({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) z) =
      fun z => R ^ s *
        ({z : Point d | 1 ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) (R⁻¹ • z) := by
    funext z
    have hn : ‖R⁻¹ • z‖ = R⁻¹ * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hb : R⁻¹ • z ∈ {z : Point d | 1 ≤ ‖z‖} ↔ z ∈ {z : Point d | R ≤ ‖z‖} := by
      change 1 ≤ ‖R⁻¹ • z‖ ↔ R ≤ ‖z‖
      rw [hn, ← div_eq_inv_mul, le_div_iff₀ hR]
      simp
    by_cases hz : z ∈ {z : Point d | R ≤ ‖z‖}
    · simp only [indicator_of_mem hz, indicator_of_mem (hb.mpr hz), hn,
        Real.mul_rpow (inv_nonneg.mpr hR.le) (norm_nonneg _), Real.inv_rpow hR.le]
      rw [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hR _).ne', one_mul]
    · simp only [indicator_of_notMem hz, indicator_of_notMem (mt hb.mp hz), mul_zero]
  rw [hscale, integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ hR.le]
  simp only [smul_eq_mul, finrank_euclideanSpace, Point, Fintype.card_fin]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hR]

lemma tail_rpow_measurable_borel (s R : ℝ) :
    Measurable (({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s)) :=
  (measurable_norm.pow_const s).indicator (measurableSet_le measurable_const measurable_norm)
end BorelTail

lemma native_ball_scale {d : ℕ} (x : Point d) (r : ℝ) (hr : 0 < r) :
    (volume : Measure (Point d)) (ball x r) =
      ENNReal.ofReal (r ^ (d : ℝ)) * volume (ball (0 : Point d) 1) := by
  simpa only [Point, finrank_euclideanSpace, Fintype.card_fin, Real.rpow_natCast] using
    Measure.addHaar_ball_of_pos (volume : Measure (Point d)) x hr


/- The elementary optimization and moment argument used for the strong bound. -/
namespace ScaleTransfer
lemma balance_pos (a b A B m n h : ℝ) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n)
    (hscale : ∀ R : ℝ, 0 < R → h ≤ A * R ^ a * m + B * R ^ (a-b) * n) :
    h ≤ (A+B) * n ^ (a/b) * m ^ (1-a/b) := by
  let R := (n/m) ^ (1/b)
  have hnm : 0 < n/m := div_pos hn hm
  have hR : 0 < R := Real.rpow_pos_of_pos hnm _
  have he1 : 1/b*a = a/b := by ring
  have he2 : 1/b*(a-b) = a/b-1 := by field_simp
  have hn0 := (Real.rpow_pos_of_pos hn (a/b)).ne'
  have hm0 := (Real.rpow_pos_of_pos hm (a/b)).ne'
  have hr1 : R ^ a * m = n ^ (a/b) * m ^ (1-a/b) := by
    rw [show R ^ a = (n/m) ^ (a/b) by
      dsimp [R]; rw [← Real.rpow_mul hnm.le, he1]]
    rw [Real.div_rpow hn.le hm.le, Real.rpow_sub hm 1 (a/b), Real.rpow_one]
    ring
  have hr2 : R ^ (a-b) * n = n ^ (a/b) * m ^ (1-a/b) := by
    rw [show R ^ (a-b) = (n/m) ^ (a/b-1) by
      dsimp [R]; rw [← Real.rpow_mul hnm.le, he2]]
    rw [Real.div_rpow hn.le hm.le, Real.rpow_sub hn (a/b) 1,
      Real.rpow_sub hm (a/b) 1, Real.rpow_sub hm 1 (a/b), Real.rpow_one, Real.rpow_one]
    field_simp
  calc
    h ≤ A * R ^ a * m + B * R ^ (a-b) * n := hscale R hR
    _ = (A+B) * n ^ (a/b) * m ^ (1-a/b) := by
      rw [mul_assoc A, mul_assoc B, hr1, hr2]; ring
lemma balance (a b A B m n h : ℝ) (ha : 0 < a) (hab : a < b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hscale : ∀ R : ℝ, 0 < R → h ≤ A * R ^ a * m + B * R ^ (a-b) * n) :
    h ≤ (A+B) * n ^ (a/b) * m ^ (1-a/b) := by
  have hb : 0 < b := lt_trans ha hab
  have ht : 0 < a/b := div_pos ha hb
  have ht' : 0 < 1-a/b := sub_pos.mpr ((div_lt_one hb).mpr hab)
  have hc : ContinuousAt (fun ε : ℝ => (A+B) * (n+ε) ^ (a/b) *
      (m+ε) ^ (1-a/b)) 0 :=
    (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).rpow_const
      (Or.inr ht.le))).mul
        ((continuousAt_const.add continuousAt_id).rpow_const (Or.inr ht'.le))
  have hlim : Tendsto (fun ε : ℝ => (A+B) * (n+ε) ^ (a/b) *
      (m+ε) ^ (1-a/b)) (𝓝[>] 0) (𝓝 ((A+B) * n ^ (a/b) * m ^ (1-a/b))) := by
    simpa only [add_zero] using hc.tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with ε hε
  have he : 0 < ε := hε
  have hmε : 0 < m+ε := by linarith
  have hnε : 0 < n+ε := by linarith
  exact balance_pos a b A B (m+ε) (n+ε) h hb hmε hnε (fun R hR =>
    (hscale R hR).trans (add_le_add
      (mul_le_mul_of_nonneg_left (by linarith : m ≤ m+ε)
        (mul_nonneg hA (Real.rpow_nonneg hR.le _)))
      (mul_le_mul_of_nonneg_left (by linarith : n ≤ n+ε)
        (mul_nonneg hB (Real.rpow_nonneg hR.le _)))))
lemma balance_ennreal (a b A B : ℝ) (ha : 0 < a) (hab : a < b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (H M N : ℝ≥0∞) (hM : M ≠ ∞) (hN : N ≠ ∞)
    (hscale : ∀ R : ℝ, 0 < R → H ≤ ENNReal.ofReal (A * R ^ a) * M +
      ENNReal.ofReal (B * R ^ (a-b)) * N) :
    H ≤ ENNReal.ofReal (A+B) * N ^ (a/b) * M ^ (1-a/b) := by
  have hb : 0 < b := lt_trans ha hab
  have ht : 0 ≤ a/b := (div_pos ha hb).le
  have ht' : 0 ≤ 1-a/b := (sub_pos.mpr ((div_lt_one hb).mpr hab)).le
  have hfin (R : ℝ) : ENNReal.ofReal (A * R ^ a) * M +
      ENNReal.ofReal (B * R ^ (a-b)) * N ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN⟩
  have hH : H ≠ ∞ := ne_top_of_le_ne_top (hfin 1) (hscale 1 zero_lt_one)
  have hbal := balance a b A B M.toReal N.toReal H.toReal ha hab hA hB
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg (fun R hR => by
      have he := ENNReal.toReal_mono (hfin R) (hscale R hR)
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN)] at he
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (mul_nonneg hA (Real.rpow_nonneg hR.le _)), ENNReal.toReal_ofReal
        (mul_nonneg hB (Real.rpow_nonneg hR.le _))] using he)
  have he : H ≤ ENNReal.ofReal ((A+B) * N.toReal ^ (a/b) * M.toReal ^ (1-a/b)) :=
    (ENNReal.le_ofReal_iff_toReal_le hH (by positivity)).mpr hbal
  simpa only [ENNReal.ofReal_mul (mul_nonneg (add_nonneg hA hB)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)),
    ENNReal.ofReal_mul (add_nonneg hA hB),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ht,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ht',
    ENNReal.ofReal_toReal hN, ENNReal.ofReal_toReal hM] using he
lemma moment_transfer {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H M : X → ℝ≥0∞) (hM : AEMeasurable M μ) (K D N : ℝ≥0∞)
    (θ η p q : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hp : 0 < p) (hq : 0 < q)
    (hθη : θ+η=1) (hpq : q*η=p)
    (hH : ∀ᵐ x ∂μ, H x ≤ K * N ^ θ * M x ^ η)
    (hmax : (∫⁻ x, M x ^ p ∂μ) ^ (1/p) ≤ D*N) :
    (∫⁻ x, H x ^ q ∂μ) ^ (1/q) ≤ K * D ^ η * N := by
  have hqp : p * (1/q) = η := by rw [← hpq]; field_simp
  have hpow : (∫⁻ x, H x ^ q ∂μ) ≤ (K * N ^ θ) ^ q * ∫⁻ x, M x ^ p ∂μ := by
    calc
      _ ≤ ∫⁻ x, (K * N ^ θ * M x ^ η) ^ q ∂μ :=
        lintegral_mono_ae (hH.mono (fun x hx => ENNReal.rpow_le_rpow hx hq.le))
      _ = ∫⁻ x, (K * N ^ θ) ^ q * M x ^ p ∂μ := by
        congr 1; funext x
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, mul_comm η q, hpq]
      _ = _ := lintegral_const_mul'' _ (hM.pow_const p)
  calc
    _ ≤ ((K * N ^ θ) ^ q * ∫⁻ x, M x ^ p ∂μ) ^ (1/q) :=
      ENNReal.rpow_le_rpow hpow (by positivity)
    _ = K * N ^ θ * ((∫⁻ x, M x ^ p ∂μ) ^ (1/p)) ^ η := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hq.ne', ENNReal.rpow_one, ← ENNReal.rpow_mul]
      congr 2
      rw [← hqp]
      field_simp
    _ ≤ K * N ^ θ * (D*N) ^ η :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hmax hη)
    _ = K * D ^ η * N := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hη]
      rw [show K * N ^ θ * (D ^ η * N ^ η) = K * D ^ η * (N ^ θ * N ^ η) by ring,
        ← ENNReal.rpow_add_of_nonneg θ η hθ hη, hθη, ENNReal.rpow_one]
lemma scale_to_moment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H M : X → ℝ≥0∞) (hM : AEMeasurable M μ)
    (a b A B D p q : ℝ) (ha : 0 < a) (hab : a < b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hp : 0 < p) (hq : 0 < q)
    (hpq : q * (1-a/b) = p) (N : ℝ≥0∞) (hN : N ≠ ∞)
    (hMfin : ∀ᵐ x ∂μ, M x < ∞)
    (hscale : ∀ x R, 0 < R → H x ≤ ENNReal.ofReal (A * R ^ a) * M x +
      ENNReal.ofReal (B * R ^ (a-b)) * N)
    (hmax : (∫⁻ x, M x ^ p ∂μ) ^ (1/p) ≤ ENNReal.ofReal D*N) :
    (∫⁻ x, H x ^ q ∂μ) ^ (1/q) ≤
      ENNReal.ofReal ((A+B) * D ^ (1-a/b)) * N := by
  have hb : 0 < b := lt_trans ha hab
  have hη : 0 ≤ 1-a/b := (sub_pos.mpr ((div_lt_one hb).mpr hab)).le
  have hpt : ∀ᵐ x ∂μ, H x ≤ ENNReal.ofReal (A+B) * N ^ (a/b) * M x ^ (1-a/b) := by
    filter_upwards [hMfin] with x hx
    exact balance_ennreal a b A B ha hab hA hB (H x) (M x) N hx.ne hN (hscale x)
  have hbound := moment_transfer μ H M hM (ENNReal.ofReal (A+B)) (ENNReal.ofReal D) N
    (a/b) (1-a/b) p q (div_pos ha hb).le hη hp hq (by ring) hpq hpt hmax
  rwa [ENNReal.ofReal_rpow_of_nonneg hD hη, ← ENNReal.ofReal_mul (add_nonneg hA hB)] at hbound
end ScaleTransfer

local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) := lebesgueSpace d
local instance (d : ℕ) [NeZero d] : SigmaFinite (μ d) := lebesgue_sigmaFinite d


variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]

omit [NeZero d] in
lemma kernel_nonneg (α : ℝ) (z : Point d) : 0 ≤ kernel α z :=
  Real.rpow_nonneg (norm_nonneg _) _

lemma integrand_congr (α : ℝ) {f g : Point d → 𝕜}
    (h : f =ᵐ[μ d] g) (x : Point d) :
    (fun y => kernel α (x-y) • f y) =ᵐ[μ d]
      (fun y => kernel α (x-y) • g y) := by
  filter_upwards [h] with y hy
  rw [hy]

/-- Equal input representatives have equal potentials at every point, including
at points where the totalized Bochner integral is zero for lack of integrability. -/
theorem representative_independence : RieszPotentialsSpec.RepresentativeIndependence := by
  intro d _ 𝕜 _ α f g h
  refine ⟨?_, ?_, fun x => integrable_congr (integrand_congr α h x)⟩
  · funext x
    exact integral_congr_ae (integrand_congr α h x)
  · funext x
    apply lintegral_congr_ae
    filter_upwards [h] with y hy
    simp only [hy]

/-- Any assignment at the singular point gives the same integral and absolute
existence set. The claim needs no integrability assumption on the input. -/
theorem origin_independence : RieszPotentialsSpec.OriginIndependence := by
  intro d _ 𝕜 _ α k hk f x
  have hnull : μ d {x} = 0 := by
    exact (lebesgue_eq_volume d {x}).trans (measure_singleton x)
  have hne : ∀ᵐ y ∂μ d, y ≠ x := by
    exact ae_iff.mpr (by simpa using hnull)
  have he : (fun y => k (x-y) • f y) =ᵐ[μ d]
      (fun y => kernelValue α (x-y) • f y) := by
    filter_upwards [hne] with y hy
    rw [hk (x-y) (sub_ne_zero.mpr (Ne.symm hy))]
  exact ⟨integrable_congr he, integral_congr_ae he⟩

/-- The extended absolute integral is exactly the norm integral of the actual
integrand, so its finiteness supplies genuine absolute convergence. -/
lemma absolutePotential_eq_lintegral_enorm (α : ℝ) (f : Point d → 𝕜) (x : Point d) :
    absolutePotential α f x = ∫⁻ y, ‖kernel α (x-y) • f y‖ₑ ∂μ d := by
  apply lintegral_congr
  intro y
  rw [← ofReal_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (kernel_nonneg α (x-y))]
  rfl

/-- The norm of the totalized integral is always bounded by the extended
absolute integral. This remains true at divergent points. -/
lemma enorm_potential_le (α : ℝ) (f : Point d → 𝕜) (x : Point d) :
    ‖potential α f x‖ₑ ≤ absolutePotential α f x := by
  exact (enorm_integral_le_lintegral_enorm _).trans_eq
    (absolutePotential_eq_lintegral_enorm α f x).symm

section Measurability
variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Every completed-measurable input has a Borel version. This avoids assuming
that joint subtraction takes values in the completed measurable space. -/
lemma borel_version (f : Point d → 𝕜) (hf : AEStronglyMeasurable f (μ d)) :
    ∃ g : Point d → 𝕜, @Measurable _ _ (nativeSpace d) _ g ∧ f =ᵐ[μ d] g := by
  let : (μ d).IsComplete := lebesgue_complete d
  obtain ⟨g, hg, hfg⟩ := D11.Ch11.ConvolutionBound.borel_version f
    (aemeasurable_iff_measurable.mp hf.aemeasurable)
  exact ⟨g, hg, hfg⟩

/-- Both the actual potential and the extended absolute potential are measurable,
without assuming the norm bounds that remain to be proved. -/
theorem measurability : RieszPotentialsSpec.Measurability := by
  intro d _ 𝕜 _ _ _ α f hf
  let : SigmaFinite (μ d) := lebesgue_sigmaFinite d
  obtain ⟨g, hg, hfg⟩ := borel_version f hf
  have hi := integrand_measurable_borel α hg
  have he := representative_independence α f g hfg
  constructor
  · rw [he.1]
    exact (hi.stronglyMeasurable.integral_prod_right' (ν := μ d)).measurable
  · rw [he.2.1]
    have ha : absoluteValue α g =
        fun x => ∫⁻ y, ‖kernel α (x-y) • g y‖ₑ ∂μ d := by
      funext x
      exact absolutePotential_eq_lintegral_enorm α g x
    rw [ha]
    exact (hi.enorm.lintegral_prod_right' (ν := μ d))

lemma integrand_aestronglyMeasurable (α : ℝ) {f : Point d → 𝕜}
    (hf : AEStronglyMeasurable f (μ d)) (x : Point d) :
    AEStronglyMeasurable (fun y => kernel α (x-y) • f y) (μ d) := by
  obtain ⟨g, hg, hfg⟩ := borel_version f hf
  exact (((integrand_measurable_borel α hg).comp
    (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable).congr
    (integrand_congr α hfg x).symm

lemma integrable_iff_absolutePotential_lt_top (α : ℝ) {f : Point d → 𝕜}
    (hf : AEStronglyMeasurable f (μ d)) (x : Point d) :
    Integrable (fun y => kernel α (x-y) • f y) (μ d) ↔
      absolutePotential α f x < ∞ := by
  rw [absolutePotential_eq_lintegral_enorm]
  exact ⟨fun h => h.2, fun h => ⟨integrand_aestronglyMeasurable α hf x, h⟩⟩

/-- An extended absolute-moment bound controls the ordinary Lq norm, with
no a priori convergence assumption on the potential. -/
lemma eLpNorm_potential_le_absoluteMoment (α q : ℝ) (hq : 0 < q)
    {f : Point d → 𝕜} (hf : AEStronglyMeasurable f (μ d)) :
    eLpNorm (potential α f) (ENNReal.ofReal q) (μ d) ≤
      (∫⁻ x, absolutePotential α f x ^ q ∂μ d) ^ (1 / q) := by
  have hm : AEStronglyMeasurable (potential α f) (μ d) :=
    (measurability α f hf).1.aestronglyMeasurable
  calc
    _ = (∫⁻ x, ‖potential α f x‖ₑ ^ q ∂μ d) ^ (1 / q) := by
      simpa only [ENNReal.toReal_ofReal hq.le] using
        eLpNorm_eq_lintegral_rpow_enorm_toReal
          (m0 := Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value d)
          (p := ENNReal.ofReal q) (μ := μ d)
          (by positivity) ENNReal.ofReal_ne_top hm
    _ ≤ _ := ENNReal.rpow_le_rpow
      (lintegral_mono fun x => ENNReal.rpow_le_rpow (enorm_potential_le α f x) hq.le)
      (by positivity)

/-- A finite bound on the actual absolute moment gives absolute convergence
and an ordinary `Lq` output, with the same bound. -/
lemma potential_membership_of_absoluteMoment (α q : ℝ) (hq : 0 < q)
    {f : Point d → 𝕜} (hf : AEStronglyMeasurable f (μ d))
    (B : ℝ≥0∞) (hB : B < ∞)
    (hb : (∫⁻ x, absolutePotential α f x ^ q ∂μ d) ^ (1 / q) ≤ B) :
    (∀ᵐ x ∂μ d, Integrable (fun y => kernel α (x-y) • f y) (μ d)) ∧
      MemLp (potential α f) (ENNReal.ofReal q) (μ d) ∧
      eLpNorm (potential α f) (ENNReal.ofReal q) (μ d) ≤ B := by
  have hint : (∫⁻ x, absolutePotential α f x ^ q ∂μ d) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hq)).mp (hb.trans_lt hB)
  have hfinite : ∀ᵐ x ∂μ d, absolutePotential α f x < ∞ := by
    filter_upwards [ae_lt_top ((measurability α f hf).2.pow_const q) hint.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hq).mp hx
  have hnorm := (eLpNorm_potential_le_absoluteMoment α q hq hf).trans hb
  refine ⟨?_, hnorm.trans_lt hB, hnorm⟩
  filter_upwards [hfinite] with x hx
  exact (integrable_iff_absolutePotential_lt_top α hf x).mpr hx

/-- Transfer the integrable truncated kernel to the completed Lebesgue space. -/
lemma nearKernel_integrable (α : ℝ) (hα : 0 < α) (R : ℝ) :
    Integrable ((Metric.ball (0 : Point d) R).indicator (kernel α)) (μ d) := by
  apply integrable_of_integrable_trim (native_borel_le d)
  have htrim : (μ d).trim (native_borel_le d) = Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value d :=
    borel_restriction d (native_borel_le d)
  exact htrim ▸ nearKernel_integrable_borel α hα R

/-- The dilation law also holds on the completed Lebesgue space. -/
lemma nearKernel_integral (α R : ℝ) (hR : 0 < R) :
    (∫ z : Point d, (Metric.ball 0 R).indicator (kernel α) z ∂μ d) =
      R ^ α * ∫ z : Point d, (Metric.ball 0 1).indicator (kernel α) z ∂μ d := by
  have ht (r : ℝ) :
      (∫ z : Point d, (Metric.ball 0 r).indicator (kernel α) z ∂μ d) =
        ∫ z : Point d, (Metric.ball 0 r).indicator (kernel α) z
          ∂Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value d := by
    have hm := nearKernel_stronglyMeasurable_borel (d := d) α r
    have htrim := integral_trim (μ := μ d) (native_borel_le d) hm
    have heq := borel_restriction d (native_borel_le d)
    rw [heq] at htrim
    exact htrim
  rw [ht, ht]
  exact nearKernel_integral_borel α R hR

/-- Absolute existence at the L¹ endpoint follows already from an L¹ near
kernel and the bounded far kernel, independently of the weak estimate. -/
lemma ae_integrable_of_integrable (α : ℝ) (hα : 0 < α) (hαd : α < d)
    {f : Point d → 𝕜} (hf : Integrable f (μ d)) :
    ∀ᵐ x ∂μ d, Integrable (fun y => kernel α (x-y) • f y) (μ d) := by
  let k : Point d → ℝ := (Metric.ball (0 : Point d) 1).indicator (kernel α)
  have hk : Integrable k (μ d) := nearKernel_integrable α hα 1
  let : (μ d).IsComplete := lebesgue_complete d
  have hy := D11.Ch11.ConvolutionBound.young d ℝ 1 le_rfl k (fun y => ‖f y‖)
    (aemeasurable_iff_measurable.mp hk.aemeasurable)
    (aemeasurable_iff_measurable.mp hf.norm.aemeasurable)
    (memLp_one_iff_integrable.mpr hk) (memLp_one_iff_integrable.mpr hf.norm)
  filter_upwards [hy.1] with x hx
  have hi : Integrable (fun y => k (x-y) * ‖f y‖) (μ d) := by
    have ht := (D11.Ch11.ConvolutionBound.measurePreserving_const_sub x).integrable_comp_of_integrable hx
    simpa only [Function.comp_def, sub_sub_cancel] using ht
  have hb : ∀ y, ‖kernel α (x-y) • f y‖ ≤ k (x-y) * ‖f y‖ + ‖f y‖ := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg α _)]
    by_cases hy : x-y ∈ Metric.ball (0 : Point d) 1
    · simp only [k, indicator_of_mem hy]
      exact le_add_of_nonneg_right (norm_nonneg _)
    · have hone : 1 ≤ ‖x-y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hy
      have hk1 : kernel α (x-y) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hone (by linarith)
      simp only [k, indicator_of_notMem hy, zero_mul, zero_add]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1 (norm_nonneg (f y))
  exact (hi.add hf.norm).mono' (integrand_aestronglyMeasurable α hf.aestronglyMeasurable x)
    (Eventually.of_forall hb)

/-- An L¹ norm of a nonnegative real function is its ordinary mass. -/
lemma eLpNorm_one_nonneg {g : Point d → ℝ} (hg : Integrable g (μ d))
    (hn : ∀ x, 0 ≤ g x) :
    eLpNorm g 1 (μ d) = ENNReal.ofReal (∫ x, g x ∂μ d) := by
  rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
  simp_rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hn _)]
  exact (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hn)).symm

/-- For every cutoff radius the far part is uniformly bounded, while the near
part has controlled L¹ mass. This estimate concerns the actual potential. -/
lemma endpoint_majorant (α : ℝ) (hα : 0 < α) (hαd : α < d)
    {f : Point d → 𝕜} (hf : Integrable f (μ d)) (R : ℝ) (hR : 0 < R) :
    ∃ g : Point d → ℝ, Measurable g ∧ Integrable g (μ d) ∧
      (∀ x, 0 ≤ g x) ∧
      eLpNorm g 1 (μ d) ≤
        ENNReal.ofReal (R ^ α * ∫ z : Point d,
          (Metric.ball 0 1).indicator (kernel α) z ∂μ d) * eLpNorm f 1 (μ d) ∧
      ∀ᵐ x ∂μ d, ‖potential α f x‖ ≤
        g x + R ^ (α - (d : ℝ)) * ∫ y, ‖f y‖ ∂μ d := by
  let k : Point d → ℝ := (Metric.ball (0 : Point d) R).indicator (kernel α)
  have hk : Integrable k (μ d) := nearKernel_integrable α hα R
  have hkn (z : Point d) : 0 ≤ k z := indicator_nonneg (fun z _ => kernel_nonneg α z) z
  let : (μ d).IsComplete := lebesgue_complete d
  obtain ⟨hi, hm, hmem, hb⟩ := D11.Ch11.ConvolutionBound.young d ℝ 1 le_rfl k
    (fun y => ‖f y‖) (aemeasurable_iff_measurable.mp hk.aemeasurable)
    (aemeasurable_iff_measurable.mp hf.norm.aemeasurable)
    (memLp_one_iff_integrable.mpr hk) (memLp_one_iff_integrable.mpr hf.norm)
  let g := Specs.D11.Ch11.ConvolutionBound.convolution_value d k (fun y => ‖f y‖)
  refine ⟨g, hm, memLp_one_iff_integrable.mp hmem, ?_, ?_, ?_⟩
  · intro x
    exact integral_nonneg fun y => mul_nonneg (hkn y) (norm_nonneg _)
  · have hkernel : eLpNorm k 1 (μ d) =
        ENNReal.ofReal (R ^ α * ∫ z : Point d,
          (Metric.ball 0 1).indicator (kernel α) z ∂μ d) := by
      rw [eLpNorm_one_nonneg hk hkn]
      congr 1
      exact nearKernel_integral α R hR
    rw [hkernel] at hb
    have hn : eLpNorm (fun y => ‖f y‖) 1 (μ d) = eLpNorm f 1 (μ d) :=
      eLpNorm_norm f hf.aestronglyMeasurable
    exact hb.trans_eq (congrArg
      (ENNReal.ofReal (R ^ α * ∫ z : Point d,
        (Metric.ball 0 1).indicator (kernel α) z ∂μ d) * ·) hn)
  · filter_upwards [hi] with x hx
    have ht := (D11.Ch11.ConvolutionBound.measurePreserving_const_sub x).integrable_comp_of_integrable hx
    have ht' : Integrable (fun y => k (x-y) * ‖f y‖) (μ d) := by
      simpa only [Function.comp_def, sub_sub_cancel] using ht
    have hbound : ∀ y, ‖kernel α (x-y) • f y‖ ≤
        k (x-y) * ‖f y‖ + R ^ (α - (d : ℝ)) * ‖f y‖ := by
      intro y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg α _)]
      by_cases hy : x-y ∈ Metric.ball (0 : Point d) R
      · simp only [k, indicator_of_mem hy]
        exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hR.le _) (norm_nonneg _))
      · have hnorm : R ≤ ‖x-y‖ := by
          simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hy
        have hkR : kernel α (x-y) ≤ R ^ (α - (d : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hR hnorm (by linarith)
        simp only [k, indicator_of_notMem hy, zero_mul, zero_add]
        exact mul_le_mul_of_nonneg_right hkR (norm_nonneg _)
    have hnorm := norm_integral_le_of_norm_le (ht'.add (hf.norm.const_mul _))
      (Eventually.of_forall hbound)
    change ‖potential α f x‖ ≤ ∫ y,
      k (x-y) * ‖f y‖ + R ^ (α - (d : ℝ)) * ‖f y‖ ∂μ d at hnorm
    rw [integral_add ht' (hf.norm.const_mul _), integral_const_mul] at hnorm
    have heq : (∫ y, k (x-y) * ‖f y‖ ∂μ d) = g x := by
      simpa only [g, Specs.D11.Ch11.ConvolutionBound.convolution_value,
        Function.comp_def, sub_sub_cancel] using
        (D11.Ch11.ConvolutionBound.measurePreserving_const_sub x).integral_comp
          (MeasurableEquiv.ofInvolutive (fun y : Point d => x-y)
            (fun y => sub_sub_cancel x y)
            (D11.Ch11.ConvolutionBound.measurePreserving_const_sub x).measurable).measurableEmbedding
          (fun y => k y * ‖f (x-y)‖)
    rwa [heq] at hnorm

/-- The all-radius near/far decomposition yields the endpoint distribution
estimate, with no finiteness assumption on the potential made in advance. -/
lemma endpoint_distribution (α : ℝ) (hα : 0 < α) (hαd : α < d)
    {f : Point d → 𝕜} (hf : Integrable f (μ d))
    (hN : 0 < ∫ y, ‖f y‖ ∂μ d) (t : ℝ) (ht : 0 < t) :
    P102.U2.distribution (μ d) (potential α f) t ≤
      ENNReal.ofReal ((∫ z : Point d,
        (Metric.ball 0 1).indicator (kernel α) z ∂μ d) *
        (2 * (∫ y, ‖f y‖ ∂μ d) / t) ^ ((d : ℝ) / ((d : ℝ) - α))) := by
  let N := ∫ y, ‖f y‖ ∂μ d
  let A := ∫ z : Point d, (Metric.ball 0 1).indicator (kernel α) z ∂μ d
  let R := (2 * N / t) ^ (1 / ((d : ℝ) - α))
  obtain ⟨hR, hfar, hpower⟩ := endpoint_radius ((d : ℝ) - α) α N t (by linarith) hN ht
  change 0 < R at hR
  have hfar' : R ^ (α - (d : ℝ)) * N = t / 2 := by
    simpa only [neg_sub] using hfar
  have hpower' : R ^ α * N / (t / 2) =
      (2 * N / t) ^ ((d : ℝ) / ((d : ℝ) - α)) := by
    simpa only [sub_add_cancel] using hpower
  obtain ⟨g, hgm, hgi, hgn, hgb, hbound⟩ := endpoint_majorant α hα hαd hf R hR
  have hinput : eLpNorm f 1 (μ d) = ENNReal.ofReal N := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact (ofReal_integral_norm_eq_lintegral_enorm hf).symm
  have hnear : (∫⁻ x, ENNReal.ofReal (g x) ∂μ d) = eLpNorm g 1 (μ d) := by
    rw [eLpNorm_one_nonneg hgi hgn]
    exact (ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hgn)).symm
  calc
    _ ≤ μ d {x | ENNReal.ofReal (t / 2) ≤ ENNReal.ofReal (g x)} := by
      apply measure_mono_ae
      filter_upwards [hbound] with x hx
      intro hxt
      have hx' : ‖potential α f x‖ ≤ g x + t / 2 := by
        change ‖potential α f x‖ ≤ g x + R ^ (α - (d : ℝ)) * N at hx
        rwa [hfar'] at hx
      exact ENNReal.ofReal_le_ofReal (by change t < ‖potential α f x‖ at hxt; linarith)
    _ ≤ (∫⁻ x, ENNReal.ofReal (g x) ∂μ d) / ENNReal.ofReal (t / 2) :=
      meas_ge_le_lintegral_div hgm.ennreal_ofReal.aemeasurable
        (by positivity) ENNReal.ofReal_ne_top
    _ ≤ (ENNReal.ofReal (R ^ α * A) * ENNReal.ofReal N) / ENNReal.ofReal (t / 2) := by
      rw [hnear]
      exact ENNReal.div_le_div_right (hgb.trans_eq (congrArg (ENNReal.ofReal (R ^ α * A) * ·) hinput)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hR.le _)
          (integral_nonneg fun z => indicator_nonneg (fun z _ => kernel_nonneg α z) z)),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      calc
        R ^ α * A * N / (t / 2) = A * (R ^ α * N / (t / 2)) := by ring
        _ = _ := by rw [hpower']

lemma tail_rpow_measurable (s R : ℝ) :
    Measurable (({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s)) :=
  (tail_rpow_measurable_borel s R).mono (native_borel_le d) le_rfl

lemma tail_rpow_integrable (s R : ℝ) (hs : s < -(d : ℝ)) (hR : 0 < R) :
    Integrable (({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s)) (μ d) := by
  apply integrable_of_integrable_trim (native_borel_le d)
  have htrim : (μ d).trim (native_borel_le d) = Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value d :=
    borel_restriction d (native_borel_le d)
  exact htrim ▸ tail_rpow_integrable_borel s R hs hR

lemma tail_rpow_integral (s R : ℝ) (hR : 0 < R) :
    (∫ z : Point d, ({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) z ∂μ d) =
      R ^ (s + (d : ℝ)) * ∫ z : Point d,
        ({z : Point d | 1 ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) z ∂μ d := by
  have ht (r : ℝ) :
      (∫ z : Point d, ({z : Point d | r ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) z ∂μ d) =
        ∫ z : Point d, ({z : Point d | r ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s) z
          ∂Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value d := by
    have hm := (tail_rpow_measurable_borel (d := d) s r).stronglyMeasurable
    have htrim := integral_trim (μ := μ d) (native_borel_le d) hm
    have heq := borel_restriction d (native_borel_le d)
    rw [heq] at htrim
    exact htrim
  rw [ht, ht]
  exact tail_rpow_integral_borel s R hR


lemma far_kernel_holder (α p t : ℝ) (hpt : p.HolderConjugate t)
    (hs : (α - (d : ℝ)) * t < -(d : ℝ))
    {f : Point d → 𝕜} (hf : MemLp f (ENNReal.ofReal p) (μ d))
    (x : Point d) (R : ℝ) (hR : 0 < R) :
    (∫⁻ y in {y : Point d | R ≤ ‖x-y‖},
      ENNReal.ofReal (kernel α (x-y) * ‖f y‖) ∂μ d) ≤
      ENNReal.ofReal (((∫ z : Point d,
        ({z : Point d | 1 ≤ ‖z‖}).indicator
          (fun z => ‖z‖ ^ ((α - (d : ℝ)) * t)) z ∂μ d) ^ (1 / t)) *
        R ^ (α - (d : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) (μ d) := by
  let s := (α - (d : ℝ)) * t
  let k : Point d → ℝ := ({z : Point d | R ≤ ‖z‖}).indicator (kernel α)
  let g : Point d → ℝ := ({z : Point d | R ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ s)
  let A : ℝ := ∫ z : Point d, ({z : Point d | 1 ≤ ‖z‖}).indicator
    (fun z => ‖z‖ ^ s) z ∂μ d
  have hkn (z : Point d) : 0 ≤ k z :=
    indicator_nonneg (fun z _ => kernel_nonneg α z) z
  have hgn (z : Point d) : 0 ≤ g z :=
    indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z
  have hAn : 0 ≤ A := integral_nonneg fun z =>
    indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z
  have hkm : Measurable k := tail_rpow_measurable (α - (d : ℝ)) R
  have hgm : Measurable g := tail_rpow_measurable s R
  have hg : Integrable g (μ d) := tail_rpow_integrable s R hs hR
  have hsub := D11.Ch11.ConvolutionBound.measurePreserving_const_sub x
  have hnormb : @Measurable (Point d) ℝ (nativeSpace d) _ (fun z => ‖z‖) := by
    letI : MeasurableSpace (Point d) := nativeSpace d
    exact measurable_norm
  have hnorm : Measurable (fun z : Point d => ‖z‖) :=
    hnormb.mono (native_borel_le d) le_rfl
  have hset : MeasurableSet {y : Point d | R ≤ ‖x-y‖} :=
    measurableSet_le measurable_const (hnorm.comp hsub.measurable)
  have hkpow (z : Point d) : ENNReal.ofReal (k z) ^ t = ENNReal.ofReal (g z) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (hkn z) hpt.symm.nonneg]
    by_cases hz : R ≤ ‖z‖
    · simp only [k, g, indicator_apply, mem_setOf_eq, if_pos hz, kernel, kernelValue]
      rw [← Real.rpow_mul (norm_nonneg _)]
    · simp only [k, g, indicator_apply, mem_setOf_eq, if_neg hz,
        Real.zero_rpow hpt.symm.ne_zero]
  have hmoment : (∫⁻ y, ENNReal.ofReal (k (x-y)) ^ t ∂μ d) =
      ENNReal.ofReal (R ^ (s + (d : ℝ)) * A) := by
    simp_rw [hkpow]
    rw [hsub.lintegral_comp hgm.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hgn)]
    congr 1
    exact tail_rpow_integral s R hR
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpt.pos
  have hN : (∫⁻ y, ‖f y‖ₑ ^ p ∂μ d) ^ (1 / p) =
      eLpNorm f (ENNReal.ofReal p) (μ d) := by
    symm
    simpa only [ENNReal.toReal_ofReal hpt.nonneg] using
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable
  have hexp : (s + (d : ℝ)) * (1 / t) = α - (d : ℝ) / p := by
    calc
      _ = α - (d : ℝ) + (d : ℝ) * (1 / t) := by
        dsimp [s]
        field_simp [hpt.symm.ne_zero]
        <;> ring
      _ = _ := by
        rw [show 1 / t = 1 - 1 / p by linarith [hpt.one_div_add_one_div]]
        ring
  calc
    _ = ∫⁻ y, ENNReal.ofReal (k (x-y)) * ‖f y‖ₑ ∂μ d := by
      rw [← lintegral_indicator (μ := μ d) hset
        (fun y => ENNReal.ofReal (kernel α (x-y) * ‖f y‖))]
      apply lintegral_congr
      intro y
      by_cases hy : R ≤ ‖x-y‖
      · simp only [k, indicator_apply, mem_setOf_eq, if_pos hy,
          ENNReal.ofReal_mul (kernel_nonneg α _), ofReal_norm]
      · simp only [k, indicator_apply, mem_setOf_eq, if_neg hy, ENNReal.ofReal_zero, zero_mul]
    _ ≤ (∫⁻ y, ENNReal.ofReal (k (x-y)) ^ t ∂μ d) ^ (1 / t) *
        (∫⁻ y, ‖f y‖ₑ ^ p ∂μ d) ^ (1 / p) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq (μ d) hpt.symm
        ((hkm.comp hsub.measurable).ennreal_ofReal.aemeasurable) hf.aestronglyMeasurable.enorm
    _ = _ := by
      rw [hmoment, hN, ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (Real.rpow_nonneg hR.le _) hAn) hpt.symm.one_div_nonneg]
      congr 2
      rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) hAn,
        ← Real.rpow_mul hR.le, hexp, mul_comm]

lemma far_kernel_bound (α p : ℝ) (hα : 0 < α) (hp : 1 < p)
    (hpd : p < (d : ℝ) / α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
      (f : Point d → 𝕜), MemLp f (ENNReal.ofReal p) (μ d) →
      ∀ (x : Point d) (R : ℝ), 0 < R →
      (∫⁻ y in {y : Point d | R ≤ ‖x-y‖},
        ENNReal.ofReal (kernel α (x-y) * ‖f y‖) ∂μ d) ≤
        ENNReal.ofReal (C * R ^ (α - (d : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) (μ d) := by
  let t := Real.conjExponent p
  have hpt : p.HolderConjugate t := Real.HolderConjugate.conjExponent hp
  have hs : (α - (d : ℝ)) * t < -(d : ℝ) := by
    rw [hpt.conjugate_eq, ← mul_div_assoc, div_lt_iff₀ hpt.sub_one_pos]
    have hpa : p * α < (d : ℝ) := (lt_div_iff₀ hα).mp hpd
    nlinarith
  refine ⟨(∫ z : Point d, ({z : Point d | 1 ≤ ‖z‖}).indicator
    (fun z => ‖z‖ ^ ((α - (d : ℝ)) * t)) z ∂μ d) ^ (1 / t), ?_, ?_⟩
  · exact Real.rpow_nonneg (integral_nonneg fun z =>
      indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z) _
  · intro 𝕜 _ _ _ f hf x R hR
    exact far_kernel_holder α p t hpt hs hf x R hR


lemma absolutePotential_eq_near_add_far (α : ℝ) (f : Point d → 𝕜) (x : Point d) (R : ℝ) :
    absolutePotential α f x =
      (∫⁻ y in ball x R, ENNReal.ofReal (kernel α (x-y) * ‖f y‖) ∂μ d) +
      ∫⁻ y in {y | R ≤ ‖x-y‖}, ENNReal.ofReal (kernel α (x-y) * ‖f y‖) ∂μ d := by
  have hc : (ball x R)ᶜ = {y : Point d | R ≤ ‖x-y‖} := by
    ext y
    simp only [mem_compl_iff, mem_ball, dist_eq_norm, mem_ofPred_eq, not_lt]
    rw [norm_sub_rev]
  change (∫⁻ y, ENNReal.ofReal (kernel α (x-y) * ‖f y‖) ∂μ d) = _
  simpa only [hc] using (lintegral_add_compl (μ := μ d)
    (fun y => ENNReal.ofReal (kernel α (x-y) * ‖f y‖)) (ball_measurable x R)).symm

lemma ball_mass_le (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (x : Point d) (r : ℝ) (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂lebesgue d) ≤
      lebesgue d (ball x r) *
        Specs.P102.U2.MaximalWeak.centered_value f x := by
  have hb := P102.U2.MaximalStrong.ofReal_ballAverage_eq f hf r hr x
  have hc : ENNReal.ofReal (P102.U2.MaximalWeak.ballAverage f r x) ≤
      Specs.P102.U2.MaximalWeak.centered_value f x :=
    le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  rw [hb] at hc
  exact (ENNReal.div_le_iff (ball_measure x r hr).1.ne'
    (ball_measure x r hr).2.1.ne).mp hc |>.trans_eq (mul_comm _ _)

lemma ball_scale (x : Point d) (r : ℝ) (hr : 0 < r) :
    lebesgue d (ball x r) =
      ENNReal.ofReal (r ^ (d : ℝ)) *
        lebesgue d (ball (0 : Point d) 1) := by
  change lebesgue d (ball x r) = ENNReal.ofReal (r ^ (d : ℝ)) * lebesgue d (ball (0 : Point d) 1)
  rw [lebesgue_eq_volume d (ball x r), lebesgue_eq_volume d (ball (0 : Point d) 1)]
  exact native_ball_scale x r hr

lemma kernel_le_tsum_balls (α : ℝ) (hαd : α < d) (R : ℝ) (hR : 0 < R)
    (z : Point d) (hz : ‖z‖ < R) :
    ENNReal.ofReal (kernel α z) ≤
      ∑' n : ℕ, (ball (0 : Point d) (2 * R * (1 / 2 : ℝ) ^ n)).indicator
        (fun _ => ENNReal.ofReal ((R * (1 / 2 : ℝ) ^ (n + 1)) ^ (α - (d : ℝ)))) z := by
  by_cases hz0 : z = 0
  · subst z
    have hs : α - (d : ℝ) ≠ 0 := by linarith
    simp only [kernel, P102.U2.RieszPotentialsSpec.kernelValue, norm_zero,
      Real.zero_rpow hs, ENNReal.ofReal_zero]
    exact bot_le
  have ht : 0 < ‖z‖ / R := div_pos (norm_pos_iff.mpr hz0) hR
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one ht
    ((div_le_one hR).mpr hz.le) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hlo : R * (1 / 2 : ℝ) ^ (n + 1) < ‖z‖ := by
    simpa only [mul_comm] using (lt_div_iff₀ hR).mp hnlo
  have hhi : ‖z‖ ≤ R * (1 / 2 : ℝ) ^ n := by
    exact (div_le_iff₀ hR).mp hnhi |>.trans_eq (mul_comm _ _)
  have hb : z ∈ ball (0 : Point d) (2 * R * (1 / 2 : ℝ) ^ n) := by
    simp only [mem_ball, dist_zero_right]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
  calc
    _ ≤ ENNReal.ofReal ((R * (1 / 2 : ℝ) ^ (n + 1)) ^ (α - (d : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hlo.le (by linarith)
    _ = (ball (0 : Point d) (2 * R * (1 / 2 : ℝ) ^ n)).indicator
        (fun _ => ENNReal.ofReal ((R * (1 / 2 : ℝ) ^ (n + 1)) ^ (α - (d : ℝ)))) z :=
      by rw [indicator_of_mem hb]
    _ ≤ _ := ENNReal.le_tsum (f := fun n : ℕ =>
      (ball (0 : Point d) (2 * R * (1 / 2 : ℝ) ^ n)).indicator
        (fun _ => ENNReal.ofReal ((R * (1 / 2 : ℝ) ^ (n + 1)) ^ (α - (d : ℝ)))) z) n

lemma shell_weight (α R : ℝ) (hR : 0 < R) (n : ℕ) :
    (R * (1 / 2 : ℝ) ^ (n + 1)) ^ (α - (d : ℝ)) *
      (2 * R * (1 / 2 : ℝ) ^ n) ^ (d : ℝ) =
      (R ^ α * ((1 / 2 : ℝ) ^ (α - (d : ℝ)) * 2 ^ (d : ℝ))) *
        ((1 / 2 : ℝ) ^ α) ^ n := by
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  rw [pow_succ, show R * ((1 / 2 : ℝ) ^ n * (1 / 2)) =
      (R * (1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ n by ring]
  rw [Real.mul_rpow (show 0 ≤ R * (1 / 2 : ℝ) by positivity)
      (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity),
    Real.mul_rpow (show 0 ≤ 2 * R by positivity)
      (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity),
    Real.mul_rpow hR.le hh.le, Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hR.le]
  have hp : ((1 / 2 : ℝ) ^ n) ^ (α - (d : ℝ)) *
      ((1 / 2 : ℝ) ^ n) ^ (d : ℝ) = ((1 / 2 : ℝ) ^ α) ^ n := by
    rw [← Real.rpow_add (pow_pos hh n), sub_add_cancel,
      ← Real.rpow_natCast_mul hh.le, mul_comm (n : ℝ) α,
      Real.rpow_mul_natCast hh.le]
  have hRp : R ^ (α - (d : ℝ)) * R ^ (d : ℝ) = R ^ α := by
    rw [← Real.rpow_add hR, sub_add_cancel]
  calc
    _ = (R ^ (α - (d : ℝ)) * R ^ (d : ℝ)) *
        ((1 / 2 : ℝ) ^ (α - (d : ℝ)) * 2 ^ (d : ℝ)) *
        (((1 / 2 : ℝ) ^ n) ^ (α - (d : ℝ)) * ((1 / 2 : ℝ) ^ n) ^ (d : ℝ)) := by ring
    _ = _ := by rw [hRp, hp]

lemma near_le_series (α : ℝ) (hαd : α < d)
    (f : Point d → 𝕜) (hf : locallyIntegrable f) (x : Point d)
    (R : ℝ) (hR : 0 < R) :
    (∫⁻ y in ball x R, ENNReal.ofReal (kernel α (x-y) * ‖f y‖)
      ∂lebesgue d) ≤
      (∑' n : ℕ, ENNReal.ofReal ((R * (1 / 2 : ℝ) ^ (n+1)) ^ (α - (d : ℝ))) *
        ENNReal.ofReal ((2 * R * (1 / 2 : ℝ) ^ n) ^ (d : ℝ))) *
      lebesgue d (ball (0 : Point d) 1) *
      Specs.P102.U2.MaximalWeak.centered_value f x := by
  let rad (n : ℕ) : ℝ := 2 * R * (1 / 2 : ℝ) ^ n
  let c (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((R * (1 / 2 : ℝ) ^ (n+1)) ^ (α - (d : ℝ)))
  let F (n : ℕ) (y : Point d) : ℝ≥0∞ := (ball x (rad n)).indicator
    (fun y => c n * ‖f y‖ₑ) y
  have hrad (n : ℕ) : 0 < rad n := by dsimp [rad]; positivity
  have hF (n : ℕ) : Measurable (F n) :=
    (hf.1.enorm.const_mul (c n)).indicator (ball_measurable x (rad n))
  have hpoint (y : Point d) :
      (ball x R).indicator (fun y => ENNReal.ofReal (kernel α (x-y) * ‖f y‖)) y ≤
        ∑' n, F n y := by
    by_cases hy : y ∈ ball x R
    · rw [indicator_of_mem hy, ENNReal.ofReal_mul (kernel_nonneg _ _), ofReal_norm]
      have hnorm : ‖x-y‖ < R := by simpa only [mem_ball, ← dist_eq_norm, dist_comm] using hy
      have hle := mul_le_mul' (kernel_le_tsum_balls α hαd R hR (x-y) hnorm) (le_refl ‖f y‖ₑ)
      rw [← ENNReal.tsum_mul_right] at hle
      apply hle.trans_eq
      apply tsum_congr
      intro n
      have hb : x-y ∈ ball (0 : Point d) (rad n) ↔ y ∈ ball x (rad n) := by
        simp only [mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]
      change (ball (0 : Point d) (rad n)).indicator (fun _ => c n) (x-y) * ‖f y‖ₑ = F n y
      by_cases hn : y ∈ ball x (rad n)
      · simp only [F, indicator_of_mem hn, indicator_of_mem (hb.mpr hn)]
      · simp only [F, indicator_of_notMem hn, indicator_of_notMem (mt hb.mp hn), zero_mul]
    · rw [indicator_of_notMem hy]
      exact bot_le
  calc
    _ = ∫⁻ y, (ball x R).indicator
        (fun y => ENNReal.ofReal (kernel α (x-y) * ‖f y‖)) y
        ∂lebesgue d := (lintegral_indicator (ball_measurable x R) _).symm
    _ ≤ ∫⁻ y, ∑' n, F n y ∂lebesgue d := lintegral_mono hpoint
    _ = ∑' n, ∫⁻ y, F n y ∂lebesgue d :=
      lintegral_tsum fun n => (hF n).aemeasurable
    _ ≤ ∑' n, c n * (lebesgue d (ball x (rad n)) *
        Specs.P102.U2.MaximalWeak.centered_value f x) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [show F n = (ball x (rad n)).indicator (fun y => c n * ‖f y‖ₑ) from rfl,
        lintegral_indicator (ball_measurable x (rad n)),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (ball_mass_le f hf x (rad n) (hrad n))
    _ = _ := by
      simp_rw [ball_scale x (rad _) (hrad _)]
      simp only [rad, c]
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

theorem near_kernel_bound (α : ℝ) (hα : 0 < α) (hαd : α < d) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
        (f : Point d → 𝕜), locallyIntegrable f → ∀ (x : Point d) (R : ℝ), 0 < R →
          (∫⁻ y in ball x R, ENNReal.ofReal (kernel α (x-y) * ‖f y‖) ∂lebesgue d) ≤
            ENNReal.ofReal (A * R ^ α) * Specs.P102.U2.MaximalWeak.centered_value f x := by
  let g : ℝ := (1 / 2 : ℝ) ^ α
  let K : ℝ := (1 / 2 : ℝ) ^ (α - (d : ℝ)) * 2 ^ (d : ℝ)
  let V : ℝ≥0∞ := lebesgue d (ball (0 : Point d) 1)
  have hg0 : 0 ≤ g := Real.rpow_nonneg (by norm_num) _
  have hg1 : g < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV : V ≠ ∞ := (ball_measure (0 : Point d) 1 (by norm_num)).2.1.ne
  let A : ℝ := K * V.toReal / (1 - g)
  refine ⟨A, div_nonneg (mul_nonneg hK ENNReal.toReal_nonneg) (sub_nonneg.mpr hg1.le), ?_⟩
  intro 𝕜 _ _ _ f hf x R hR
  have hnear := near_le_series α hαd f hf x R hR
  have hterm (n : ℕ) :
      ENNReal.ofReal ((R * (1 / 2 : ℝ) ^ (n+1)) ^ (α - (d : ℝ))) *
        ENNReal.ofReal ((2 * R * (1 / 2 : ℝ) ^ n) ^ (d : ℝ)) =
        ENNReal.ofReal (R ^ α * K) * ENNReal.ofReal g ^ n := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), shell_weight α R hR]
    rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hR.le _) hK), ENNReal.ofReal_pow hg0]
  simp_rw [hterm] at hnear
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric] at hnear
  have hden : ENNReal.ofReal ((1 - g)⁻¹) = (1 - ENNReal.ofReal g)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hg1), ENNReal.ofReal_sub _ hg0]
    norm_num
  apply hnear.trans_eq
  rw [← hden]
  change ENNReal.ofReal (R ^ α * K) * ENNReal.ofReal ((1 - g)⁻¹) * V *
    Specs.P102.U2.MaximalWeak.centered_value f x =
    ENNReal.ofReal (A * R ^ α) * Specs.P102.U2.MaximalWeak.centered_value f x
  rw [← ENNReal.ofReal_toReal hV]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hR.le _) hK),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (Real.rpow_nonneg hR.le _) hK)
      (inv_nonneg.mpr (sub_nonneg.mpr hg1.le)))]
  congr 2
  dsimp [A]
  ring


/-- The strong HLS estimate, obtained from the actual near/far absolute integrals
and the centered maximal strong estimate. -/
theorem strong_bound : RieszPotentialsSpec.StrongBound := by
  intro d _ α hα hαd p q hp hpd hrel
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hαb : α < (d : ℝ) / p := by
    apply (lt_div_iff₀ hp0).mpr
    have hpa := (lt_div_iff₀ hα).mp hpd
    nlinarith
  obtain ⟨hq, hexp⟩ := exponent_identity α p q hα hp hpd hrel
  have hpq : q * (1-α/((d : ℝ)/p)) = p := by
    simpa only [div_div_eq_mul_div] using hexp
  obtain ⟨A, hA, hnear⟩ := near_kernel_bound (d := d) α hα hαd
  obtain ⟨B, hB, hfar⟩ := far_kernel_bound (d := d) α p hα hp hpd
  obtain ⟨D, hD⟩ := MaximalStrong.finiteStrongBound d p hp
  let C : ℝ≥0 := ⟨(A+B) * (D : ℝ) ^ (1-α/((d : ℝ)/p)), by positivity⟩
  refine ⟨C, ?_⟩
  intro 𝕜 _ _ _ f hf
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hfl := MaximalStrong.localIntegrability (ENNReal.ofReal p) hp1 f hf
  have hm := (MaximalWeak.measurable_maximal f hfl).1
  have hmax := hD false f hf
  have hscale : ∀ x R, 0 < R → absolutePotential α f x ≤
      ENNReal.ofReal (A * R ^ α) * Specs.P102.U2.MaximalWeak.centered_value f x +
      ENNReal.ofReal (B * R ^ (α - (d : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) (μ d) := by
    intro x R hR
    rw [absolutePotential_eq_near_add_far α f x R]
    exact add_le_add (hnear f hfl x R hR) (hfar f hf x R hR)
  have hmoment := ScaleTransfer.scale_to_moment (μ d) (absolutePotential α f)
    (Specs.P102.U2.MaximalWeak.centered_value f) hm.aemeasurable
    α ((d : ℝ)/p) A B (D : ℝ) p q hα hαb hA hB D.coe_nonneg hp0 hq hpq
    (eLpNorm f (ENNReal.ofReal p) (μ d)) hf.ne
    (by simpa only [MaximalStrongSpec.maximalValue, Bool.false_eq_true, ite_false] using hmax.2.1)
    hscale
    (by simpa only [MaximalStrongSpec.maximalValue, Bool.false_eq_true, ite_false,
      ENNReal.ofReal_coe_nnreal] using hmax.1)
  have hb : (∫⁻ x, absolutePotential α f x ^ q ∂μ d) ^ (1/q) ≤
      (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (μ d) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := C)]
    exact hmoment
  exact potential_membership_of_absoluteMoment α q hq hf.aestronglyMeasurable _
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hf) hb

theorem endpoint_absoluteExistence : RieszPotentialsSpec.EndpointAbsoluteExistence := by
  intro d _ 𝕜 _ _ _ α hα hαd f hf
  exact ae_integrable_of_integrable α hα hαd hf

/-- The weak endpoint for the actual Riesz integral, including its absolute
existence and measurability conclusions. -/
theorem weak_endpoint : RieszPotentialsSpec.WeakEndpoint := by
  intro d _ α hα hαd
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  let q := (d : ℝ) / ((d : ℝ) - α)
  have hq : 0 < q := div_pos hd (by linarith)
  let A := ∫ z : Point d, (Metric.ball 0 1).indicator (kernel α) z ∂μ d
  have hA : 0 ≤ A := integral_nonneg fun z =>
    indicator_nonneg (fun z _ => kernel_nonneg α z) z
  let C : ℝ≥0 := ⟨2 * A ^ (1 / q), by positivity⟩
  refine ⟨C, ?_⟩
  intro 𝕜 _ _ _ f hf
  refine ⟨ae_integrable_of_integrable α hα hαd hf,
    (measurability α f hf.aestronglyMeasurable).1, ?_⟩
  let N := ∫ y, ‖f y‖ ∂μ d
  have hN : 0 ≤ N := integral_nonneg fun y => norm_nonneg _
  have hinput : eLpNorm f 1 (μ d) = ENNReal.ofReal N := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact (ofReal_integral_norm_eq_lintegral_enorm hf).symm
  change P102.U2.weakSize (μ d) q (potential α f) ≤ _
  rcases eq_or_lt_of_le hN with hNz | hNp
  · have hz : (fun y => ‖f y‖) =ᵐ[μ d] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => norm_nonneg (f y)) hf.norm).mp hNz.symm
    have hfz : f =ᵐ[μ d] 0 := hz.mono fun y hy => norm_eq_zero.mp hy
    have he := (representative_independence α f 0 hfz).1
    have hpz : potential α f = 0 := by
      funext x
      change potentialValue α f x = 0
      rw [he]
      simp [potentialValue]
    rw [hpz]
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    simp only [P102.U2.distribution, Pi.zero_apply, norm_zero]
    simp [show ¬ t < 0 from ht.not_gt, ENNReal.zero_rpow_of_pos (inv_pos.mpr hq)]
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    have hu : 0 < 2 * N / t := by positivity
    have hb := endpoint_distribution α hα hαd hf hNp t ht
    change P102.U2.distribution (μ d) (potential α f) t ≤
      ENNReal.ofReal (A * (2 * N / t) ^ q) at hb
    calc
      ENNReal.ofReal t * P102.U2.distribution (μ d) (potential α f) t ^ (1 / q) ≤
          ENNReal.ofReal t * ENNReal.ofReal (A * (2 * N / t) ^ q) ^ (1 / q) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hb (by positivity))
      _ = ENNReal.ofReal (2 * A ^ (1 / q) * N) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← ENNReal.ofReal_mul ht.le]
        congr 1
        rw [Real.mul_rpow hA (Real.rpow_nonneg hu.le _), ← Real.rpow_mul hu.le,
          show q * (1 / q) = 1 by field_simp, Real.rpow_one]
        field_simp
      _ = (C : ℝ≥0∞) * eLpNorm f 1 (μ d) := by
        rw [hinput, ← ENNReal.ofReal_coe_nnreal (p := C),
          ← ENNReal.ofReal_mul (show 0 ≤ (C : ℝ) from C.coe_nonneg)]
        rfl

end Measurability
end P102.U2.RieszPotentials
