import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZLp
import MathGenome.Internal.FourierSobolev.P102.U2.Marcinkiewicz
import MathGenome.Internal.FourierSobolev.P102.U2.CZWeakExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundLp
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace P102.U2.CZLp
open CZWeak CZLpData

/-- The mean-value argument uses only the derivative bound. In particular it
does not require the additional size bound of `StandardKernel`. -/
theorem kernel_difference_of_gradient {d : ℕ} (K : Point d → ℂ) (B : ℝ≥0)
    (hK : ContDiffOn ℝ 1 K ({0}ᶜ : Set (Point d)))
    (hB : ∀ z ≠ 0, gradientNorm K z ≤ (B : ℝ) / ‖z‖ ^ (d + 1))
    (a h : Point d) (ha : a ≠ 0) (hh : ‖h‖ ≤ ‖a‖ / 2) :
    ‖K (a - h) - K a‖ ≤
      ((d : ℝ) * B * 2 ^ (d + 1)) * ‖h‖ / ‖a‖ ^ (d + 1) := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let D := Metric.closedBall a (‖a‖ / 2)
  have hnorm (z : Point d) (hz : z ∈ D) : ‖a‖ / 2 ≤ ‖z‖ := by
    have hz' : ‖z - a‖ ≤ ‖a‖ / 2 := by simpa [D, dist_eq_norm] using hz
    have ht : ‖a‖ ≤ ‖z - a‖ + ‖z‖ := by
      calc
        ‖a‖ = ‖(a - z) + z‖ := by congr 1; abel
        _ ≤ ‖a - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z - a‖ + ‖z‖ := by rw [norm_sub_rev a z]
    linarith
  have hne (z : Point d) (hz : z ∈ D) : z ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by linarith) (hnorm z hz))
  have hd (z : Point d) (hz : z ∈ D) : DifferentiableAt ℝ K z :=
    (hK.differentiableOn (by norm_num) z (hne z hz)).differentiableAt
      (isClosed_singleton.isOpen_compl.mem_nhds (hne z hz))
  have hb (z : Point d) (hz : z ∈ D) :
      ‖fderiv ℝ K z‖ ≤ (d : ℝ) * B / (‖a‖ / 2) ^ (d + 1) := by
    calc
      ‖fderiv ℝ K z‖ ≤ (d : ℝ) * gradientNorm K z :=
        ExpandedFA.SingularIntegrals.CZWeak.fderiv_norm_le_gradient _ _
      _ ≤ (d : ℝ) * ((B : ℝ) / ‖z‖ ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left (hB z (hne z hz)) (Nat.cast_nonneg _)
      _ ≤ (d : ℝ) * ((B : ℝ) / (‖a‖ / 2) ^ (d + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
        exact div_le_div_of_nonneg_left B.coe_nonneg (by positivity)
          (pow_le_pow_left₀ (by positivity) (hnorm z hz) _)
      _ = _ := by ring
  have hma : a ∈ D := Metric.mem_closedBall_self (by positivity)
  have hmh : a - h ∈ D := by simpa [D, dist_eq_norm] using hh
  have hv := Convex.norm_image_sub_le_of_norm_fderiv_le hd hb (convex_closedBall a _) hma hmh
  have heq : ‖a - h - a‖ = ‖h‖ := by rw [sub_right_comm, sub_self, zero_sub, norm_neg]
  rw [heq] at hv
  calc
    ‖K (a - h) - K a‖ ≤ (d : ℝ) * B / (‖a‖ / 2) ^ (d + 1) * ‖h‖ := hv
    _ = _ := by rw [div_pow]; field_simp

/-- Explicit dimension constant from the radial integral. -/
def smoothConstant (d : ℕ) : ℝ≥0 :=
  ⟨(d : ℝ) ^ 2 * 2 ^ d * volume.real (Metric.ball (0 : Point d) 1), by positivity⟩

theorem smooth_difference_bound {d : ℕ} (hd : 0 < d)
    (K : Point d → ℂ) (B : ℝ≥0)
    (hK : ContDiffOn ℝ 1 K ({0}ᶜ : Set (Point d)))
    (hB : ∀ z ≠ 0, gradientNorm K z ≤ (B : ℝ) / ‖z‖ ^ (d + 1)) :
    DifferenceBound K (smoothConstant d * B) := by
  intro h hh
  have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  let E : Set (Point d) := {z | 2 * ‖h‖ < ‖z‖}
  let W : Point d → ℝ := fun z =>
    (Ioi (2 * ‖h‖)).indicator (fun r : ℝ => 1 / r ^ (d + 1)) ‖z‖
  have hE : MeasurableSet E := measurableSet_lt measurable_const continuous_norm.measurable
  obtain ⟨hi, he⟩ := ExpandedFA.SingularIntegrals.CZWeak.radial_tail hd
    (2 * ‖h‖) (by positivity)
  let c : ℝ := (d : ℝ) * B * 2 ^ (d + 1) * ‖h‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hW (z : Point d) : 0 ≤ W z := by
    simp only [W, Set.indicator_apply]
    split_ifs <;> positivity
  have hi' : Integrable (fun z => c * W z) volume := hi.const_mul c
  change (∫⁻ z in E, ‖K (z - h) - K z‖ₑ) ≤ _
  rw [← lintegral_indicator hE]
  calc
    (∫⁻ z, E.indicator (fun z => ‖K (z - h) - K z‖ₑ) z) ≤
        ∫⁻ z, ‖c * W z‖ₑ := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ E
      · simp only [indicator_of_mem hz, ← ofReal_norm]
        rw [Real.norm_of_nonneg (mul_nonneg hc (hW z))]
        apply ENNReal.ofReal_le_ofReal
        have hz' : 2 * ‖h‖ < ‖z‖ := hz
        have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
        have hv := kernel_difference_of_gradient K B hK hB z h hz0 (by linarith)
        simpa [c, W, indicator_of_mem (show ‖z‖ ∈ Ioi (2 * ‖h‖) from hz'),
          div_eq_mul_inv, mul_assoc] using hv
      · rw [indicator_of_notMem hz]
        exact zero_le
    _ = ENNReal.ofReal (∫ z, c * W z) :=
      (ofReal_integral_norm_eq_lintegral_enorm hi').symm.trans
        (congrArg ENNReal.ofReal (integral_congr_ae (Eventually.of_forall
          (fun z => Real.norm_of_nonneg (mul_nonneg hc (hW z))))))
    _ = ENNReal.ofReal ((smoothConstant d : ℝ) * B) := by
      congr 1
      rw [integral_const_mul, show (∫ z, W z) =
        (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / (2 * ‖h‖) from he]
      change c * ((d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / (2 * ‖h‖)) =
        ((d : ℝ) ^ 2 * 2 ^ d * volume.real (Metric.ball (0 : Point d) 1)) * B
      dsimp only [c]
      rw [pow_succ (2 : ℝ) d]
      field_simp
    _ = _ := by simp only [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
        ENNReal.coe_mul]

/-- The gradient sufficient condition, with no endpoint premises. -/
theorem smooth_difference :
    Specs.P102.U2.CZLp.smooth_difference := by
  exact ⟨smoothConstant, fun _ hd K B hK hB => smooth_difference_bound hd K B hK hB⟩

/-- Agreement on the triple core passes to the entire pairwise intersection.
This lemma has no kernel assumptions. -/
theorem bounded_extensions_agree {d : ℕ} (T : Operator d)
    (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]
    (hpTop : p ≠ ∞) (hqTop : q ≠ ∞)
    (S : Space d p →L[ℂ] Space d p) (R : Space d q →L[ℂ] Space d q)
    (hS : ∀ (f : Point d → ℂ) (_h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume)
      (h : MemLp f p volume), (S (h.toLp f) : Point d → ℂ) =ᵐ[volume]
        (T (h2.toLp f) : Point d → ℂ))
    (hR : ∀ (f : Point d → ℂ) (_h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume)
      (h : MemLp f q volume), (R (h.toLp f) : Point d → ℂ) =ᵐ[volume]
        (T (h2.toLp f) : Point d → ℂ))
    (f : Point d → ℂ) (hfp : MemLp f p volume) (hfq : MemLp f q volume) :
    (S (hfp.toLp f) : Point d → ℂ) =ᵐ[volume] (R (hfq.toLp f) : Point d → ℂ) := by
  let g : Point d → ℂ := hfp.toLp f
  have hgp : MemLp g p volume := Lp.memLp _
  have hgq : MemLp g q volume := (memLp_congr_ae hfp.coeFn_toLp).mpr hfq
  obtain ⟨u, hu, hconv⟩ := ExpandedFA.SingularIntegrals.CZLp.simultaneous_simple_approx
    volume g (Lp.stronglyMeasurable (hfp.toLp f)).measurable
    (zero_lt_one.trans_le hp.out).ne' hpTop hgp
  have hep : hgp.toLp g = hfp.toLp f := hgp.toLp_congr hfp hfp.coeFn_toLp
  have heq : hgq.toLp g = hfq.toLp f := hgq.toLp_congr hfq hfp.coeFn_toLp
  have hup := S.continuous.tendsto (hgp.toLp g) |>.comp (hconv p hpTop hgp)
  have huq := R.continuous.tendsto (hgq.toLp g) |>.comp (hconv q hqTop hgq)
  rw [hep] at hup
  rw [heq] at huq
  have he (n : ℕ) :
      (S ((hu n p).toLp (u n)) : Point d → ℂ) =ᵐ[volume]
        (R ((hu n q).toLp (u n)) : Point d → ℂ) :=
    (hS (u n) (hu n 1) (hu n 2) (hu n p)).trans
      (hR (u n) (hu n 1) (hu n 2) (hu n q)).symm
  exact tendstoInMeasure_ae_unique
    ((tendstoInMeasure_of_tendsto_Lp hup).congr_left he)
    (tendstoInMeasure_of_tendsto_Lp huq)

/-- The same approximation identifies the strong and weak actions on the
whole L¹/Lᵖ intersection. Measure continuity is supplied by the proved endpoint
result, rather than being assumed of an arbitrary weak operator. -/
theorem strong_weak_agree {d : ℕ} (T : Operator d) (p : Exponent)
    (R : StrongOperator d p) (hR : Agrees T p R)
    (S : Extension d) (hS : Compatible T S) (hcont : MeasureContinuous S)
    (f : Point d → ℂ) (hfp : MemLp f p.val volume) (hf1 : MemLp f 1 volume) :
    (R (hfp.toLp f) : Point d → ℂ) =ᵐ[volume] (S (hf1.toLp f) : Point d → ℂ) := by
  let g : Point d → ℂ := hfp.toLp f
  have hgp : MemLp g p.val volume := Lp.memLp _
  have hg1 : MemLp g 1 volume := (memLp_congr_ae hfp.coeFn_toLp).mpr hf1
  obtain ⟨u, hu, hconv⟩ := ExpandedFA.SingularIntegrals.CZLp.simultaneous_simple_approx
    volume g (Lp.stronglyMeasurable (hfp.toLp f)).measurable
    (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne hgp
  have hep : hgp.toLp g = hfp.toLp f := hgp.toLp_congr hfp hfp.coeFn_toLp
  have he1 : hg1.toLp g = hf1.toLp f := hg1.toLp_congr hf1 hfp.coeFn_toLp
  have hup := R.continuous.tendsto (hgp.toLp g) |>.comp (hconv p.val p.lt_top.ne hgp)
  have huw := hcont (fun n => (hu n 1).toLp (u n)) (hg1.toLp g) (hconv 1 (by simp) hg1)
  rw [hep] at hup
  rw [he1] at huw
  have he (n : ℕ) :
      (R ((hu n p.val).toLp (u n)) : Point d → ℂ) =ᵐ[volume]
        (S ((hu n 1).toLp (u n)) : Point d → ℂ) := by
    have heq := hS (u n) (hu n 1) (hu n 2)
    have hae : (S ((hu n 1).toLp (u n)) : Point d → ℂ) =ᵐ[volume]
        (T ((hu n 2).toLp (u n)) : Point d → ℂ) := by
      exact AEEqFun.ext_iff.mp heq
    exact (hR (u n) (hu n p.val) (hu n 2)).trans hae.symm
  exact tendstoInMeasure_ae_unique
    ((tendstoInMeasure_of_tendsto_Lp hup).congr_left he) huw

/-- Quantitative interpolation below two. The constant is chosen before
the dimension and the operator, so its only inputs are p and the endpoint
bounds. Agreement holds on the full L²/Lᵖ intersection. -/
theorem low_extension_of_core (p : Exponent) (hp2 : p.val < 2) (C₁ C₂ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (d : ℕ) (T : Operator d), CoreBound T C₁ → ‖T‖₊ ≤ C₂ →
      ∃ R : StrongOperator d p, ‖R‖ ≤ C ∧ Agrees T p R := by
  open ExpandedFA.Interpolation ExpandedFA.Interpolation.MarcinkiewiczSpec in
    obtain ⟨C, hC⟩ := marcinkiewicz_linear_extension 1 2 p.val
      (by rfl) p.one_lt hp2 C₁ C₂
    refine ⟨C, ?_⟩
    intro d T hweak hnorm
    obtain ⟨L, hLm, hLae⟩ := ExpandedFA.SingularIntegrals.CZLp.exists_linear_representatives
      ℂ (volume : Measure (Point d))
    let V := ExpandedFA.SingularIntegrals.CZLp.intersectionToL2 (𝕜 := ℂ) (d := d) p.val
    let W : intersectionCore (volume : Measure (Point d)) 1 2 p.val →ₗ[ℂ] Classes d :=
      (lpEmbed 2).comp (T.toLinearMap.comp V)
    let U := L.comp W
    have hae (f : intersectionCore (volume : Measure (Point d)) 1 2 p.val) :
        U f =ᵐ[volume] (T (V f) : Point d → ℂ) := hLae (W f)
    have hw1 (f : intersectionCore (volume : Measure (Point d)) 1 2 p.val) :
        endpointEstimate volume volume 1 C₁ (f.val : Point d → ℂ) (U f) := by
      apply ExpandedFA.SingularIntegrals.CZLp.endpoint_one_of_weak _ _ _ C₁
      intro t ht
      change ExpandedFA.Interpolation.MarcinkiewiczSpec.distribution volume (U f) t ≤ _
      rw [distribution_congr_ae (hae f)]
      exact hweak f.val f.property.1 f.property.2 t ht
    have hw2 (f : intersectionCore (volume : Measure (Point d)) 1 2 p.val) :
        endpointEstimate volume volume 2 C₂ (f.val : Point d → ℂ) (U f) := by
      apply ExpandedFA.SingularIntegrals.CZLp.endpoint_two _ _ _ f.property.2
        ((memLp_congr_ae (hae f)).mpr (Lp.memLp _))
      rw [eLpNorm_congr_ae (hae f), ← Lp.enorm_def, ← ofReal_norm]
      apply (ENNReal.ofReal_le_ofReal (T.le_opNorm _)).trans
      have hn : ‖T‖ ≤ (C₂ : ℝ) := hnorm
      apply (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hn (norm_nonneg (V f)))).trans_eq
      rw [ENNReal.ofReal_mul C₂.coe_nonneg]
      change ENNReal.ofReal (C₂ : ℝ) * ENNReal.ofReal ‖f.property.2.toLp _‖ = _
      rw [Lp.norm_toLp, ENNReal.ofReal_toReal f.property.2.ne]
      simp only [ENNReal.ofReal_coe_nnreal]
    obtain ⟨R, hR, _⟩ := hC volume volume U (fun f => hLm _) hw1 hw2
    refine ⟨R, hR.1, ?_⟩
    have hcore : ∀ (f : Point d → ℂ) (_h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume)
        (hf : MemLp f p.val volume), (R (hf.toLp f) : Point d → ℂ) =ᵐ[volume]
          (T (h2.toLp f) : Point d → ℂ) := by
      intro f h1 h2 hf
      let a : intersectionCore (volume : Measure (Point d)) 1 2 p.val :=
        ⟨hf.toLp f, (memLp_congr_ae hf.coeFn_toLp).mpr h1,
          (memLp_congr_ae hf.coeFn_toLp).mpr h2⟩
      have he : V a = h2.toLp f := a.property.2.toLp_congr h2 hf.coeFn_toLp
      exact (hR.2 a).trans ((hae a).trans (by rw [he]))
    intro f hf h2
    exact bounded_extensions_agree T p.val 2 p.lt_top.ne (by simp) R T hcore
      (fun _ _ _ _ => Filter.EventuallyEq.rfl) f hf h2

/-- Reflection followed by scalar conjugation, with no smoothness assumption. -/
def adjointKernel {d : ℕ} (K : Point d → ℂ) (z : Point d) : ℂ := star (K (-z))

/-- Reflection and conjugation preserve local integrability away from zero. -/
theorem adjointKernel_locallyIntegrable {d : ℕ} (K : Point d → ℂ)
    (hK : LocallyIntegrableOn K ({0}ᶜ : Set (Point d)) volume) :
    LocallyIntegrableOn (adjointKernel K) ({0}ᶜ : Set (Point d)) volume := by
  have hr : LocallyIntegrableOn (fun z => K (-z)) ({0}ᶜ : Set (Point d)) volume := by
    apply (locallyIntegrableOn_iff isClosed_singleton.isOpen_compl.isLocallyClosed).mpr
    intro S hS hcompact
    have hi : IntegrableOn K ((fun z : Point d => -z) '' S) volume :=
      hK.integrableOn_compact_subset (by
        rintro z ⟨y, hy, rfl⟩
        exact neg_ne_zero.mpr (hS hy)) (hcompact.image continuous_neg)
    have hc := (Measure.measurePreserving_neg (volume : Measure (Point d))).integrableOn_image
      (Homeomorph.neg (Point d)).measurableEmbedding |>.mp hi
    exact hc
  exact RCLike.conjCLE.toContinuousLinearMap.locallyIntegrableOn_comp hr

theorem adjointKernel_difference {d : ℕ} (K : Point d → ℂ) (A : ℝ≥0)
    (hK : DifferenceBound K A) : DifferenceBound (adjointKernel K) A := by
  intro h hh
  have hi := (Measure.measurePreserving_neg (volume : Measure (Point d))).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.neg (Point d)).measurableEmbedding
    (fun z => ‖K (z - (-h)) - K z‖ₑ) {z : Point d | 2 * ‖-h‖ < ‖z‖}
  simp only [preimage_ofPred_eq, norm_neg] at hi
  calc
    (∫⁻ z in {z : Point d | 2 * ‖h‖ < ‖z‖}, ‖adjointKernel K (z - h) - adjointKernel K z‖ₑ) =
        ∫⁻ z in {z : Point d | 2 * ‖h‖ < ‖z‖}, ‖K ((-z) - (-h)) - K (-z)‖ₑ := by
      apply lintegral_congr
      intro z
      simp only [adjointKernel, ← star_sub, ← ofReal_norm, norm_star]
      congr 3
      abel_nf
    _ = ∫⁻ z in {z : Point d | 2 * ‖h‖ < ‖z‖}, ‖K (z - (-h)) - K z‖ₑ := hi
    _ ≤ A := by simpa only [norm_neg] using hK (-h) (neg_ne_zero.mpr hh)

/-- Quantitative duality: a lower-exponent realization of the adjoint gives
an upper-exponent realization of T with the same norm bound. -/
theorem high_extension_of_adjoint_core (p : Exponent) (hp2 : 2 < p.val)
    (C₁ C₂ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (d : ℕ) (T : Operator d),
      CoreBound T.adjoint C₁ → ‖T‖₊ ≤ C₂ →
      ∃ R : StrongOperator d p, ‖R‖ ≤ C ∧ Agrees T p R := by
  let q := ENNReal.conjExponent p.val
  have hq1 : 1 < q :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p.val q).mp p.lt_top
  have hqTop : q < ∞ :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt q p.val).mpr p.one_lt
  have hq2 : q < 2 := by
    have hs : 1 < p.val - 1 :=
      (lt_tsub_iff_right).mpr (by norm_num only [one_add_one_eq_two]; exact hp2)
    change 1 + (p.val - 1)⁻¹ < 2
    have hi : (p.val - 1)⁻¹ < 1 := ENNReal.inv_lt_one.mpr hs
    calc
      1 + (p.val - 1)⁻¹ < 1 + 1 := ENNReal.add_lt_add_left (by norm_num) hi
      _ = 2 := by norm_num
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  let r : Exponent := ⟨q, hq1, hqTop⟩
  obtain ⟨C, hC⟩ := low_extension_of_core r hq2 C₁ C₂
  refine ⟨C, ?_⟩
  intro d T hweak hnorm
  obtain ⟨R, hnormR, hR⟩ := hC d T.adjoint hweak (by simpa using hnorm)
  let S := ExpandedFA.SingularIntegrals.CZLp.dualityTransfer volume p.val q hqTop.ne R
  refine ⟨S, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    intro f
    exact (ExpandedFA.SingularIntegrals.CZLp.dualityTransfer_bound
      volume p.val q hqTop.ne R f).trans
      (mul_le_mul_of_nonneg_right hnormR (norm_nonneg f))
  · exact ExpandedFA.SingularIntegrals.CZLp.dualityTransfer_agrees
      volume p.val q hqTop.ne T R hR


/-- The middle exponent uses the original operator itself. -/
theorem two_extension_of_norm (p : Exponent) (hp : p.val = 2) (C₂ : ℝ≥0) :
    ∀ (d : ℕ) (T : Operator d), ‖T‖₊ ≤ C₂ →
      ∃ R : StrongOperator d p, ‖R‖ ≤ C₂ ∧ Agrees T p R := by
  rcases p with ⟨v, h1, ht⟩
  dsimp only at hp
  subst v
  intro d T hn
  refine ⟨T, hn, ?_⟩
  intro f h2 h2'
  have he : h2.toLp f = h2'.toLp f := rfl
  rw [he]

/-- Both core estimates suffice for all finite strong exponents; the bound
is uniform over dimensions and operators with the specified endpoint bounds. -/
theorem extension_of_two_core_bounds (p : Exponent) (C₁ C₂ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (d : ℕ) (T : Operator d),
      CoreBound T C₁ → CoreBound T.adjoint C₁ → ‖T‖₊ ≤ C₂ →
      ∃ R : StrongOperator d p, ‖R‖ ≤ C ∧ Agrees T p R := by
  rcases lt_trichotomy p.val 2 with hp | hp | hp
  · obtain ⟨C, hC⟩ := low_extension_of_core p hp C₁ C₂
    exact ⟨C, fun d T hw _ hn => hC d T hw hn⟩
  · exact ⟨C₂, fun d T _ _ hn => two_extension_of_norm p hp C₂ d T hn⟩
  · obtain ⟨C, hC⟩ := high_extension_of_adjoint_core p hp C₁ C₂
    exact ⟨C, fun d T _ hw hn => hC d T hw hn⟩

/-- All remaining assembly is reduced to the rough-kernel adjoint theorem.
This premise is an explicitly recorded remaining obligation, not part of the
independent specification of the original theorem. -/
theorem full_extension_of_adjoint
    (hadjoint : ∀ (d : ℕ), 0 < d → ∀ (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0),
      KernelHypotheses T K A → KernelHypotheses T.adjoint (adjointKernel K) A) :
    Specs.P102.U2.CZLp.full_extension := by
  obtain ⟨C₁, hC₁⟩ := CZWeakExtension.weak_extension
  have hex := fun p C₁ C₂ => extension_of_two_core_bounds p C₁ C₂
  choose C hC using hex
  refine ⟨C₁, fun d p A N => C p (C₁ d A N) N, ?_⟩
  intro d hd T K A hK
  obtain ⟨hcore, S, hS, hw, hcont, ha, hu, hsum⟩ := hC₁ d hd T K A hK
  have hadj := (hC₁ d hd T.adjoint (adjointKernel K) A (hadjoint d hd T K A hK)).1
  have hadj' : CoreBound T.adjoint (C₁ d A ‖T‖₊) := by
    simpa using hadj
  have hr (p : Exponent) : ∃ R : StrongOperator d p,
      ‖R‖ ≤ C p (C₁ d A ‖T‖₊) ‖T‖₊ ∧ Agrees T p R :=
    hC p (C₁ d A ‖T‖₊) ‖T‖₊ d T hcore hadj' le_rfl
  choose R hR using hr
  refine ⟨hcore, S, R, hS, hw, hcont, ha, hu, hsum,
    fun p => (hR p).1, fun p => (hR p).2, ?_, ?_⟩
  · intro p q f hp hq
    exact bounded_extensions_agree T p.val q.val p.lt_top.ne q.lt_top.ne (R p) (R q)
      (fun f _ h2 hp => (hR p).2 f hp h2)
      (fun f _ h2 hq => (hR q).2 f hq h2) f hp hq
  · intro p f h1 hp
    exact strong_weak_agree T p (R p) (hR p).2 S hS hcont f hp h1


/-- Local integrability and the reflected difference estimate have already
been proved here, so only the off-support adjoint representation is missing. -/
theorem full_extension_of_adjoint_representation
    (hrep : ∀ (d : ℕ), 0 < d → ∀ (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0),
      KernelHypotheses T K A →
      ∀ (b : Point d → ℂ) (h2 : MemLp b 2 volume) (S : Set (Point d)),
        IsCompact S → (∀ᵐ y ∂volume, y ∉ S → b y = 0) →
        ∀ᵐ x ∂volume, x ∉ S →
          T.adjoint (h2.toLp b) x = ∫ y, star (K (-(x - y))) * b y) :
    Specs.P102.U2.CZLp.full_extension := by
  apply full_extension_of_adjoint
  intro d hd T K A hK
  exact ⟨adjointKernel_locallyIntegrable K hK.locallyIntegrable,
    hrep d hd T K A hK, adjointKernel_difference K A hK.difference⟩


/-- Absolute integrability for the localized adjoint pairing uses L¹ only. -/
theorem integrable_adjoint_convolution_integrand {d : ℕ}
    {k b : Point d → ℂ} (hk : Integrable k volume) (hb : Integrable b volume) :
    Integrable (fun p : Point d × Point d => star (k (p.2 - p.1)) * b p.2)
      (volume.prod volume) := by
  have hr : Integrable (fun z => star (k (-z))) volume := by
    exact RCLike.conjCLE.toContinuousLinearMap.integrable_comp
      hk.comp_neg
  have hi := hb.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hr
  convert hi using 1
  ext p
  simp only [ContinuousLinearMap.mul_apply']
  rw [mul_comm]
  congr 2
  abel_nf

theorem integral_adjoint_convolution {d : ℕ} {k b : Point d → ℂ}
    (hk : Integrable k volume) (hb : Integrable b volume) (s : Set (Point d)) :
    (∫ x in s, ∫ y, star (k (y - x)) * b y) =
      ∫ y, star (∫ x in s, k (y - x)) * b y := by
  have hi : Integrable (fun p : Point d × Point d => star (k (p.2 - p.1)) * b p.2)
      ((volume.restrict s).prod volume) :=
    (integrable_adjoint_convolution_integrand hk hb).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  rw [integral_integral_swap hi]
  congr 1
  ext y
  rw [integral_mul_const]
  exact congrArg (fun z : ℂ => z * b y) (integral_conj (f := fun x => k (y - x)))

/-- A compactly essentially supported L² input is integrable. -/
theorem integrable_of_compact_support_L2 {d : ℕ} {b : Point d → ℂ}
    (h2 : MemLp b 2 volume) {S : Set (Point d)} (hS : IsCompact S)
    (hs : ∀ᵐ y ∂volume, y ∉ S → b y = 0) : Integrable b volume := by
  have hi : IntegrableOn b S volume :=
    (integrableOn_Lp_of_measure_ne_top (h2.toLp b) (by norm_num) hS.measure_lt_top.ne).congr
      (ae_restrict_of_ae h2.coeFn_toLp)
  exact hi.integrable_of_ae_notMem_eq_zero hs

/-- Cut off the rough kernel on the compact difference of two separated sets. -/
theorem exists_localized_kernel {d : ℕ} {K : Point d → ℂ}
    (hK : LocallyIntegrableOn K ({0}ᶜ : Set (Point d)) volume)
    {S E : Set (Point d)} (hS : IsCompact S) (hE : IsCompact E)
    (hdis : Disjoint S E) :
    ∃ k : Point d → ℂ, Integrable k volume ∧
      ∀ y ∈ S, ∀ x ∈ E, k (y - x) = K (y - x) := by
  let D := (fun p : Point d × Point d => p.1 - p.2) '' (S ×ˢ E)
  have hc : IsCompact D := (hS.prod hE).image (continuous_fst.sub continuous_snd)
  have hd : D ⊆ ({0}ᶜ : Set (Point d)) := by
    rintro z ⟨⟨y, x⟩, ⟨hy, hx⟩, rfl⟩
    exact sub_ne_zero.mpr (fun h => (Set.disjoint_left.mp hdis) hy (h ▸ hx))
  refine ⟨D.indicator K, (hK.integrableOn_compact_subset hd hc).integrable_indicator hc.measurableSet, ?_⟩
  intro y hy x hx
  exact indicator_of_mem (show y - x ∈ D from ⟨(y, x), ⟨hy, hx⟩, rfl⟩) K

/-- Identify the adjoint on each compact set separated from the input support.
Indicator tests suffice, so no local L² convolution theorem is required. -/
theorem adjoint_representation_on_compact {d : ℕ}
    (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0) (hK : KernelHypotheses T K A)
    (b : Point d → ℂ) (h2 : MemLp b 2 volume) (S E : Set (Point d))
    (hS : IsCompact S) (hE : IsCompact E) (hdis : Disjoint S E)
    (hbs : ∀ᵐ y ∂volume, y ∉ S → b y = 0) :
    (fun x => T.adjoint (h2.toLp b) x) =ᵐ[volume.restrict E]
      (fun x => ∫ y, star (K (-(x - y))) * b y) := by
  have hb := integrable_of_compact_support_L2 h2 hS hbs
  obtain ⟨k, hk, hkK⟩ := exists_localized_kernel hK.locallyIntegrable hS hE hdis
  let F : Point d → ℂ := fun x => ∫ y, star (k (y - x)) * b y
  have hFi : Integrable F volume :=
    (integrable_adjoint_convolution_integrand hk hb).integral_prod_left
  have hFK (x : Point d) (hx : x ∈ E) :
      F x = ∫ y, star (K (-(x - y))) * b y := by
    apply integral_congr_ae
    filter_upwards [hbs] with y hy
    by_cases hys : y ∈ S
    · rw [hkK y hys x hx, neg_sub]
    · simp [hy hys]
  have hpair (s : Set (Point d)) (hs : MeasurableSet s) (hsub : s ⊆ E) :
      (∫ x in s, T.adjoint (h2.toLp b) x) = ∫ x in s, F x := by
    have hsf : volume s ≠ ∞ := (measure_mono hsub |>.trans_lt hE.measure_lt_top).ne
    let g : L2 d := indicatorConstLp 2 hs hsf (1 : ℂ)
    have hg : MemLp (s.indicator (fun _ : Point d => (1 : ℂ))) 2 volume :=
      memLp_indicator_const 2 hs.nullMeasurableSet 1 (.inr hsf)
    have hoff := hK.offSupport (s.indicator (fun _ : Point d => (1 : ℂ))) hg E hE
      (Eventually.of_forall fun y hy => indicator_of_notMem (fun h => hy (hsub h)) _)
    change ∀ᵐ y ∂volume, y ∉ E → T g y = ∫ x, K (y - x) * s.indicator (fun _ => (1 : ℂ)) x at hoff
    have hinner := T.adjoint_inner_right g (h2.toLp b)
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ _ hs 1 hsf, L2.inner_def] at hinner
    have hinner' : (∫ x in s, T.adjoint (h2.toLp b) x) =
        ∫ y, star (T g y) * (h2.toLp b) y := by
      simpa only [RCLike.inner_apply, starRingEnd_apply, star_one, mul_one, one_mul, mul_comm] using hinner
    rw [hinner']
    calc
      (∫ y, star (T g y) * (h2.toLp b) y) =
          ∫ y, star (∫ x in s, k (y - x)) * b y := by
        apply integral_congr_ae
        filter_upwards [hoff, h2.coeFn_toLp, hbs] with y hy hyb hy0
        rw [hyb]
        by_cases hys : y ∈ S
        · have hye : y ∉ E := fun h => Set.disjoint_left.mp hdis hys h
          rw [hy hye]
          congr 2
          rw [← integral_indicator hs]
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            by_cases hx : x ∈ s
            · simp [hx, hkK y hys x (hsub hx)]
            · simp [hx]
        · simp [hy0 hys]
      _ = ∫ x in s, F x := (integral_adjoint_convolution hk hb s).symm
  have hi : IntegrableOn (fun x => T.adjoint (h2.toLp b) x) E volume :=
    integrableOn_Lp_of_measure_ne_top _ (by norm_num) hE.measure_lt_top.ne
  have heq : (fun x => T.adjoint (h2.toLp b) x) =ᵐ[volume.restrict E] F := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi hFi.integrableOn
    intro s hs _
    rw [Measure.restrict_restrict hs]
    exact hpair (s ∩ E) (hs.inter hE.measurableSet) inter_subset_right
  exact heq.trans ((ae_restrict_mem hE.measurableSet).mono fun x hx => hFK x hx)

/-- The Hilbert adjoint has the reflected conjugate kernel under the original
rough-kernel hypotheses. A countable compact cover handles the full complement. -/
theorem adjoint_representation (d : ℕ) (_hd : 0 < d)
    (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0) (hK : KernelHypotheses T K A)
    (b : Point d → ℂ) (h2 : MemLp b 2 volume) (S : Set (Point d))
    (hS : IsCompact S) (hbs : ∀ᵐ y ∂volume, y ∉ S → b y = 0) :
    ∀ᵐ x ∂volume, x ∉ S →
      T.adjoint (h2.toLp b) x = ∫ y, star (K (-(x - y))) * b y := by
  let U := (Sᶜ : Set (Point d))
  let : LocallyCompactSpace U := hS.isClosed.isOpen_compl.locallyCompactSpace
  let E : ℕ → Set (Point d) := fun n => Subtype.val '' compactCovering U n
  have hc (n : ℕ) : IsCompact (E n) :=
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hd (n : ℕ) : Disjoint S (E n) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨y, _, rfl⟩
    exact y.property hx
  have hcover : ⋃ n, E n = Sᶜ := by
    simp only [E, ← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe, U]
  apply (ae_restrict_iff' hS.measurableSet.compl).mp
  change (fun x => T.adjoint (h2.toLp b) x) =ᵐ[volume.restrict Sᶜ]
    (fun x => ∫ y, star (K (-(x - y))) * b y)
  rw [← hcover, ae_eq_restrict_iUnion_iff]
  intro n
  exact adjoint_representation_on_compact T K A hK b h2 S (E n) hS (hc n) (hd n) hbs

/-- The complete source theorem, with the original rough-kernel hypotheses. -/
theorem full_extension : Specs.P102.U2.CZLp.full_extension :=
  full_extension_of_adjoint_representation adjoint_representation

end P102.U2.CZLp
