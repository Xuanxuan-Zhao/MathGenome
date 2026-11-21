import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.ArclengthFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.MonotoneReparameterization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.AbsolutelyContinuousContours
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcPrimitive
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D12Complex.Arclength
open Stieltjes

/-- Accumulated polygonal variation of the original parametrization. -/
abbrev accumulated (γ : ComplexPath) (t : ℝ) : ℝ :=
  Specs.D12Complex.Ch03.ArclengthFactorization.accumulated_value γ t

theorem accumulated_eq_signed (γ : ComplexPath) {t : ℝ} (ht : t ∈ Icc γ.a γ.b) :
    accumulated γ t = variationOnFromTo γ (Icc γ.a γ.b) γ.a t := by
  rw [accumulated, Specs.D12Complex.Ch03.ArclengthFactorization.accumulated_value,
    totalVariation_eq_eVariationOn γ ht.1,
    variationOnFromTo.eq_of_le _ _ ht.1,
    inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)]

theorem accumulated_properties :
    Specs.D12Complex.Ch03.ArclengthFactorization.accumulated_properties_type := by
  intro γ hγ
  have hb := (rectifiable_iff γ).mp hγ
  have ha : γ.a ∈ Icc γ.a γ.b := ⟨le_rfl, γ.ordered⟩
  have hcont : ContinuousOn (accumulated γ) (Icc γ.a γ.b) := by
    intro x hx
    exact ((hb.continuousWithinAt_variationOnFromTo_iff ha hx).mpr
      (γ.continuousOn x hx)).congr_of_mem
        (fun y hy => accumulated_eq_signed γ hy) hx
  have hm : MonotoneOn (accumulated γ) (Icc γ.a γ.b) := by
    intro x hx y hy hxy
    rw [accumulated_eq_signed γ hx, accumulated_eq_signed γ hy]
    exact variationOnFromTo.monotoneOn hb.locallyBoundedVariationOn ha hx hy hxy
  have hzero : accumulated γ γ.a = 0 := by
    rw [accumulated, Specs.D12Complex.Ch03.ArclengthFactorization.accumulated_value,
      totalVariation_degenerate, ENNReal.toReal_zero]
  have hend : accumulated γ γ.b = (polygonalLength γ).toReal := rfl
  refine ⟨hcont, hm, hzero, hend, ?_⟩
  rw [← hend, ← hzero]
  exact hcont.image_Icc_of_monotoneOn γ.ordered hm

/-- The distance between path values is controlled by the length increment. -/
theorem dist_le_accumulated_sub (γ : ComplexPath) (hγ : Rectifiable γ)
    {x y : ℝ} (hx : x ∈ Icc γ.a γ.b) (hy : y ∈ Icc γ.a γ.b) (hxy : x ≤ y) :
    dist (γ x) (γ y) ≤ accumulated γ y - accumulated γ x := by
  have hfin : totalVariation γ x y ≠ ⊤ := ne_of_lt
    ((totalVariation_mono γ.ordered hxy hx.1 hy.2 γ).trans_lt hγ)
  have hfinx : totalVariation γ γ.a x ≠ ⊤ := ne_of_lt
    ((totalVariation_mono γ.ordered hx.1 le_rfl hx.2 γ).trans_lt hγ)
  have hadd := totalVariation_add hx.1 hxy (γ : ℝ → ℂ)
  have hdist : dist (γ x) (γ y) ≤ (totalVariation γ x y).toReal := by
    rw [totalVariation_eq_eVariationOn γ hxy]
    apply BoundedVariationOn.dist_le
    · simpa [BoundedVariationOn, ← totalVariation_eq_eVariationOn γ hxy] using hfin
    · exact ⟨le_rfl, hxy⟩
    · exact ⟨hxy, le_rfl⟩
  unfold accumulated Specs.D12Complex.Ch03.ArclengthFactorization.accumulated_value
  rw [← hadd, ENNReal.toReal_add hfinx hfin, add_sub_cancel_left]
  exact hdist

theorem dist_le_accumulated_dist (γ : ComplexPath) (hγ : Rectifiable γ)
    {x y : ℝ} (hx : x ∈ Icc γ.a γ.b) (hy : y ∈ Icc γ.a γ.b) :
    dist (γ x) (γ y) ≤ dist (accumulated γ x) (accumulated γ y) := by
  rcases le_total x y with hxy | hyx
  · exact (dist_le_accumulated_sub γ hγ hx hy hxy).trans
      (by rw [Real.dist_eq, abs_sub_comm]; exact le_abs_self _)
  · rw [dist_comm (γ x), dist_comm (accumulated γ x)]
    exact (dist_le_accumulated_sub γ hγ hy hx hyx).trans
      (by rw [Real.dist_eq, abs_sub_comm]; exact le_abs_self _)

theorem lipschitz_factor :
    Specs.D12Complex.Ch03.ArclengthFactorization.lipschitz_factor_type := by
  intro γ hγ
  classical
  obtain ⟨hc, hm, _, _, hi⟩ := accumulated_properties γ hγ
  let L := (polygonalLength γ).toReal
  have hpre (v : ℝ) (hv : v ∈ Icc 0 L) : ∃ t ∈ Icc γ.a γ.b, accumulated γ t = v := by
    exact (show v ∈ accumulated γ '' Icc γ.a γ.b from hi.symm ▸ hv)
  let σ : ℝ → ℂ := fun v => if hv : v ∈ Icc 0 L then γ (hpre v hv).choose else 0
  have hmaps (t : ℝ) (ht : t ∈ Icc γ.a γ.b) : accumulated γ t ∈ Icc 0 L :=
    hi ▸ mem_image_of_mem (accumulated γ) ht
  have hfactor (t : ℝ) (ht : t ∈ Icc γ.a γ.b) : γ t = σ (accumulated γ t) := by
    dsimp only [σ]
    rw [dite_eq_left (hmaps t ht)]
    have hp := (hpre _ (hmaps t ht)).choose_spec
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    have hd := dist_le_accumulated_dist γ hγ ht hp.1
    rw [hp.2, dist_self] at hd
    exact hd
  have hlip : LipschitzOnWith 1 σ (Icc 0 L) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    dsimp only [σ]
    rw [dite_eq_left hv, dite_eq_left hw]
    have hv' := (hpre v hv).choose_spec
    have hw' := (hpre w hw).choose_spec
    simpa only [hv'.2, hw'.2, NNReal.coe_one, one_mul] using
      dist_le_accumulated_dist γ hγ hv'.1 hw'.1
  refine ⟨σ, hlip, hfactor, ?_, ?_⟩
  · rw [← hi, ← image_comp]
    exact image_congr (fun t ht => (hfactor t ht).symm)
  · have hv := variation_monotone (show (0 : ℝ) ≤ L from ENNReal.toReal_nonneg)
      γ.ordered σ (accumulated γ) hm hi
    change totalVariation σ 0 L = totalVariation γ γ.a γ.b
    rw [← hv, totalVariation_eq_eVariationOn _ γ.ordered,
      totalVariation_eq_eVariationOn γ γ.ordered]
    exact eVariationOn.congr (fun t ht => (hfactor t ht).symm)

theorem ac_length : Specs.D12Complex.Ch03.ArclengthFactorization.ac_length_type := by
  intro a b hab σ hσ
  rcases hab.eq_or_lt with rfl | hab
  · simp [totalVariation_degenerate]
  obtain ⟨hi, _, hf⟩ := ac_derivative hab.le σ hσ
  have hcongr := D11.Ch12.variation_congr hf
  have hv := D11.Ch12.AcPrimitive.primitive_variation (deriv σ) (σ a) hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hi)
  have he : totalVariation σ a b =
      ENNReal.ofReal (∫ v in a..b, ‖deriv σ v‖) := by
    rw [totalVariation_eq_eVariationOn σ hab.le, ← D11.Ch12.variation_eq_eVariationOn]
    exact hcongr.trans hv
  rw [he, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab.le
    (fun _ _ => norm_nonneg _))]

theorem unit_speed : Specs.D12Complex.Ch03.ArclengthFactorization.unit_speed_type := by
  intro L hL σ hlip hlen
  have hac : AbsolutelyContinuousOnInterval σ 0 L :=
    (show LipschitzOnWith 1 σ (uIcc 0 L) from by
      simpa [uIcc_of_le hL.le] using hlip).absolutelyContinuousOnInterval
  obtain ⟨hi, hd, _⟩ := ac_derivative hL.le σ hac
  have hnorm : ∀ᵐ v ∂volume.restrict (Icc 0 L), ‖deriv σ v‖ ≤ 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun v hv => by
      simpa using norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hv.1 hv.2) hlip)
  have heq : (∫ v in (0 : ℝ)..L, ‖deriv σ v‖) = ∫ _v in (0 : ℝ)..L, (1 : ℝ) := by
    rw [← ac_length hL.le σ hac, hlen]
    simp
  have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mp hi.norm
  have hc' : IntegrableOn (fun _v : ℝ => (1 : ℝ)) (Icc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mp intervalIntegrable_const
  have heqcc : (∫ v in Icc 0 L, ‖deriv σ v‖) = ∫ _v in Icc 0 L, (1 : ℝ) := by
    simpa only [intervalIntegral.integral_of_le hL.le, integral_Icc_eq_integral_Ioc] using heq
  have hunit := (integral_eq_iff_of_ae_le hi' hc' hnorm).mp heqcc
  have hd' : ∀ᵐ v ∂volume.restrict (Icc 0 L), HasDerivAt σ (deriv σ v) v := by
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact hd
  filter_upwards [hunit, hd'] with v hv hder
  exact ⟨hder, hv⟩

/-- Equality on the parameter interval suffices for the mesh-defined integral. -/
theorem integral_congr_on {a b : ℝ} (hab : a ≤ b)
    {u v γ η : ℝ → ℂ} (hu : ContinuousOn u (Icc a b))
    (hγ : totalVariation γ a b < ⊤) (huv : EqOn u v (Icc a b))
    (hγη : EqOn γ η (Icc a b)) : integral a b u γ = integral a b v η := by
  apply (integral_eq_of_hasIntegral hab ?_).symm
  have hi := hasIntegral_integral hab u γ hu hγ
  intro ε hε
  obtain ⟨δ, hδ, hlim⟩ := hi ε hε
  refine ⟨δ, hδ, fun P hP tags => ?_⟩
  have hmem (i : Fin (P.n + 1)) : P.point i ∈ Icc a b := by
    constructor
    · simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i)
    · simpa only [P.last] using P.strictMono.monotone (Fin.le_last i)
  have heq : taggedSum P tags v η = taggedSum P tags u γ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← huv (SingleVariableAnalysis.Stieltjes.tag_mem_interval P tags i),
      ← hγη (hmem i.succ), ← hγη (hmem i.castSucc)]
  change ‖taggedSum P tags v η - integral a b u γ‖ < ε
  rw [heq]
  exact hlim P hP tags

theorem arclength_factorization :
    Specs.D12Complex.Ch03.ArclengthFactorization.arclength_factorization_type := by
  intro γ hγ hL
  classical
  obtain ⟨σ, hlip, hfac, htrace, hvar⟩ := lipschitz_factor γ hγ
  let L := (polygonalLength γ).toReal
  have hL0 : (0 : ℝ) ≤ L := hL.le
  have hac : AbsolutelyContinuousOnInterval σ 0 L :=
    (show LipschitzOnWith 1 σ (uIcc 0 L) from by
      simpa only [uIcc_of_le hL0] using hlip).absolutelyContinuousOnInterval
  have hσfin : totalVariation σ 0 L < ⊤ := hvar ▸ hγ
  have hlen : (totalVariation σ 0 L).toReal = L := congrArg ENNReal.toReal hvar
  have hs := unit_speed hL σ hlip hlen
  obtain ⟨hsc, hsm, _, _, hsi⟩ := accumulated_properties γ hγ
  refine ⟨σ, hlip, hfac, htrace, hvar, hs, ?_⟩
  intro f hf
  have hu : ContinuousOn (f ∘ σ) (Icc 0 L) :=
    hf.comp hlip.continuousOn (fun v hv => htrace ▸ mem_image_of_mem σ hv)
  obtain ⟨hi, heqσ⟩ := integral_ac hL0 (f ∘ σ) σ hu hac
  have heqcomp : contourIntegral γ f = integral γ.a γ.b
      ((f ∘ σ) ∘ accumulated γ) (σ ∘ accumulated γ) := by
    apply integral_congr_on γ.ordered
      (hf.comp γ.continuousOn (fun t ht => ⟨t, ht, rfl⟩)) hγ
    · intro t ht
      simp only [Function.comp_apply, ← hfac t ht]
    · exact hfac
  have heq : contourIntegral γ f = ∫ v in (0 : ℝ)..L, f (σ v) * deriv σ v :=
    heqcomp.trans ((integral_monotone hL0 γ.ordered (f ∘ σ) σ (accumulated γ)
      hu hσfin hsc hsm hsi).trans heqσ)
  have hinorm : IntervalIntegrable (fun v => ‖f (σ v)‖ * ‖deriv σ v‖) volume 0 L := by
    simpa only [Function.comp_apply, norm_mul] using hi.norm
  refine ⟨hi, hinorm, heq, ?_, ?_⟩
  · rw [heq]
    simpa only [norm_mul] using intervalIntegral.norm_integral_le_integral_norm hL0
      (f := fun v => f (σ v) * deriv σ v)
  · let M := sSup ((fun z => ‖f z‖) '' γ.trace)
    have hbounded : BddAbove ((fun z => ‖f z‖) '' γ.trace) :=
      (ComplexPath.trace_compact γ).bddAbove_image hf.norm
    have hM (v : ℝ) (hv : v ∈ Icc 0 L) : ‖f (σ v)‖ ≤ M :=
      le_csSup hbounded (mem_image_of_mem _ (htrace ▸ mem_image_of_mem σ hv))
    have hiD := (ac_derivative hL0 σ hac).1.norm
    have hle : (∫ v in (0 : ℝ)..L, ‖f (σ v)‖ * ‖deriv σ v‖) ≤
        ∫ v in (0 : ℝ)..L, M * ‖deriv σ v‖ := by
      apply intervalIntegral.integral_mono_on hL0 hinorm (hiD.const_mul M)
      intro v hv
      exact mul_le_mul_of_nonneg_right (hM v hv) (norm_nonneg _)
    rw [intervalIntegral.integral_const_mul, ← ac_length hL0 σ hac, hlen] at hle
    simpa only [mul_comm] using hle

theorem zero_length : Specs.D12Complex.Ch03.ArclengthFactorization.zero_length_type := by
  intro γ hzero
  exact ⟨constant_of_zero_variation γ.ordered γ hzero,
    fun f => integral_zero_variation γ.ordered (f ∘ γ) γ hzero⟩

/-- A pointwise bound on the fixed trace gives a bound for the contour integral. -/
theorem contourIntegral_norm_le_bound (γ : ComplexPath) (hγ : Rectifiable γ)
    (f : ℂ → ℂ) (hf : ContinuousOn f γ.trace) {M : ℝ}
    (hM : ∀ z ∈ γ.trace, ‖f z‖ ≤ M) :
    ‖contourIntegral γ f‖ ≤ (polygonalLength γ).toReal * M := by
  apply (contourIntegral_norm_le γ hγ f hf).trans
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact csSup_le ((ComplexPath.trace_nonempty γ).image _) (by
    rintro _ ⟨z, hz, rfl⟩
    exact hM z hz)

theorem contourIntegral_uniform_limit :
    Specs.D12Complex.Ch03.ArclengthFactorization.contourIntegral_uniform_limit_type := by
  intro γ hγ f F hf hF hlim
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let L := (polygonalLength γ).toReal
  let η := ε / (L + 1)
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hlim) η hη)
  refine ⟨N, fun n hn => ?_⟩
  have hdiff : contourIntegral γ (fun z => F n z - f z) =
      contourIntegral γ (F n) - contourIntegral γ f := by
    have h := continuous_integrand_linearity γ.ordered (F n ∘ γ) (f ∘ γ) γ 1 (-1)
      ((hF n).comp γ.continuousOn (fun t ht => ⟨t, ht, rfl⟩))
      (hf.comp γ.continuousOn (fun t ht => ⟨t, ht, rfl⟩)) hγ
    simp only [contourIntegral, Function.comp_def, one_mul, neg_one_mul,
      sub_eq_add_neg] at h ⊢
    exact h
  rw [dist_eq_norm, ← hdiff]
  have hbound : ‖contourIntegral γ (fun z => F n z - f z)‖ ≤ L * η :=
    contourIntegral_norm_le_bound γ hγ _ ((hF n).sub hf) (fun z hz => by
      have h := hN n hn z hz
      change ‖F n z - f z‖ ≤ η
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using h.le)
  apply hbound.trans_lt
  have heq : η * (L + 1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

end D12Complex.Arclength
