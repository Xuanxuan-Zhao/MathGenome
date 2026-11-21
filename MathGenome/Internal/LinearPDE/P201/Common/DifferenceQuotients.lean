import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Common.DifferenceQuotients
import MathGenome.Internal.FourierSobolev.P102.U4.DifferenceQuotientConverse

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace P201

abbrev differenceQuotient : P201Specs.differenceQuotientType :=
  @P201Specs.differenceQuotient

/-- A local uniform quotient bound constructs the distributional derivative. -/
theorem differenceQuotientConverse : P201Specs.differenceQuotientConverseStatement := by
  intro n hn 𝕜 _ Ω V U j p hp hpt hUV _hVΩ w C hb
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  have hu := P102.U4.domainLp_locallyIntegrable V p w
  have hb' : P102.U4.DifferenceQuotient.HasBound V U j p w C := by
    obtain ⟨δ, hδ, hb⟩ := hb
    obtain ⟨ε, hε, hK⟩ := hUV.1.exists_cthickening_subset_open V.isOpen hUV.2
    refine ⟨min δ ε, lt_min hδ hε, fun h hh hδ' => ?_⟩
    obtain ⟨hm, hnorm⟩ := hb h hh (hδ'.trans_le (min_le_left _ _))
    refine ⟨?_, hm, hnorm⟩
    intro x hx
    apply hK
    apply Metric.mem_cthickening_of_dist_le _ x ε _ (subset_closure hx)
    simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul,
      P102.U4.DifferenceQuotient.norm_coordinateVector, mul_one, Real.norm_eq_abs]
      using (hδ'.trans_le (min_le_right _ _)).le
  obtain ⟨g, hg, hweak⟩ := hb'.exists_local_derivative hp hpt hu hUV
  exact ⟨g, hweak, hg⟩

namespace DifferenceQuotients
open P102.U4
open P102.U4.DifferenceQuotient

/-- Translation is a contraction from the comparison domain onto a subset. -/
theorem translatedNorm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Set (Space n)} {v : Space n → 𝕜} (hv : StronglyMeasurable v)
    (a : Space n) (ha : (fun x => x + a) '' U ⊆ V) (p : ℝ≥0∞) :
    eLpNorm (fun x => v (x + a)) p (volume.restrict U) ≤
      eLpNorm v p (volume.restrict V) := by
  have mp := (measurePreserving_add_right volume a).restrict_image_emb
    (Homeomorph.addRight a).measurableEmbedding U
  change eLpNorm (v ∘ (fun x => x + a)) p (volume.restrict U) ≤ _
  rw [eLpNorm_comp_measurePreserving (g := v) hv.aestronglyMeasurable.restrict mp]
  exact eLpNorm_mono_measure v (Measure.restrict_mono ha le_rfl)

/-- Minkowski with only the directional segment condition. -/
theorem segmentAverage_bound {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Domain n) (j : Fin n) (h : ℝ)
    (hs : P201Specs.AdmissibleSegments U V j h)
    {v : Space n → 𝕜} (hv : StronglyMeasurable v)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hvp : MemLp v p (domainMeasure V)) :
    MemLp (segmentAverage v j h) p (domainMeasure U) ∧
      eLpNorm (segmentAverage v j h) p (domainMeasure U) ≤
        eLpNorm v p (domainMeasure V) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let F : Space n × ℝ → 𝕜 := fun z => v (z.1 + (z.2*h) • coordinate n j)
  have hF : Measurable F := hv.measurable.comp
    (measurable_fst.add ((measurable_snd.mul_const h).smul_const _))
  have hb : (∫⁻ t in Ioo (0 : ℝ) 1,
      eLpNorm (fun x => F (x,t)) p (domainMeasure U)) ≤
      eLpNorm v p (domainMeasure V) := by
    calc
      _ ≤ ∫⁻ _t in Ioo (0 : ℝ) 1, eLpNorm v p (domainMeasure V) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        apply translatedNorm_le hv ((t*h) • coordinate n j) _ p
        rintro _ ⟨x, hx, rfl⟩
        exact hs x hx t ⟨ht.1.le, ht.2.le⟩
      _ = _ := by simp
  obtain ⟨_, hbound⟩ := ExpandedFA.Distributions.minkowski_integral_eLpNorm
    (domainMeasure U) (volume.restrict (Ioo (0 : ℝ) 1)) p hp hpt F hF
    (hb.trans_lt hvp.eLpNorm_lt_top)
  exact ⟨hbound.trans_lt (hb.trans_lt hvp.eLpNorm_lt_top), hbound.trans hb⟩

/-- ACL on the containing domain suffices; no ball neighborhood is required. -/
theorem segmentAverage_eq_quotient {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Domain n) (j : Fin n) (u v : Space n → 𝕜)
    {h : ℝ} (hh : h ≠ 0) (hs : P201Specs.AdmissibleSegments U V j h)
    (hr : ACL.HasRepresentative V j u v) (hv : Integrable v volume) :
    segmentAverage v j h =ᵐ[domainMeasure U] quotient u j h := by
  obtain ⟨f, huf, hf⟩ := hr
  have hgood := ae_of_ae_transverse j (hf.and (ACL.integrable_lines j hv))
  have havg : segmentAverage v j h =ᵐ[domainMeasure U] quotient f j h := by
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem U.isOpen.measurableSet]
      with x hx hxU
    have hseg : uIcc (x j) (x j+h) ⊆ ACL.fiber V j (fun k => x k.val) := by
      intro s hmem
      rw [← segment_eq_uIcc, segment_eq_image'] at hmem
      obtain ⟨t, ht, rfl⟩ := hmem
      simp only [add_sub_cancel_left, smul_eq_mul]
      change ACL.line j (fun k => x k.val) (x j + t*h) ∈ (V : Set (Space n))
      rw [← line_add_coordinate, line_at_point]
      exact hs x hxU t ht
    simpa only [line_at_point] using segmentAverage_eq_quotient_on_line
      V j f v (fun k => x k.val) (x j) h hh hx.1.1 hx.1.2 hx.2 hseg
  have hUV : (U : Set (Space n)) ⊆ V := by
    intro x hx
    simpa using hs x hx 0 (by simp)
  have ht := ae_eq_translate huf (h • coordinate n j) (A := (U : Set (Space n))) (by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hs x hx 1 (by simp))
  have hq : quotient u j h =ᵐ[domainMeasure U] quotient f j h := by
    filter_upwards [ht, ae_restrict_of_ae_restrict_of_subset hUV huf] with x hx hy
    simp only [quotient, hx, hy]
  exact havg.trans hq.symm

end DifferenceQuotients

/-- The sharp estimate on every admissible coordinate segment, including p=1. -/
theorem differenceQuotientEstimate : P201Specs.differenceQuotientEstimateStatement := by
  intro n hn 𝕜 _ Ω V U j h p _ hpt hh hUV hVΩ hs u
  let v := P102.U4.sobolevDerivative u (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n 1)
  have hvp := Lp.memLp v
  have hVm : MeasurableSet (V : Set (Space n)) := V.isOpen.measurableSet
  let : IsFiniteMeasure (domainMeasure V) :=
    isFiniteMeasure_restrict.mpr
      ((hVΩ.1.isBounded.subset subset_closure).measure_lt_top.ne)
  let m := hvp.aestronglyMeasurable.mk (v : Space n → 𝕜)
  let w := (V : Set (Space n)).indicator m
  have hm : StronglyMeasurable m := hvp.aestronglyMeasurable.stronglyMeasurable_mk
  have hvm : (v : Space n → 𝕜) =ᵐ[domainMeasure V] m :=
    hvp.aestronglyMeasurable.ae_eq_mk
  have hvw : (v : Space n → 𝕜) =ᵐ[domainMeasure V] w := by
    filter_upwards [hvm, ae_restrict_mem hVm] with x hx hxV
    simpa only [w, indicator_of_mem hxV] using hx
  have hmp : MemLp m p (domainMeasure V) := (memLp_congr_ae hvm).mp hvp
  have hwint : Integrable w volume := (integrable_indicator_iff hVm).mpr (hmp.integrable Fact.out)
  have hwp : MemLp w p (domainMeasure V) := (memLp_congr_ae hvw).mp hvp
  have hr := P102.U4.DifferenceQuotient.representative_restrict (U := V) le_rfl j
    (P102.U4.ACL.weak_to_representative j
      (P102.U4.domainLp_locallyIntegrable V p (P102.U4.sobolevUnderlying u))
      (P102.U4.domainLp_locallyIntegrable V p v)
      (P102.U4.sobolev_derivative_distribution V 1 p u ⟨{j}, by simp⟩)) hvw
  have hid := DifferenceQuotients.segmentAverage_eq_quotient U V j
    (P102.U4.sobolevUnderlying u) w hh hs hr hwint
  obtain ⟨hmem, hbound⟩ := DifferenceQuotients.segmentAverage_bound U V j h hs
    (hm.indicator hVm) Fact.out hpt hwp
  refine ⟨(memLp_congr_ae hid).mp hmem, ?_⟩
  calc
    _ = eLpNorm (P102.U4.DifferenceQuotient.segmentAverage w j h) p (domainMeasure U) :=
      (eLpNorm_congr_ae hid).symm
    _ ≤ eLpNorm w p (domainMeasure V) := hbound
    _ = _ := (eLpNorm_congr_ae hvw).symm


/-- The discrete adjoint identity only requires integrability of the products. -/
theorem discreteIntegrationByPartsWholeSpace :
    P201Specs.discreteIntegrationByPartsWholeSpaceStatement := by
  intro n hn 𝕜 _ w ψ j h hh hB hC
  let a := h • coordinate n j
  change Integrable (fun x => w x * ψ (x - a)) volume at hC
  have hA : Integrable (fun x => w (x + a) * ψ x) volume := by
    simpa only [Function.comp_def, add_sub_cancel_right] using
      (measurePreserving_add_right volume a).integrable_comp_of_integrable hC
  have hAC : (∫ x, w (x + a) * ψ x) = ∫ x, w x * ψ (x - a) := by
    simpa only [add_sub_cancel_right] using
      integral_add_right_eq_self (fun x => w x * ψ (x - a)) a
  simp only [P201Specs.differenceQuotient, P102.U4.DifferenceQuotient.quotient,
    smul_mul_assoc, sub_mul, mul_smul_comm, mul_sub, neg_smul, ← sub_eq_add_neg]
  change (∫ x, h⁻¹ • (w (x + a) * ψ x - w x * ψ x)) =
    -(∫ x, (-h)⁻¹ • (w x * ψ (x - a) - w x * ψ x))
  rw [integral_smul, integral_sub hA hB, integral_smul, integral_sub hC hB, hAC]
  simp

/-- Compact tests with admissible translates give the local discrete adjoint identity. -/
theorem discreteIntegrationByParts : P201Specs.discreteIntegrationByPartsStatement := by
  intro n hn 𝕜 _ Ω w ψ j h hh hw hs
  let a := h • coordinate n j
  have hsub : tsupport (fun x => ψ (x - a)) ⊆ (Ω : Set (Space n)) := by
    intro x hx
    have hx' : x - a ∈ tsupport ψ :=
      tsupport_comp_subset_preimage (f := fun x => x - a) ψ (by fun_prop) hx
    simpa only [← show h • coordinate n j = a from rfl, sub_add_cancel] using hs (x - a) hx'
  let ψplus : Test 𝕜 Ω :=
    ⟨fun x => ψ (x - a), ψ.contDiff.comp (contDiff_id.sub contDiff_const),
      ψ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight a), hsub⟩
  have hB : Integrable (fun x => w x * ψ x) volume := by
    simpa [mul_comm] using ψ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hw
  have hC : Integrable (fun x => w x * ψ (x - a)) volume := by
    change Integrable (fun x => w x * ψplus x) volume
    simpa [mul_comm] using ψplus.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hw
  have hwhole := discreteIntegrationByPartsWholeSpace hn w ψ j h hh hB hC
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [ψ.zero_on_compl hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hwhole
  · intro x hx
    have hz : ψ x = 0 := ψ.zero_on_compl hx
    have hz' : ψ (x - a) = 0 := ψplus.zero_on_compl hx
    simp only [P201Specs.differenceQuotient,
      P102.U4.DifferenceQuotient.quotient, neg_smul, ← sub_eq_add_neg]
    change w x * ((-h)⁻¹ • (ψ (x-a) - ψ x)) = 0
    rw [hz, hz']
    simp

end P201
