import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DifferenceQuotientEstimate
import MathGenome.Internal.FourierSobolev.P102.U4.ACL
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Pointwise ENNReal Topology
namespace P102.U4.DifferenceQuotient

@[simp] theorem norm_coordinateVector {d : ℕ} (j : Fin d) :
    ‖coordinateVector d j‖ = 1 := by
  simp [coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single]

/-- Every strict interior parameter stays inside the open-ball neighborhood. -/
theorem segment_mem_neighborhood {d : ℕ} {V : Set (Space d)}
    {x : Space d} (hx : x ∈ V) (j : Fin d) {h t : ℝ}
    (hh : h ≠ 0) (ht : |t| < 1) :
    x + (t * h) • coordinateVector d j ∈ neighborhood V h := by
  refine ⟨x, hx, (t*h) • coordinateVector d j, ?_, rfl⟩
  simp only [Metric.mem_ball, dist_zero_right, norm_smul, norm_coordinateVector,
    mul_one, Real.norm_eq_abs, abs_mul]
  exact (mul_lt_mul_of_pos_right ht (abs_pos.mpr hh)).trans_eq (one_mul _)

/-- Openness of V also puts the segment endpoint in the open-ball sum. -/
theorem endpoint_mem_neighborhood {d : ℕ} {V : Set (Space d)} (hV : IsOpen V)
    {x : Space d} (hx : x ∈ V) (j : Fin d) {h : ℝ} (hh : h ≠ 0) :
    x + h • coordinateVector d j ∈ neighborhood V h := by
  obtain ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.mp hV x hx
  obtain ⟨δ, hδ, hδm⟩ := exists_between (lt_min (div_pos hε (abs_pos.mpr hh)) zero_lt_one)
  have hδε := hδm.trans_le (min_le_left _ _)
  have hδ1 := hδm.trans_le (min_le_right _ _)
  have hbase : x + (δ*h) • coordinateVector d j ∈ V := by
    apply hxε
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      norm_coordinateVector, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
    exact (lt_div_iff₀ (abs_pos.mpr hh)).mp hδε
  refine ⟨x + (δ*h) • coordinateVector d j, hbase,
    ((1-δ)*h) • coordinateVector d j, ?_, ?_⟩
  · simp only [Metric.mem_ball, dist_zero_right, norm_smul, norm_coordinateVector,
      mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos (sub_pos.mpr hδ1)]
    exact (mul_lt_mul_of_pos_right (by linarith : 1-δ < 1)
      (abs_pos.mpr hh)).trans_eq (one_mul _)
  · change x + (δ*h) • coordinateVector d j + ((1-δ)*h) • coordinateVector d j = _
    rw [add_assoc, ← add_smul]
    congr 2
    ring

/-- The full closed segment lies in the same neighborhood, including both ends. -/
theorem closed_segment_mem_neighborhood {d : ℕ} {V : Set (Space d)} (hV : IsOpen V)
    {x : Space d} (hx : x ∈ V) (j : Fin d) {h t : ℝ}
    (hh : h ≠ 0) (ht : t ∈ Icc (0 : ℝ) 1) :
    x + (t*h) • coordinateVector d j ∈ neighborhood V h := by
  by_cases ht1 : t = 1
  · simpa [ht1] using endpoint_mem_neighborhood hV hx j hh
  · exact segment_mem_neighborhood hx j hh (by rw [abs_of_nonneg ht.1]; exact lt_of_le_of_ne ht.2 ht1)

/-- Averaging the directional translates over a unit interval. -/
def segmentAverage {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : Space d → 𝕜) (j : Fin d) (h : ℝ) (x : Space d) : 𝕜 :=
  ∫ t in Ioo (0 : ℝ) 1, v (x + (t*h) • coordinateVector d j)

/-- Translation on V is controlled by the norm on the open-ball neighborhood. -/
theorem translated_eLpNorm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {V : Set (Space d)} {v : Space d → 𝕜} (hv : StronglyMeasurable v)
    (j : Fin d) {h t : ℝ} (hh : h ≠ 0) (ht : |t| < 1) (p : ℝ≥0∞) :
    eLpNorm (fun x => v (x + (t*h) • coordinateVector d j)) p (volume.restrict V) ≤
      eLpNorm v p (volume.restrict (neighborhood V h)) := by
  have mp := (measurePreserving_add_right volume ((t*h) • coordinateVector d j)).restrict_image_emb
    (Homeomorph.addRight _).measurableEmbedding V
  change eLpNorm (v ∘ (fun x => x + (t*h) • coordinateVector d j)) p (volume.restrict V) ≤ _
  rw [eLpNorm_comp_measurePreserving (g := v) hv.aestronglyMeasurable.restrict mp]
  apply eLpNorm_mono_measure
  apply Measure.restrict_mono
  · rintro _ ⟨x, hx, rfl⟩
    exact segment_mem_neighborhood hx j hh ht
  · exact le_rfl

/-- Minkowski and translation give the constant-one bound for the segment average. -/
theorem segmentAverage_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {V : Set (Space d)} {v : Space d → 𝕜} (hv : StronglyMeasurable v)
    (j : Fin d) {h : ℝ} (hh : h ≠ 0)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hvp : MemLp v p (volume.restrict (neighborhood V h))) :
    MemLp (segmentAverage v j h) p (volume.restrict V) ∧
      eLpNorm (segmentAverage v j h) p (volume.restrict V) ≤
        eLpNorm v p (volume.restrict (neighborhood V h)) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let F : Space d × ℝ → 𝕜 := fun z => v (z.1 + (z.2*h) • coordinateVector d j)
  have hF : Measurable F := hv.measurable.comp
    (measurable_fst.add ((measurable_snd.mul_const h).smul_const _))
  have hb : (∫⁻ t in Ioo (0 : ℝ) 1,
      eLpNorm (fun x => F (x,t)) p (volume.restrict V)) ≤
      eLpNorm v p (volume.restrict (neighborhood V h)) := by
    calc
      _ ≤ ∫⁻ _t in Ioo (0 : ℝ) 1, eLpNorm v p (volume.restrict (neighborhood V h)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact translated_eLpNorm_le hv j hh (by rw [abs_of_pos ht.1]; exact ht.2) p
      _ = _ := by simp
  obtain ⟨_, hbound⟩ := ExpandedFA.Distributions.minkowski_integral_eLpNorm
    (volume.restrict V) (volume.restrict (Ioo (0 : ℝ) 1)) p hp hpt F hF
    (hb.trans_lt hvp.eLpNorm_lt_top)
  exact ⟨hbound.trans_lt (hb.trans_lt hvp.eLpNorm_lt_top), hbound.trans hb⟩

/-- Restriction of ACL representatives, allowing an a.e. change of derivative. -/
theorem representative_restrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω U : Opens (Space d)} (hU : (U : Set (Space d)) ⊆ Ω)
    (j : Fin d) {u v w : Space d → 𝕜}
    (hr : ACL.HasRepresentative Ω j u v)
    (hvw : v =ᵐ[volume.restrict (U : Set (Space d))] w) :
    ACL.HasRepresentative U j u w := by
  obtain ⟨f, huf, hf⟩ := hr
  refine ⟨f, ae_restrict_of_ae_restrict_of_subset hU huf, ?_⟩
  filter_upwards [hf, ACL.ae_on_fibers j hvw] with z hz hzw
  have hsub : ACL.fiber U j z ⊆ ACL.fiber Ω j z := fun _ ht => hU ht
  refine ⟨fun a b hab => hz.1 a b (hab.trans hsub), ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hz.2, hzw] with t ht he
  rwa [← he]

/-- Translation preserves a.e. equality when its image lies in the comparison set. -/
theorem ae_eq_translate {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A B : Set (Space d)} {f g : Space d → 𝕜}
    (he : f =ᵐ[volume.restrict B] g) (a : Space d)
    (hs : (fun x => x+a) '' A ⊆ B) :
    (fun x => f (x+a)) =ᵐ[volume.restrict A] (fun x => g (x+a)) := by
  exact ((measurePreserving_add_right volume a).restrict_image_emb
    (Homeomorph.addRight a).measurableEmbedding A).quasiMeasurePreserving.ae
      (ae_restrict_of_ae_restrict_of_subset hs he)

/-- The quotient depends only on the a.e. class in its neighborhood. -/
theorem quotient_congr {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {V : Set (Space d)} (hV : IsOpen V) {u f : Space d → 𝕜}
    (j : Fin d) {h : ℝ} (hh : h ≠ 0)
    (he : u =ᵐ[volume.restrict (neighborhood V h)] f) :
    quotient u j h =ᵐ[volume.restrict V] quotient f j h := by
  have hsub : V ⊆ neighborhood V h := by
    intro x hx
    simpa using segment_mem_neighborhood hx j hh (t := 0) (by norm_num)
  have ht := ae_eq_translate he (h • coordinateVector d j) (by
    rintro _ ⟨x, hx, rfl⟩
    exact endpoint_mem_neighborhood hV hx j hh)
  filter_upwards [ht, ae_restrict_of_ae_restrict_of_subset hsub he] with x hx hy
  simp only [quotient, hx, hy]

@[simp] theorem line_add_coordinate {d : ℕ} (j : Fin d) (z : ACL.Transverse j)
    (t s : ℝ) :
    ACL.line j z t + s • coordinateVector d j = ACL.line j z (t+s) := by
  classical
  apply PiLp.ext
  intro i
  by_cases hi : i = j
  · subst i
    simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  · simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single, hi]

/-- Lift a transverse full-measure set back to Euclidean space. -/
theorem ae_of_ae_transverse {d : ℕ} (j : Fin d) {P : ACL.Transverse j → Prop}
    (hP : ∀ᵐ z ∂volume, P z) :
    ∀ᵐ x : Space d ∂volume, P (fun k => x k.val) := by
  have hp : ∀ᵐ q : ℝ × ACL.Transverse j ∂(volume.prod volume), P q.2 :=
    Measure.quasiMeasurePreserving_snd.ae hP
  rw [← Measure.volume_eq_prod] at hp
  have hc := (ExpandedFA.Sobolev.Lines.coordinateEquiv_measurePreserving j).quasiMeasurePreserving.ae hp
  have he := (PiLp.volume_preserving_toLp (Fin d)).symm
    (MeasurableEquiv.toLp 2 (Fin d → ℝ))
  exact he.quasiMeasurePreserving.ae hc

@[simp] theorem line_at_point {d : ℕ} (j : Fin d) (x : Space d) :
    ACL.line j (fun k => x k.val) (x j) = x := by
  classical
  apply PiLp.ext
  intro i
  by_cases hi : i = j <;> simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, hi]

/-- The ACL fundamental theorem, written as a normalized segment average.
The specified derivative is globally integrable on this one line; no
integrability or regularity is assumed for f away from the open fiber. -/
theorem segmentAverage_eq_quotient_on_line {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : Opens (Space d)) (j : Fin d) (f w : Space d → 𝕜)
    (z : ACL.Transverse j) (a h : ℝ) (hh : h ≠ 0)
    (hac : ACL.LocallyAC (fun t => f (ACL.line j z t)) (ACL.fiber U j z))
    (hd : ∀ᵐ t ∂volume.restrict (ACL.fiber U j z),
      HasDerivAt (fun s => f (ACL.line j z s)) (w (ACL.line j z t)) t)
    (hw : Integrable (fun t => w (ACL.line j z t)) volume)
    (hs : uIcc a (a+h) ⊆ ACL.fiber U j z) :
    segmentAverage w j h (ACL.line j z a) = quotient f j h (ACL.line j z a) := by
  have hd' : ∀ᵐ t ∂volume, t ∈ uIcc a (a+h) →
      HasDerivAt (fun s => f (ACL.line j z s)) (w (ACL.line j z t)) t := by
    filter_upwards [(ae_restrict_iff' (ACL.fiber_isOpen U j z).measurableSet).mp hd] with t ht hti
    exact ht (hs hti)
  have hFTC := ExpandedFA.Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
    (hac a (a+h) hs) hw.locallyIntegrable hd'
  unfold segmentAverage quotient
  simp only [line_add_coordinate]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hchange := intervalIntegral.integral_comp_mul_add
    (a := (0:ℝ)) (b := 1) (fun t => w (ACL.line j z t)) hh a
  simp only [mul_zero, zero_add, mul_one] at hchange
  simp_rw [mul_comm h, add_comm _ a] at hchange
  rw [hchange, hFTC]

/-- The segment identity holds for the original a.e. class, with no special
choice of values at the two endpoints. -/
theorem segmentAverage_eq_quotient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (V : Opens (Space d)) (j : Fin d) (u w : Space d → 𝕜)
    {h : ℝ} (hh : h ≠ 0)
    (hr : ACL.HasRepresentative
      ⟨neighborhood (V : Set (Space d)) h, V.isOpen.add_right⟩ j u w)
    (hw : Integrable w volume) :
    segmentAverage w j h =ᵐ[volume.restrict (V : Set (Space d))] quotient u j h := by
  let U : Opens (Space d) := ⟨neighborhood (V : Set (Space d)) h, V.isOpen.add_right⟩
  obtain ⟨f, huf, hf⟩ := hr
  have hgood := ae_of_ae_transverse j (hf.and (ACL.integrable_lines j hw))
  have havg : segmentAverage w j h =ᵐ[volume.restrict (V : Set (Space d))] quotient f j h := by
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
    have hs : uIcc (x j) (x j+h) ⊆ ACL.fiber U j (fun k => x k.val) := by
      intro s hs
      rw [← segment_eq_uIcc, segment_eq_image'] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      simp only [add_sub_cancel_left, smul_eq_mul]
      change ACL.line j (fun k => x k.val) (x j + t*h) ∈ (U : Set (Space d))
      rw [← line_add_coordinate, line_at_point]
      exact closed_segment_mem_neighborhood V.isOpen hxV j hh ht
    simpa only [line_at_point] using segmentAverage_eq_quotient_on_line
      U j f w (fun k => x k.val) (x j) h hh hx.1.1 hx.1.2 hx.2 hs
  exact havg.trans (quotient_congr V.isOpen j hh huf).symm

end P102.U4.DifferenceQuotient

namespace P102.U4

/-- U4-05: the sharp interior difference-quotient estimate for every finite
exponent p ≥ 1. The proof uses only the j-th distributional derivative and
requires no Lp hypothesis on u. -/
theorem difference_quotient_estimate : DifferenceQuotientExpected.Estimate := by
  intro d _hd 𝕜 _ Ω V j h p hp hpt hh hVc _hVΩ hNΩ u v hu hv hvp hweak
  let N : Opens (Space d) :=
    ⟨DifferenceQuotient.neighborhood (V : Set (Space d)) h, V.isOpen.add_right⟩
  have hNm : MeasurableSet (N : Set (Space d)) := N.isOpen.measurableSet
  have hNb : Bornology.IsBounded (N : Set (Space d)) :=
    (hVc.isBounded.subset subset_closure).add Metric.isBounded_ball
  let : IsFiniteMeasure (volume.restrict (N : Set (Space d))) :=
    isFiniteMeasure_restrict.mpr hNb.measure_lt_top.ne
  let m : Space d → 𝕜 := hvp.aestronglyMeasurable.mk v
  let w : Space d → 𝕜 := (N : Set (Space d)).indicator m
  have hm : StronglyMeasurable m := hvp.aestronglyMeasurable.stronglyMeasurable_mk
  have hvm : v =ᵐ[volume.restrict (N : Set (Space d))] m := hvp.aestronglyMeasurable.ae_eq_mk
  have hvw : v =ᵐ[volume.restrict (N : Set (Space d))] w := by
    filter_upwards [hvm, ae_restrict_mem hNm] with x hx hxN
    simpa only [w, indicator_of_mem hxN] using hx
  have hmp : MemLp m p (volume.restrict (N : Set (Space d))) := (memLp_congr_ae hvm).mp hvp
  have hwint : Integrable w volume := (integrable_indicator_iff hNm).mpr (hmp.integrable hp)
  have hwp : MemLp w p (volume.restrict (N : Set (Space d))) := (memLp_congr_ae hvw).mp hvp
  have hr := DifferenceQuotient.representative_restrict (U := N) hNΩ j
    (ACL.weak_to_representative j hu hv hweak) hvw
  have hid := DifferenceQuotient.segmentAverage_eq_quotient V j u w hh hr hwint
  obtain ⟨hmem, hbound⟩ := DifferenceQuotient.segmentAverage_bound
    (V := (V : Set (Space d))) (hm.indicator hNm) j hh hp hpt hwp
  refine ⟨(memLp_congr_ae hid).mp hmem, ?_⟩
  calc
    _ = eLpNorm (DifferenceQuotient.segmentAverage w j h) p (volume.restrict (V : Set (Space d))) :=
      (eLpNorm_congr_ae hid).symm
    _ ≤ eLpNorm w p (volume.restrict (N : Set (Space d))) := hbound
    _ = _ := (eLpNorm_congr_ae hvw).symm

end P102.U4
