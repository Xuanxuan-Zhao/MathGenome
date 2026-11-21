import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatTrace
import MathGenome.Internal.FourierSobolev.P102.U4.ACL
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.DenseEmbedding
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ENNReal

namespace P102.Trace
open P102.U4

@[simp] theorem point_height (m : ℕ) (z : Boundary m) (t : ℝ) :
    point m z t (Fin.last m) = t := by
  simp [point, ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine]

@[simp] theorem vertical_fiber (m : ℕ) (z : Boundary m) :
    ACL.fiber (halfSpace m) (Fin.last m) z = Ioi (0 : ℝ) := by
  ext t
  change (0 < point m z t (Fin.last m)) ↔ 0 < t
  rw [point_height]

/-- Explicit identification with m ordinary real coordinates. -/
def boundaryCoordinates (m : ℕ) : (Fin m → ℝ) ≃ᵐ Boundary m :=
  MeasurableEquiv.piCongrLeft (fun _ : {j : Fin (m + 1) // j ≠ Fin.last m} => ℝ)
    (finSuccAboveEquiv (Fin.last m))

theorem boundaryCoordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (boundaryCoordinates m) volume volume :=
  volume_measurePreserving_piCongrLeft _ _

/-- The boundary/height coordinates use exactly Lebesgue measure. -/
theorem point_measurePreserving (m : ℕ) :
    MeasurePreserving (fun q : Boundary m × ℝ => point m q.1 q.2)
      (volume.prod volume) volume := by
  have hsplit := (ExpandedFA.Sobolev.Lines.coordinateEquiv_measurePreserving
    (Fin.last m)).symm (ExpandedFA.Sobolev.Lines.coordinateEquiv (Fin.last m))
  have h := (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
    (hsplit.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure (Boundary m))) (ν := (volume : Measure ℝ))))
  simpa only [Function.comp_def, Prod.swap,
    ExpandedFA.Sobolev.Lines.coordinateEquiv_symm_apply, point, ACL.line] using h

/-- Product disintegration on the actual half-space, with the open positive
height interval rather than an arbitrarily assigned zero-height slice. -/
theorem halfSpace_measurePreserving (m : ℕ) :
    MeasurePreserving (fun q : Boundary m × ℝ => point m q.1 q.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ))))
      (volume.restrict (halfSpace m : Set (Space (m + 1)))) := by
  have h := (point_measurePreserving m).restrict_preimage (halfSpace m).isOpen.measurableSet
  have he : (fun q : Boundary m × ℝ => point m q.1 q.2) ⁻¹'
      (halfSpace m : Set (Space (m + 1))) = univ ×ˢ Ioi (0 : ℝ) := by
    ext q
    simp [halfSpace]
  rw [he, ← Measure.prod_restrict, Measure.restrict_univ] at h
  exact h

/-- In particular, each actual Sobolev tuple component has the expected product
Lp bound. This change of variables assumes no pointwise slice integrability. -/
theorem halfSpace_memLp_product {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (v : DomainLp 𝕜 (halfSpace m) p) :
    MemLp (fun q : Boundary m × ℝ => v (point m q.1 q.2)) p
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
  (Lp.memLp v).comp_measurePreserving (halfSpace_measurePreserving m)

theorem halfSpace_eLpNorm_product {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (v : DomainLp 𝕜 (halfSpace m) p) :
    eLpNorm (fun q : Boundary m × ℝ => v (point m q.1 q.2)) p
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) =
    eLpNorm v p (volume.restrict (halfSpace m : Set (Space (m + 1)))) :=
  eLpNorm_comp_measurePreserving (Lp.memLp v).aestronglyMeasurable
    (halfSpace_measurePreserving m)

/-- Ambient a.e. statements hold on almost every horizontal slice. -/
theorem ae_on_heights {m : ℕ} {P : Space (m + 1) → Prop}
    (hP : ∀ᵐ x ∂volume.restrict (halfSpace m : Set (Space (m + 1))), P x) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ z : Boundary m ∂volume, P (point m z t) := by
  have h := (halfSpace_measurePreserving m).comp
    (Measure.measurePreserving_swap
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure (Boundary m))))
  exact Measure.ae_ae_of_ae_prod (h.quasiMeasurePreserving.ae hP)

/-- Vertical ACL representatives come from the actual weak derivative of the
shared Sobolev model. No slice value has yet been selected. -/
theorem vertical_acl : FlatTraceExpected.VerticalACL := by
  intro m 𝕜 _ p _ u
  have h := (acl_characterization (m + 1) (by omega) 𝕜 (halfSpace m)
    (Fin.last m) (sobolevUnderlying u) (sobolevDerivative u (verticalIndex m))
    (domainLp_locallyIntegrable (halfSpace m) p _)
    (domainLp_locallyIntegrable (halfSpace m) p _)).mp
      (sobolev_derivative_distribution (halfSpace m) 1 p u (verticalIndex m))
  simpa only [ACL.HasRepresentative, vertical_fiber, point] using h

/-- A.e. agreement determines every nonnegative-height slice, including the
zero-height endpoint, by continuity in the Lp norm. -/
theorem slice_unique : FlatTraceExpected.SliceUniqueness := by
  intro m 𝕜 _ p _ u F G hF hG
  have hae : F =ᵐ[volume.restrict (Ioi (0 : ℝ))] G := by
    filter_upwards [hF.2, hG.2] with t hFt hGt
    exact Lp.ext (hFt.trans hGt.symm)
  have hpos : EqOn F G (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      (hF.1.mono Ioi_subset_Ici_self) (hG.1.mono Ioi_subset_Ici_self)
  have hext := hpos.of_subset_closure hF.1 hG.1 Ioi_subset_Ici_self
  exact hext (by rw [closure_Ioi])

theorem IsSliceRepresentative.add {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {u v : HalfSobolev m 𝕜 p}
    {F G : ℝ → BoundaryLp m 𝕜 p}
    (hF : IsSliceRepresentative u F) (hG : IsSliceRepresentative v G) :
    IsSliceRepresentative (u + v) (F + G) := by
  refine ⟨hF.1.add hG.1, ?_⟩
  have huv : sobolevUnderlying (u + v) = sobolevUnderlying u + sobolevUnderlying v :=
    (sobolevUnderlyingCLM (halfSpace m) 1 p).map_add u v
  have ha := ae_on_heights (m := m)
    (show ∀ᵐ x ∂volume.restrict (halfSpace m : Set (Space (m + 1))),
      sobolevUnderlying (u + v) x = sobolevUnderlying u x + sobolevUnderlying v x by
      rw [huv]
      exact Lp.coeFn_add _ _)
  filter_upwards [hF.2, hG.2, ha] with t hFt hGt hat
  filter_upwards [hFt, hGt, hat, Lp.coeFn_add (F t) (G t)] with z hFz hGz haz hcz
  change (F t + G t) z = sobolevUnderlying (u + v) (point m z t)
  rw [hcz, Pi.add_apply, hFz, hGz, haz]

theorem IsSliceRepresentative.smul {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : HalfSobolev m 𝕜 p}
    {F : ℝ → BoundaryLp m 𝕜 p} (hF : IsSliceRepresentative u F) (c : 𝕜) :
    IsSliceRepresentative (c • u) (c • F) := by
  refine ⟨hF.1.const_smul c, ?_⟩
  have hcu : sobolevUnderlying (c • u) = c • sobolevUnderlying u :=
    (sobolevUnderlyingCLM (halfSpace m) 1 p).map_smul c u
  have ha := ae_on_heights (m := m)
    (show ∀ᵐ x ∂volume.restrict (halfSpace m : Set (Space (m + 1))),
      sobolevUnderlying (c • u) x = c • sobolevUnderlying u x by
      rw [hcu]
      exact Lp.coeFn_smul _ _)
  filter_upwards [hF.2, ha] with t hFt hat
  filter_upwards [hFt, hat, Lp.coeFn_smul c (F t)] with z hFz haz hcz
  change (c • F t) z = sobolevUnderlying (c • u) (point m z t)
  rw [hcz, Pi.smul_apply, hFz, haz]

/-- Once representative existence and the endpoint bound are proved, linearity
is forced by representative uniqueness. This constructs the actual bounded map. -/
theorem trace_of_slice_representatives {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hex : ∀ u : HalfSobolev m 𝕜 p, ∃ F : ℝ → BoundaryLp m 𝕜 p,
      IsSliceRepresentative u F) (C : ℝ)
    (hbound : ∀ (u : HalfSobolev m 𝕜 p) (F : ℝ → BoundaryLp m 𝕜 p),
      IsSliceRepresentative u F → ‖F 0‖ ≤ C * ‖u‖) :
    ∃ T : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p,
      (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (u : HalfSobolev m 𝕜 p) (F : ℝ → BoundaryLp m 𝕜 p),
        IsSliceRepresentative u F → T u = F 0 := by
  choose S hS using hex
  have huniq (u : HalfSobolev m 𝕜 p) (F : ℝ → BoundaryLp m 𝕜 p)
      (hF : IsSliceRepresentative u F) : S u 0 = F 0 :=
    slice_unique m 𝕜 p u (S u) F (hS u) hF (by simp)
  let L : HalfSobolev m 𝕜 p →ₗ[𝕜] BoundaryLp m 𝕜 p :=
    { toFun := fun u => S u 0
      map_add' := fun u v => huniq (u + v) (S u + S v) ((hS u).add (hS v))
      map_smul' := fun c u => huniq (c • u) (c • S u) ((hS u).smul c) }
  refine ⟨L.mkContinuous C (fun u => hbound u (S u) (hS u)), ?_, ?_⟩
  · exact fun u => hbound u (S u) (hS u)
  · exact huniq

/-- Continuity up to the boundary identifies the vertical trace, with no
pointwise assertion about the original arbitrary Lp representative. -/
theorem vertical_boundary_compatibility : FlatTraceExpected.VerticalBoundaryCompatibility := by
  intro m 𝕜 _ p _ u g f hg hf huf
  obtain ⟨v, huv, hv⟩ := hg
  have hline := ACL.ae_on_fibers (Fin.last m) (huv.symm.trans huf)
  filter_upwards [hv, hline] with z hz heq
  have hfc : ContinuousOn (fun t => f (point m z t)) (Ici (0 : ℝ)) :=
    hf.comp (ACL.line_contDiff (Fin.last m) z).continuous.continuousOn
      (fun t ht => by simpa using ht)
  have hvc : ContinuousOn (fun t => v (point m z t)) (Ioi (0 : ℝ)) :=
    ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn hz.1 isOpen_Ioi
  have heq' : (fun t => v (point m z t)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => f (point m z t)) := by
    simpa only [Filter.EventuallyEq, vertical_fiber, point] using heq
  have hon := Measure.eqOn_open_of_ae_eq heq' isOpen_Ioi hvc
    (hfc.mono Ioi_subset_Ici_self)
  have hft : Tendsto (fun t => f (point m z t)) (𝓝[>] 0)
      (𝓝 (f (point m z 0))) :=
    (hfc 0 (by simp)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  exact tendsto_nhds_unique hz.2.2
    (hft.congr' (eventually_mem_nhdsWithin.mono fun t ht => (hon ht).symm))

/-- Completeness converts a vanishing scalar oscillation modulus into a limit.
This is the endpoint-completeness step independently of the slicing argument. -/
theorem exists_limit_of_vanishing_control {ι E : Type*} [MetricSpace E]
    [CompleteSpace E] {l : Filter ι} [l.NeBot] {F : ι → E} {J : ι → ℝ}
    {s : Set ι} (hs : s ∈ l) (hJ : Tendsto J l (𝓝 0))
    (hbound : ∀ a ∈ s, ∀ b ∈ s, dist (F a) (F b) ≤ |J a| + |J b|) :
    ∃ g : E, Tendsto F l (𝓝 g) := by
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, fun ε hε => ?_⟩
  have hsmall : ∀ᶠ t in l, |J t| < ε / 2 := by
    have h := hJ.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < ε / 2 by simpa using half_pos hε))
    simpa using h
  let A := s ∩ {t | |J t| < ε / 2}
  have hA : A ∈ l := inter_mem hs hsmall
  refine ⟨F '' A, ?_, ?_⟩
  · apply mem_map.mpr
    exact mem_of_superset hA fun t ht => ⟨t, ht, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    calc
      dist (F a) (F b) ≤ |J a| + |J b| := hbound a ha.1 b hb.1
      _ < ε / 2 + ε / 2 := add_lt_add ha.2 hb.2
      _ = ε := by ring

/-- The scalar primitive controls the endpoint Cauchy filter. Local integrability
through zero is essential here; integrability only on (0,∞) locally is insufficient. -/
theorem exists_endpoint_of_integral_control {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E} {A : ℝ → ℝ} (hA : IntervalIntegrable A volume 0 1)
    (hinc : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ b ∈ Ioc (0 : ℝ) 1,
      ‖F b - F a‖ ≤ ∫ t in min a b..max a b, A t) :
    ∃ g : E, Tendsto F (𝓝[>] 0) (𝓝 g) := by
  let J : ℝ → ℝ := fun t => ∫ a in (0 : ℝ)..t, A a
  have hc : ContinuousOn J (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      (intervalIntegral.continuousOn_primitive_interval' hA left_mem_uIcc)
  have hJ : Tendsto J (𝓝[>] 0) (𝓝 0) := by
    have hc0 := hc 0 (by simp)
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 0 :=
      nhdsWithin_le_iff.mpr
        (mem_of_superset (Ioc_mem_nhdsGT zero_lt_one) Ioc_subset_Icc_self)
    simpa [J] using hc0.mono_left hle
  have hi (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) 1) :
      IntervalIntegrable A volume 0 a :=
    hA.mono_set (by
      rw [uIcc_of_le ha.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl ha.2)
  apply exists_limit_of_vanishing_control
    (s := Ioc (0 : ℝ) 1) (J := J) (Ioc_mem_nhdsGT zero_lt_one) hJ
  intro a ha b hb
  have he : (∫ t in a..b, A t) = J b - J a := by
    dsimp [J]
    exact (intervalIntegral.integral_interval_sub_left (hi b hb) (hi a ha)).symm
  have he' : (∫ t in b..a, A t) = J a - J b := by
    dsimp [J]
    exact (intervalIntegral.integral_interval_sub_left (hi a ha) (hi b hb)).symm
  rcases le_total a b with hab | hba
  · calc
      dist (F a) (F b) = ‖F b - F a‖ := dist_eq_norm' _ _
      _ ≤ ∫ t in a..b, A t := by simpa [min_eq_left hab, max_eq_right hab] using hinc a ha b hb
      _ = J b - J a := he
      _ ≤ |J a| + |J b| := by linarith [le_abs_self (J b), neg_le_abs (J a)]
  · calc
      dist (F a) (F b) = ‖F b - F a‖ := dist_eq_norm' _ _
      _ ≤ ∫ t in b..a, A t := by simpa [min_eq_right hba, max_eq_left hba] using hinc a ha b hb
      _ = J a - J b := he'
      _ ≤ |J a| + |J b| := by linarith [le_abs_self (J a), neg_le_abs (J b)]

section ProductLp

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {p : ℝ≥0∞} {f : X × Y → E}

/-- Finite product Lp membership gives Lp sections at almost every height. -/
theorem MemLp_sections (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : MemLp f p (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x => f (x, y)) p μ := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_right,
    (hf.integrable_norm_rpow hp0 hpt).prod_left_ae] with y hym hyi
  exact (integrable_norm_rpow_iff hym hp0 hpt).mp hyi

/-- Tonelli for the powers underlying the mixed norm, including arbitrary
quotient representatives and exceptional sections. -/
theorem lintegral_section_eLpNorm_rpow (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : MemLp f p (μ.prod ν)) :
    (∫⁻ y, eLpNorm (fun x => f (x, y)) p μ ^ p.toReal ∂ν) =
      ∫⁻ q, ‖f q‖ₑ ^ p.toReal ∂(μ.prod ν) := by
  have hpR : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hpt⟩
  calc
    _ = ∫⁻ y, ∫⁻ x, ‖f (x, y)‖ₑ ^ p.toReal ∂μ ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hf.aestronglyMeasurable.prodMk_right] with y hy
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hy,
        ← ENNReal.rpow_mul]
      simp [hpR]
    _ = _ := (lintegral_prod_symm _ (hf.aestronglyMeasurable.enorm.pow_const _)).symm

/-- Measurability of the section norm is a conclusion, not a hypothesis on
pointwise representatives. -/
theorem aemeasurable_section_eLpNorm (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : MemLp f p (μ.prod ν)) :
    AEMeasurable (fun y => eLpNorm (fun x => f (x, y)) p μ) ν := by
  have hm := (hf.aestronglyMeasurable.enorm.pow_const p.toReal).lintegral_prod_left'
  apply (hm.pow_const (1 / p.toReal)).congr
  filter_upwards [hf.aestronglyMeasurable.prodMk_right] with y hy
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hy).symm

/-- The real section-norm profile belongs to the same Lp space in height.
In particular its finite-interval L1 bounds remain valid at p = 1. -/
theorem memLp_section_profile (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : MemLp f p (μ.prod ν)) :
    MemLp (fun y => (eLpNorm (fun x => f (x, y)) p μ).toReal) p ν := by
  have hm := (aemeasurable_section_eLpNorm hp0 hpt hf).ennreal_toReal.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt hm]
  have he : (∫⁻ y, ‖(eLpNorm (fun x => f (x, y)) p μ).toReal‖ₑ ^ p.toReal ∂ν) =
      ∫⁻ y, eLpNorm (fun x => f (x, y)) p μ ^ p.toReal ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [MemLp_sections hp0 hpt hf] with y hy
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy.ne]
  rw [he, lintegral_section_eLpNorm_rpow hp0 hpt hf]
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt hf.eLpNorm_lt_top

/-- Exact mixed-norm equality: no extra constant or measure normalization. -/
theorem eLpNorm_section_profile (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : MemLp f p (μ.prod ν)) :
    eLpNorm (fun y => (eLpNorm (fun x => f (x, y)) p μ).toReal) p ν =
      eLpNorm f p (μ.prod ν) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
    (memLp_section_profile hp0 hpt hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable]
  congr 1
  calc
    _ = ∫⁻ y, eLpNorm (fun x => f (x, y)) p μ ^ p.toReal ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [MemLp_sections hp0 hpt hf] with y hy
      rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy.ne]
    _ = _ := lintegral_section_eLpNorm_rpow hp0 hpt hf

end ProductLp

set_option maxHeartbeats 800000 in
/-- Every genuine derivative component has Lp horizontal sections a.e. -/
theorem halfSpace_memLp_sections {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (v : DomainLp 𝕜 (halfSpace m) p) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      MemLp (fun z : Boundary m => v (point m z t)) p volume :=
  MemLp_sections (f := fun q : Boundary m × ℝ => v (point m q.1 q.2))
    hp0 hpt (halfSpace_memLp_product v)

set_option maxHeartbeats 800000 in
/-- The height profile of a component retains its exact global Lp norm. -/
theorem halfSpace_memLp_profile {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (v : DomainLp 𝕜 (halfSpace m) p) :
    MemLp (fun t => (eLpNorm (fun z : Boundary m => v (point m z t)) p volume).toReal)
      p (volume.restrict (Ioi (0 : ℝ))) :=
  memLp_section_profile (f := fun q : Boundary m × ℝ => v (point m q.1 q.2))
    hp0 hpt (halfSpace_memLp_product v)

theorem halfSpace_eLpNorm_profile {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (v : DomainLp 𝕜 (halfSpace m) p) :
    eLpNorm (fun t => (eLpNorm (fun z : Boundary m => v (point m z t)) p volume).toReal)
      p (volume.restrict (Ioi (0 : ℝ))) =
      eLpNorm v p (volume.restrict (halfSpace m : Set (Space (m + 1)))) := by
  rw [eLpNorm_section_profile hp0 hpt (halfSpace_memLp_product v), halfSpace_eLpNorm_product]

/-- The derivative profile is globally Lp in height, including the endpoint p=1. -/
theorem verticalProfile_memLp {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) (u : HalfSobolev m 𝕜 p) :
    MemLp (verticalProfile u) p (volume.restrict (Ioi (0 : ℝ))) :=
  halfSpace_memLp_profile (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hpt
    (sobolevDerivative u (verticalIndex m))

/-- In particular the control is integrable all the way through height zero. -/
theorem verticalProfile_integrableOn {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) (u : HalfSobolev m 𝕜 p)
    (R : ℝ) : IntegrableOn (verticalProfile u) (Ioc 0 R) := by
  have h : MemLp (verticalProfile u) p (volume.restrict (Ioc 0 R)) :=
    (verticalProfile_memLp hpt u).mono_measure
    (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  exact h.integrable Fact.out

/-- A continuous scalar modulus extends data on a dense set into a complete
metric space. This supplies the completion step for a.e.-defined Lp slices,
without assigning values to exceptional raw sections. -/
theorem exists_continuous_extension_of_control {A B E : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MetricSpace E] [CompleteSpace E]
    {i : A → B} (hi : IsDenseInducing i) (f : A → E) (J : B → ℝ)
    (hJ : Continuous J) (hcontrol : ∀ a b, dist (f a) (f b) ≤ |J (i a) - J (i b)|) :
    ∃ F : B → E, Continuous F ∧ (∀ a, F (i a) = f a) ∧
      ∀ a b, dist (F a) (F b) ≤ |J a - J b| := by
  have hlim (b : B) : ∃ g : E, Tendsto f (comap i (𝓝 b)) (𝓝 g) := by
    have : (comap i (𝓝 b)).NeBot := hi.comap_nhds_neBot b
    have hj : Tendsto (fun a => J (i a) - J b) (comap i (𝓝 b)) (𝓝 0) := by
      have hj0 : Tendsto (fun a => J (i a)) (comap i (𝓝 b)) (𝓝 (J b)) :=
        (hJ.tendsto b).comp tendsto_comap
      simpa using hj0.sub_const (J b)
    apply exists_limit_of_vanishing_control (s := univ) (by simp) hj
    intro a _ c _
    calc
      dist (f a) (f c) ≤ |J (i a) - J (i c)| := hcontrol a c
      _ ≤ |J (i a) - J b| + |J (i c) - J b| := by
        simpa [abs_sub_comm] using abs_sub_le (J (i a)) (J b) (J (i c))
  let F := hi.extend f
  have hF : Continuous F := hi.continuous_extend hlim
  have hEq : ∀ a, F (i a) = f a := hi.extend_eq' hlim
  refine ⟨F, hF, hEq, ?_⟩
  have hc : IsClosed {q : B × B | dist (F q.1) (F q.2) ≤ |J q.1 - J q.2|} :=
    isClosed_le ((hF.comp continuous_fst).dist (hF.comp continuous_snd))
      (((hJ.comp continuous_fst).sub (hJ.comp continuous_snd)).abs)
  have hd := hi.dense.prodMap hi.dense
  intro a b
  apply isClosed_property hd hc (fun q : A × A => ?_) (a, b)
  change dist (F (i q.1)) (F (i q.2)) ≤ |J (i q.1) - J (i q.2)|
  rw [hEq, hEq]
  exact hcontrol q.1 q.2

/-- The exact endpoint comparison follows by passing to the right limit in
the increment estimate. It requires integrability through zero. -/
theorem endpoint_norm_sub_le_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ → E} {g : E} {A : ℝ → ℝ}
    (hg : Tendsto F (𝓝[>] 0) (𝓝 g))
    (hA : ∀ R : ℝ, 0 < R → IntervalIntegrable A volume 0 R)
    (hinc : ∀ a b : ℝ, 0 < a → 0 < b →
      ‖F b - F a‖ ≤ ∫ t in min a b..max a b, A t)
    {t : ℝ} (ht : 0 < t) : ‖g - F t‖ ≤ ∫ a in (0 : ℝ)..t, A a := by
  let J : ℝ → ℝ := fun a => ∫ s in (0 : ℝ)..a, A s
  have hc : ContinuousOn J (Icc 0 t) := by
    simpa only [uIcc_of_le ht.le] using
      (intervalIntegral.continuousOn_primitive_interval' (hA t ht) left_mem_uIcc)
  have hj : Tendsto J (𝓝[>] 0) (𝓝 0) := by
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (0 : ℝ) t] 0 :=
      nhdsWithin_le_iff.mpr
        (mem_of_superset (Ioc_mem_nhdsGT ht) Ioc_subset_Icc_self)
    simpa [J] using (hc 0 (by simp [ht.le])).mono_left hle
  suffices ‖g - F t‖ ≤ J t - 0 by simpa only [sub_zero] using this
  apply le_of_tendsto_of_tendsto
    ((hg.sub_const (F t)).norm) ((tendsto_const_nhds.sub hj) :
      Tendsto (fun a => J t - J a) (𝓝[>] 0) (𝓝 (J t - 0)))
  filter_upwards [Ioc_mem_nhdsGT ht] with a ha
  have hai : IntervalIntegrable A volume 0 a := (hA t ht).mono_set (by
    rw [uIcc_of_le ha.1.le, uIcc_of_le ht.le]
    exact Icc_subset_Icc le_rfl ha.2)
  have he : (∫ s in a..t, A s) = J t - J a :=
    (intervalIntegral.integral_interval_sub_left (hA t ht) hai).symm
  rw [← he]
  simpa [min_eq_right ha.2, max_eq_left ha.2] using hinc t a ht ha.1

/-- Extending a continuous positive-height curve by its complete-space endpoint
preserves all positive slices and gives the exact comparison with height zero. -/
theorem extend_to_zero_of_integral_control {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → E} {A : ℝ → ℝ}
    (hF : ContinuousOn F (Ioi 0))
    (hA : ∀ R : ℝ, 0 < R → IntervalIntegrable A volume 0 R)
    (hinc : ∀ a b : ℝ, 0 < a → 0 < b →
      ‖F b - F a‖ ≤ ∫ t in min a b..max a b, A t) :
    ∃ G : ℝ → E, ContinuousOn G (Ici 0) ∧ EqOn G F (Ioi 0) ∧
      Tendsto G (𝓝[>] 0) (𝓝 (G 0)) ∧
      ∀ t : ℝ, 0 < t → ‖G 0‖ ≤ ‖G t‖ + ∫ a in (0 : ℝ)..t, A a := by
  classical
  obtain ⟨g, hg⟩ := exists_endpoint_of_integral_control (hA 1 zero_lt_one)
    (fun a ha b hb => hinc a b ha.1 hb.1)
  let G := Function.update F 0 g
  have heq : EqOn G F (Ioi 0) := fun t ht => Function.update_of_ne ht.ne' _ _
  have hG0 : G 0 = g := by simp [G]
  have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by ext t; simp [lt_iff_le_and_ne, eq_comm]
  have hG : ContinuousOn G (Ici 0) := by
    apply continuousOn_update_iff.mpr
    rw [hset]
    exact ⟨hF, fun _ => hg⟩
  refine ⟨G, hG, heq, ?_, ?_⟩
  · rw [hG0]
    exact hg.congr' (eventually_mem_nhdsWithin.mono fun t ht => (heq ht).symm)
  · intro t ht
    rw [hG0, heq ht]
    calc
      ‖g‖ ≤ ‖g - F t‖ + ‖F t‖ := by
        simpa only [sub_add_cancel] using norm_add_le (g - F t) (F t)
      _ ≤ (∫ a in (0 : ℝ)..t, A a) + ‖F t‖ :=
        by linarith [endpoint_norm_sub_le_integral hg hA hinc ht]
      _ = _ := add_comm _ _

/-- Unit-height averaging of a component profile costs no extra constant. -/
theorem halfSpace_integral_profile_unit_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (v : DomainLp 𝕜 (halfSpace m) p) :
    (∫ t in Ioc (0 : ℝ) 1,
      (eLpNorm (fun z : Boundary m => v (point m z t)) p volume).toReal) ≤ ‖v‖ := by
  let A : ℝ → ℝ := fun t =>
    (eLpNorm (fun z : Boundary m => v (point m z t)) p volume).toReal
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hA : MemLp A p (volume.restrict (Ioi (0 : ℝ))) :=
    halfSpace_memLp_profile hp0 hpt v
  have hA1 : MemLp A p (volume.restrict (Ioc (0 : ℝ) 1)) := hA.mono_measure
    (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  have hle : eLpNorm A 1 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      eLpNorm A p (volume.restrict (Ioi (0 : ℝ))) := by
    calc
      _ ≤ eLpNorm A p (volume.restrict (Ioc (0 : ℝ) 1)) *
          (volume.restrict (Ioc (0 : ℝ) 1)) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ Fact.out hA1.aestronglyMeasurable
      _ = eLpNorm A p (volume.restrict (Ioc (0 : ℝ) 1)) := by simp
      _ ≤ _ := eLpNorm_mono_measure A (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  have hn : (eLpNorm A 1 (volume.restrict (Ioc (0 : ℝ) 1))).toReal =
      ∫ t in Ioc (0 : ℝ) 1, A t := by
    rw [toReal_eLpNorm, lpNorm_one_eq_integral_norm hA1.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => Real.norm_of_nonneg ENNReal.toReal_nonneg
  rw [← hn]
  have hf := ENNReal.toReal_mono hA.ne hle
  change _ ≤ (eLpNorm v p (volume.restrict (halfSpace m : Set (Space (m + 1))))).toReal
  exact hf.trans_eq (congrArg ENNReal.toReal (halfSpace_eLpNorm_profile hp0 hpt v))

/-- An identified slice curve has the same norm profile a.e.; this makes the
averaging proof meaningful on the original quotient Sobolev class. -/
theorem slice_norm_profile_ae {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : HalfSobolev m 𝕜 p}
    {F : ℝ → BoundaryLp m 𝕜 p} (hF : IsSliceRepresentative u F) :
    (fun t => ‖F t‖) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (eLpNorm (fun z : Boundary m => sobolevUnderlying u (point m z t))
        p volume).toReal) := by
  filter_upwards [hF.2] with t ht
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae ht)

/-- The endpoint norm estimate by averaging over 0<t<1. Its only analytic
input beyond representative existence is the actual endpoint comparison. -/
theorem slice_endpoint_norm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) {u : HalfSobolev m 𝕜 p}
    {F : ℝ → BoundaryLp m 𝕜 p} (hF : IsSliceRepresentative u F)
    (hzero : ∀ t : ℝ, 0 < t →
      ‖F 0‖ ≤ ‖F t‖ + ∫ a in (0 : ℝ)..t, verticalProfile u a) :
    ‖F 0‖ ≤ ‖sobolevUnderlying u‖ + ‖sobolevDerivative u (verticalIndex m)‖ := by
  let U : ℝ → ℝ := fun t =>
    (eLpNorm (fun z : Boundary m => sobolevUnderlying u (point m z t)) p volume).toReal
  let V := verticalProfile u
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hU : IntegrableOn U (Ioc 0 1) :=
    ((halfSpace_memLp_profile hp0 hpt (sobolevUnderlying u)).mono_measure
      (Measure.restrict_mono (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self) le_rfl)).integrable Fact.out
  have hV : IntegrableOn V (Ioc 0 1) := verticalProfile_integrableOn hpt u 1
  have hnorm : (fun t => ‖F t‖) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] U :=
    ae_mono (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) (slice_norm_profile_ae hF)
  have hcomp : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      ‖F 0‖ ≤ U t + ∫ a in Ioc (0 : ℝ) 1, V a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hnorm] with t ht hnt
    have hlt : (∫ a in (0 : ℝ)..t, V a) ≤ ∫ a in Ioc (0 : ℝ) 1, V a := by
      rw [intervalIntegral.integral_of_le ht.1.le]
      apply setIntegral_mono_set hV
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      exact Eventually.of_forall (fun _ ha => ⟨ha.1, ha.2.trans ht.2⟩)
    have hz := hzero t ht.1
    rw [hnt] at hz
    linarith
  have havg := integral_mono_ae (integrable_const ‖F 0‖)
    (hU.add (integrable_const (∫ a in Ioc (0 : ℝ) 1, V a))) hcomp
  change (∫ _ in Ioc (0 : ℝ) 1, ‖F 0‖) ≤
    ∫ t in Ioc (0 : ℝ) 1, U t + (∫ a in Ioc (0 : ℝ) 1, V a) at havg
  rw [integral_add hU (integrable_const _)] at havg
  simp [Measure.real] at havg
  calc
    ‖F 0‖ ≤ (∫ t in Ioc (0 : ℝ) 1, U t) + ∫ t in Ioc (0 : ℝ) 1, V t := havg
    _ ≤ _ := add_le_add (halfSpace_integral_profile_unit_le hpt (sobolevUnderlying u))
      (halfSpace_integral_profile_unit_le hpt (sobolevDerivative u (verticalIndex m)))

/-- Scalar Minkowski with all measurability and mixed-norm finiteness supplied
by product Lp membership on a finite interval in the second variable. -/
theorem minkowski_of_product_memLp {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] [IsFiniteMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : X × Y → 𝕜}
    (hfm : Measurable f) (hf : MemLp f p (μ.prod ν)) :
    (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧
      eLpNorm (fun x => ∫ y, f (x, y) ∂ν) p μ ≤
        ENNReal.ofReal (∫ y, (eLpNorm (fun x => f (x, y)) p μ).toReal ∂ν) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hi := (memLp_section_profile hp0 hpt hf).integrable hp
  have hfinite : ∀ᵐ y ∂ν, eLpNorm (fun x => f (x, y)) p μ ≠ ∞ :=
    (MemLp_sections hp0 hpt hf).mono fun _ hy => hy.ne
  have hfin : (∫⁻ y, eLpNorm (fun x => f (x, y)) p μ ∂ν) < ∞ :=
    lt_top_iff_ne_top.mpr ((hasFiniteIntegral_toReal_iff hfinite).mp hi.hasFiniteIntegral)
  have he : ENNReal.ofReal (∫ y, (eLpNorm (fun x => f (x, y)) p μ).toReal ∂ν) =
      ∫⁻ y, eLpNorm (fun x => f (x, y)) p μ ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    apply lintegral_congr_ae
    exact hfinite.mono fun _ hy => ENNReal.ofReal_toReal hy
  rw [he]
  exact ExpandedFA.Distributions.minkowski_integral_eLpNorm μ ν p hp hpt f hfm hfin

/-- FTC on a compact positive-height interval, with no global integrability
assumption on the vertical derivative outside that interval. -/
theorem vertical_integral_eq_sub {𝕜 : Type} [RCLike 𝕜] {f h : ℝ → 𝕜}
    (hf : ACL.LocallyAC f (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), HasDerivAt f (h t) t)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hi : IntegrableOn h (uIcc a b)) :
    (∫ t in a..b, h t) = f b - f a := by
  classical
  have hs : uIcc a b ⊆ Ioi 0 := by
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  let k := (uIcc a b).indicator h
  have hk : Integrable k volume := (integrable_indicator_iff measurableSet_uIcc).mpr hi
  have hdk : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt f (k t) t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hd] with t ht hti
    simpa only [k, indicator_of_mem hti] using ht (hs hti)
  have he := ExpandedFA.Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
    (hf a b hs) hk.locallyIntegrable hdk
  rw [← he]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (indicator_of_mem ht h).symm

/-- The graph norm includes both the original function and the vertical weak
partial derivative. A fixed constant suffices for the ordinary trace bound. -/
theorem slice_endpoint_sobolev_bound {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) {u : HalfSobolev m 𝕜 p}
    {F : ℝ → BoundaryLp m 𝕜 p} (hF : IsSliceRepresentative u F)
    (hzero : ∀ t : ℝ, 0 < t →
      ‖F 0‖ ≤ ‖F t‖ + ∫ a in (0 : ℝ)..t, verticalProfile u a) :
    ‖F 0‖ ≤ 2 * ‖u‖ := by
  have h₀ : ‖sobolevUnderlying u‖ ≤ ‖u‖ :=
    PiLp.norm_apply_le u.val (zeroSobolevIndex (m + 1) 1)
  have h₁ : ‖sobolevDerivative u (verticalIndex m)‖ ≤ ‖u‖ :=
    PiLp.norm_apply_le u.val (verticalIndex m)
  linarith [slice_endpoint_norm_le hpt hF hzero]


set_option maxHeartbeats 800000 in
theorem horizontal_slice_increment_le_of_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) (u : HalfSobolev m 𝕜 p)
    {f : Space (m + 1) → 𝕜}
    (hf : ∀ᵐ z : Boundary m ∂volume,
      ACL.LocallyAC (fun t => f (point m z t)) (Ioi 0) ∧
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (fun s => f (point m z s))
          (sobolevDerivative u (verticalIndex m) (point m z t)) t)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (A B : BoundaryLp m 𝕜 p)
    (hA : (fun z : Boundary m => A z) =ᵐ[volume] (fun z => f (point m z a)))
    (hB : (fun z : Boundary m => B z) =ᵐ[volume] (fun z => f (point m z b))) :
    ‖B - A‖ ≤ ∫ t in a..b, verticalProfile u t := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : BorelSpace 𝕜 := ⟨rfl⟩
  let h : Boundary m × ℝ → 𝕜 := fun q =>
    sobolevDerivative u (verticalIndex m) (point m q.1 q.2)
  have hhm : Measurable h :=
    (Lp.stronglyMeasurable (sobolevDerivative u (verticalIndex m))).measurable.comp
      (point_measurePreserving m).measurable
  have hs : Icc a b ⊆ Ioi (0 : ℝ) := fun _ ht => ha.trans_le ht.1
  have hhp : MemLp h p (volume.prod (volume.restrict (Icc a b))) :=
    (halfSpace_memLp_product (sobolevDerivative u (verticalIndex m))).mono_measure
      (Measure.prod_mono le_rfl (Measure.restrict_mono hs le_rfl))
  obtain ⟨hint, hbound⟩ := minkowski_of_product_memLp
    (volume : Measure (Boundary m)) (volume.restrict (Icc a b)) Fact.out hpt hhm hhp
  have heq : (fun z : Boundary m => (B - A) z) =ᵐ[volume]
      (fun z => ∫ t in Icc a b, h (z, t)) := by
    filter_upwards [hf, hA, hB, hint, Lp.coeFn_sub B A] with z hzf hzA hzB hzi hzsub
    rw [hzsub, Pi.sub_apply, hzA, hzB]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact (vertical_integral_eq_sub hzf.1 hzf.2 ha hb (by
      simpa only [uIcc_of_le hab, h, IntegrableOn] using hzi)).symm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => ENNReal.toReal_nonneg))] at hreal
  calc
    ‖B - A‖ = (eLpNorm (fun z => ∫ t in Icc a b, h (z, t)) p volume).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae heq]
    _ ≤ ∫ t in Icc a b, verticalProfile u t := hreal
    _ = ∫ t in a..b, verticalProfile u t := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- The vertical fundamental theorem and Minkowski control every pair of
identified horizontal Lp slices at positive heights. -/
theorem horizontal_slice_increment_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) (u : HalfSobolev m 𝕜 p)
    {f : Space (m + 1) → 𝕜}
    (hf : ∀ᵐ z : Boundary m ∂volume,
      ACL.LocallyAC (fun t => f (point m z t)) (Ioi 0) ∧
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (fun s => f (point m z s))
          (sobolevDerivative u (verticalIndex m) (point m z t)) t)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (A B : BoundaryLp m 𝕜 p)
    (hA : (fun z : Boundary m => A z) =ᵐ[volume] (fun z => f (point m z a)))
    (hB : (fun z : Boundary m => B z) =ᵐ[volume] (fun z => f (point m z b))) :
    ‖B - A‖ ≤ ∫ t in min a b..max a b, verticalProfile u t := by
  rcases le_total a b with hab | hba
  · simpa only [min_eq_left hab, max_eq_right hab] using
      horizontal_slice_increment_le_of_le hpt u hf ha hb hab A B hA hB
  · simpa only [min_eq_right hba, max_eq_left hba, norm_sub_rev A B] using
      horizontal_slice_increment_le_of_le hpt u hf hb ha hba B A hB hA


/-- Countably many ordinary slices may be chosen outside any exceptional set. -/
theorem exists_good_heights {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n ∧ P (t n)) ∧ Tendsto t atTop (𝓝[>] 0) := by
  obtain ⟨r, -, hrpos, hrlim⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  have hex (n : ℕ) : ∃ t : ℝ, t ∈ Ioo 0 (r n) ∧ P t := by
    apply Measure.exists_mem_of_measure_ne_zero_of_ae
      (μ := (volume : Measure ℝ)) (s := Ioo 0 (r n))
    · rw [Real.volume_Ioo]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hrpos n)))
    · exact ae_mono (Measure.restrict_mono (by intro t ht; exact ht.1) le_rfl) hP
  choose t ht using hex
  refine ⟨t, fun n => ⟨(ht n).1.1, (ht n).2⟩, ?_⟩
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n => (ht n).1.1⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_nhdsWithin_iff.mp hrlim).1 (fun n => (ht n).1.1.le)
      (fun n => (ht n).1.2.le)

/-- A vertical ACL curve with integrable derivative through zero has a right endpoint. -/
theorem exists_vertical_endpoint {𝕜 : Type} [RCLike 𝕜] {f h : ℝ → 𝕜}
    (hf : ACL.LocallyAC f (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), HasDerivAt f (h t) t)
    (hi : IntegrableOn h (Ioc (0 : ℝ) 1)) :
    ∃ g : 𝕜, Tendsto f (𝓝[>] 0) (𝓝 g) := by
  apply exists_endpoint_of_integral_control
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hi.norm)
  intro a ha b hb
  have his : IntegrableOn h (uIcc (min a b) (max a b)) := by
    apply hi.mono_set
    intro t ht
    simp only [uIcc_of_le (min_le_max : min a b ≤ max a b)] at ht
    exact ⟨lt_of_lt_of_le (lt_min ha.1 hb.1) ht.1,
      ht.2.trans (max_le ha.2 hb.2)⟩
  have he := vertical_integral_eq_sub hf hd (lt_min ha.1 hb.1)
    (lt_max_of_lt_left ha.1) his
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := h) (min_le_max : min a b ≤ max a b)
  rw [he] at hnorm
  rcases le_total a b with hab | hba
  · simpa only [min_eq_left hab, max_eq_right hab] using hnorm
  · simpa only [min_eq_right hba, max_eq_left hba, norm_sub_rev] using hnorm

/-- The endpoint of the continuous Lp slice curve is the boundary value of
an actual vertical ACL representative of the Sobolev class. -/
theorem slice_hasVerticalBoundaryValues {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) {u : HalfSobolev m 𝕜 p}
    {F : ℝ → BoundaryLp m 𝕜 p} (hF : IsSliceRepresentative u F) :
    HasVerticalBoundaryValues u (F 0) := by
  classical
  obtain ⟨f, huf, hf⟩ := vertical_acl m 𝕜 p u
  refine ⟨f, huf, ?_⟩
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hswap := (halfSpace_memLp_product (sobolevDerivative u (verticalIndex m))).comp_measurePreserving
    (Measure.measurePreserving_swap (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := (volume : Measure (Boundary m))))
  have hsections := MemLp_sections hp0 hpt hswap
  have hinter : ∀ᵐ z : Boundary m ∂volume,
      IntegrableOn (fun t => sobolevDerivative u (verticalIndex m) (point m z t))
        (Ioc (0 : ℝ) 1) := by
    filter_upwards [hsections] with z hz
    exact (hz.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)).integrable Fact.out
  have hgood : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (fun z : Boundary m => F t z) =ᵐ[volume] (fun z => f (point m z t)) := by
    filter_upwards [hF.2, ae_on_heights huf] with t ht huft
    exact ht.trans huft
  obtain ⟨t, htgood, htlim⟩ := exists_good_heights hgood
  have hFlim : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) :=
    (hF.1 0 (by simp)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hFlim.comp htlim)).exists_seq_tendsto_ae
  have heq : ∀ᵐ z : Boundary m ∂volume, ∀ n : ℕ,
      F (t n) z = f (point m z (t n)) :=
    ae_all_iff.mpr (fun n => (htgood n).2)
  filter_upwards [hf, hinter, hae, heq] with z hz hzi hza hze
  obtain ⟨g, hg⟩ := exists_vertical_endpoint hz.1 hz.2 hzi
  refine ⟨hz.1, hz.2, ?_⟩
  have hgseq := hg.comp (htlim.comp hns.tendsto_atTop)
  have hFseq : Tendsto (fun n => f (point m z (t (ns n)))) atTop (𝓝 (F 0 z)) := by
    exact hza.congr' (Eventually.of_forall fun n => hze (ns n))
  exact (tendsto_nhds_unique hgseq hFseq) ▸ hg


set_option maxHeartbeats 1200000 in
/-- Every genuine component is Lp on almost every vertical line. -/
theorem halfSpace_memLp_vertical_lines {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (v : DomainLp 𝕜 (halfSpace m) p) :
    ∀ᵐ z : Boundary m ∂volume,
      MemLp (fun t => v (point m z t)) p (volume.restrict (Ioi (0 : ℝ))) := by
  have h := (halfSpace_memLp_product v).comp_measurePreserving
    (Measure.measurePreserving_swap
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure (Boundary m))))
  exact MemLp_sections hp0 hpt h

/-- The vertical line derivatives are integrable even through the boundary. -/
theorem halfSpace_integrableOn_vertical_lines {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (v : DomainLp 𝕜 (halfSpace m) p) :
    ∀ᵐ z : Boundary m ∂volume,
      ∀ R : ℝ, IntegrableOn (fun t => v (point m z t)) (Ioc 0 R) := by
  filter_upwards [halfSpace_memLp_vertical_lines
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hpt v] with z hz
  intro R
  have hi : MemLp (fun t => v (point m z t)) p (volume.restrict (Ioc 0 R)) :=
    hz.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  exact hi.integrable Fact.out

/-- Compact positive intervals admit the linewise FTC hypothesis. -/
theorem halfSpace_integrableOn_positive_vertical_intervals {m : ℕ} {𝕜 : Type}
    [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (v : DomainLp 𝕜 (halfSpace m) p) :
    ∀ᵐ z : Boundary m ∂volume,
      ∀ a b : ℝ, 0 < a → 0 < b →
        IntegrableOn (fun t => v (point m z t)) (uIcc a b) := by
  filter_upwards [halfSpace_memLp_vertical_lines
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hpt v] with z hz
  intro a b ha hb
  have hs : uIcc a b ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  have hi : MemLp (fun t => v (point m z t)) p (volume.restrict (uIcc a b)) :=
    hz.mono_measure (Measure.restrict_mono hs le_rfl)
  letI : IsFiniteMeasure (volume.restrict (uIcc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_uIcc.measure_lt_top.ne
  exact hi.integrable Fact.out

/-- The graph norm has two distinct relevant coordinates. -/
theorem underlying_add_verticalDerivative_norm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) :
    ‖sobolevUnderlying u‖ + ‖sobolevDerivative u (verticalIndex m)‖ ≤ ‖u‖ := by
  classical
  have hne : zeroSobolevIndex (m + 1) 1 ≠ verticalIndex m := by
    intro h
    have hv := congrArg Subtype.val h
    simp [zeroSobolevIndex, verticalIndex] at hv
  rw [sobolev_norm]
  change ‖sobolevDerivative u (zeroSobolevIndex (m + 1) 1)‖ + _ ≤ _
  calc
    _ = ∑ i ∈ {zeroSobolevIndex (m + 1) 1, verticalIndex m}, ‖sobolevDerivative u i‖ := by
      rw [Finset.sum_pair hne]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

/-- A single full-measure family of vertical lines obeys FTC simultaneously
at every pair of positive heights. -/
theorem vertical_acl_with_integral_identity {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) (u : HalfSobolev m 𝕜 p) :
    ∃ f : Space (m + 1) → 𝕜,
      sobolevUnderlying u =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] f ∧
      ∀ᵐ z : Boundary m ∂volume,
        ACL.LocallyAC (fun t => f (point m z t)) (Ioi 0) ∧
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          HasDerivAt (fun s => f (point m z s))
            (sobolevDerivative u (verticalIndex m) (point m z t)) t) ∧
        (∀ R : ℝ, IntegrableOn
          (fun t => sobolevDerivative u (verticalIndex m) (point m z t)) (Ioc 0 R)) ∧
        ∀ a b : ℝ, 0 < a → 0 < b →
          (∫ t in a..b, sobolevDerivative u (verticalIndex m) (point m z t)) =
            f (point m z b) - f (point m z a) := by
  obtain ⟨f, huf, hf⟩ := vertical_acl m 𝕜 p u
  refine ⟨f, huf, ?_⟩
  filter_upwards [hf,
    halfSpace_integrableOn_vertical_lines hpt (sobolevDerivative u (verticalIndex m)),
    halfSpace_integrableOn_positive_vertical_intervals hpt (sobolevDerivative u (verticalIndex m))]
    with z hz hi hi'
  refine ⟨hz.1, hz.2, hi, ?_⟩
  intro a b ha hb
  exact vertical_integral_eq_sub hz.1 hz.2 ha hb (hi' a b ha hb)




/-- An almost everywhere subset of the positive half-line is dense there. -/
theorem dense_positive_good {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t) :
    Dense {t : Ioi (0 : ℝ) | P t} := by
  have hd : Dense {t : ℝ | 0 < t → P t} :=
    Measure.dense_of_ae ((ae_restrict_iff' measurableSet_Ioi).mp hP)
  have h := hd.preimage (f := ((↑) : Ioi (0 : ℝ) → ℝ)) isOpen_Ioi.isOpenMap_subtype_val
  have he : ((↑) : Ioi (0 : ℝ) → ℝ) ⁻¹' {t : ℝ | 0 < t → P t} =
      {t : Ioi (0 : ℝ) | P t} := by
    ext t
    exact ⟨fun ht => ht t.property, fun ht _ => ht⟩
  rwa [he] at h

/-- The primitive is continuous at every strictly positive height. -/
theorem continuousOn_primitive_positive {A : ℝ → ℝ}
    (hA : ∀ R : ℝ, 0 < R → IntervalIntegrable A volume 0 R) :
    ContinuousOn (fun t => ∫ a in (0 : ℝ)..t, A a) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hc : ContinuousOn (fun t => ∫ a in (0 : ℝ)..t, A a) (Icc 0 (t + 1)) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ t + 1 by linarith)] using
      intervalIntegral.continuousOn_primitive_interval' (hA (t + 1) (by linarith)) left_mem_uIcc
  exact (hc.continuousAt (Icc_mem_nhds ht (by linarith))).continuousWithinAt

theorem abs_primitive_sub_eq_integral {A : ℝ → ℝ}
    (hA : ∀ R : ℝ, 0 < R → IntervalIntegrable A volume 0 R)
    (hn : ∀ t, 0 ≤ A t) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |(∫ t in (0 : ℝ)..a, A t) - ∫ t in (0 : ℝ)..b, A t| =
      ∫ t in min a b..max a b, A t := by
  have he := intervalIntegral.integral_interval_sub_left (hA a ha) (hA b hb)
  rw [he]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab, intervalIntegral.integral_symm a b,
      abs_neg, abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hab hn)]
  · rw [min_eq_right hba, max_eq_left hba,
      abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hba hn)]

/-- Complete the a.e.-defined slices using their exact integral modulus. -/
theorem extend_ae_slices_of_integral_control {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {P : ℝ → Prop} {f : ℝ → E} {A : ℝ → ℝ}
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t)
    (hA : ∀ R : ℝ, 0 < R → IntervalIntegrable A volume 0 R)
    (hn : ∀ t, 0 ≤ A t)
    (hinc : ∀ a b : ℝ, 0 < a → 0 < b → P a → P b →
      ‖f b - f a‖ ≤ ∫ t in min a b..max a b, A t) :
    ∃ F : ℝ → E, ContinuousOn F (Ioi 0) ∧
      (∀ t, 0 < t → P t → F t = f t) ∧
      (∀ a b : ℝ, 0 < a → 0 < b →
        ‖F b - F a‖ ≤ ∫ t in min a b..max a b, A t) := by
  classical
  let B := Ioi (0 : ℝ)
  let S : Set B := {t | P t}
  let J : B → ℝ := fun t => ∫ a in (0 : ℝ)..t.val, A a
  have hJ : Continuous J :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_primitive_positive hA)
  have hd : Dense S := dense_positive_good hP
  obtain ⟨H, hH, hEq, hcontrol⟩ := exists_continuous_extension_of_control
    hd.isDenseInducing_val (fun t : S => f t.val.val) J hJ (by
      intro a b
      rw [abs_primitive_sub_eq_integral hA hn a.val.property b.val.property]
      exact (show dist (f a.val.val) (f b.val.val) = ‖f b.val.val - f a.val.val‖ from
        dist_eq_norm' _ _).trans_le (hinc _ _ a.val.property b.val.property a.property b.property))
  let F : ℝ → E := fun t => if ht : 0 < t then H ⟨t, ht⟩ else 0
  refine ⟨F, ?_, ?_, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    convert hH using 1
    ext t
    exact dite_eq_left t.property
  · intro t ht hpt
    simpa only [F, dite_eq_left ht] using hEq (⟨⟨t, ht⟩, hpt⟩ : S)
  · intro a b ha hb
    have hc := hcontrol (⟨a, ha⟩ : B) (⟨b, hb⟩ : B)
    rw [abs_primitive_sub_eq_integral hA hn ha hb] at hc
    simpa only [F, dite_eq_left ha, dite_eq_left hb, dist_eq_norm'] using hc



/-- The genuine product Lp and vertical ACL data determine a continuous slice
curve, with the exact oscillation bound, all the way to height zero. -/
theorem exists_slice_representative_with_control {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) (u : HalfSobolev m 𝕜 p) :
    ∃ F : ℝ → BoundaryLp m 𝕜 p, IsSliceRepresentative u F ∧
      Tendsto F (𝓝[>] 0) (𝓝 (F 0)) ∧
      (∀ a b : ℝ, 0 < a → 0 < b →
        ‖F b - F a‖ ≤ ∫ t in min a b..max a b, verticalProfile u t) ∧
      (∀ t : ℝ, 0 < t →
        ‖F 0‖ ≤ ‖F t‖ + ∫ a in (0 : ℝ)..t, verticalProfile u a) := by
  classical
  obtain ⟨f, huf, hf⟩ := vertical_acl m 𝕜 p u
  let raw : ℝ → Boundary m → 𝕜 := fun t z => sobolevUnderlying u (point m z t)
  let P : ℝ → Prop := fun t => MemLp (raw t) p volume ∧
    (raw t) =ᵐ[volume] (fun z => f (point m z t))
  have hP : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t :=
    (halfSpace_memLp_sections (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
      hpt (sobolevUnderlying u)).and (ae_on_heights huf)
  let L : ℝ → BoundaryLp m 𝕜 p := fun t =>
    if ht : MemLp (raw t) p volume then ht.toLp (raw t) else 0
  have hL (t : ℝ) (ht : P t) :
      (fun z : Boundary m => L t z) =ᵐ[volume] (raw t) := by
    simpa only [L, dite_eq_left ht.1] using ht.1.coeFn_toLp
  have hA : ∀ R : ℝ, 0 < R → IntervalIntegrable (verticalProfile u) volume 0 R := by
    intro R hR
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr
      (verticalProfile_integrableOn hpt u R)
  obtain ⟨G, hG, hEq, hinc⟩ := extend_ae_slices_of_integral_control hP hA
    (fun _ => ENNReal.toReal_nonneg) (by
      intro a b ha hb hpa hpb
      exact horizontal_slice_increment_le hpt u hf ha hb (L a) (L b)
        ((hL a hpa).trans hpa.2) ((hL b hpb).trans hpb.2))
  obtain ⟨F, hF, hFG, hFlim, hzero⟩ := extend_to_zero_of_integral_control hG hA hinc
  refine ⟨F, ⟨hF, ?_⟩, hFlim, ?_, hzero⟩
  · filter_upwards [hP, ae_restrict_mem measurableSet_Ioi] with t ht htpos
    rw [hFG htpos, hEq t htpos ht]
    exact hL t ht
  · intro a b ha hb
    rw [hFG ha, hFG hb]
    exact hinc a b ha hb

/-- The ordinary half-space trace, including p = 1. The operator is determined
by its continuous horizontal slices, and its endpoint is the vertical ACL value. -/
theorem flat_trace_exists : FlatTraceExpected.TraceExists := by
  intro m _hm 𝕜 _ p _ hpt
  have hex := exists_slice_representative_with_control (m := m) (𝕜 := 𝕜) hpt
  obtain ⟨T, hT, hTEq⟩ := trace_of_slice_representatives
    (fun u => (hex u).imp (fun _ h => h.1)) 1 (by
      intro u F hF
      obtain ⟨G, hG, -, -, hGzero⟩ := hex u
      have he : F 0 = G 0 := slice_unique m 𝕜 p u F G hF hG (by simp)
      rw [he, one_mul]
      exact (slice_endpoint_norm_le hpt hG hGzero).trans
        (underlying_add_verticalDerivative_norm_le u))
  refine ⟨1, zero_le_one, T, hT, ?_, ?_⟩
  · intro u
    obtain ⟨F, hF, hFlim, hinc, hzero⟩ := hex u
    have he : F 0 = T u := (hTEq u F hF).symm
    refine ⟨F, hF, he, he ▸ hFlim, ?_, ?_, hinc, ?_, ?_⟩
    · intro R _
      exact verticalProfile_integrableOn hpt u R
    · exact halfSpace_memLp_sections
        (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hpt
        (sobolevDerivative u (verticalIndex m))
    · simpa only [← he] using hzero
    · rw [← he]
      exact slice_hasVerticalBoundaryValues hpt hF
  · intro u f hf huf
    obtain ⟨F, hF, -, -, -⟩ := hex u
    have hg : HasVerticalBoundaryValues u (T u) := by
      rw [hTEq u F hF]
      exact slice_hasVerticalBoundaryValues hpt hF
    exact vertical_boundary_compatibility m 𝕜 p u (T u) f hg hf huf


end P102.Trace
