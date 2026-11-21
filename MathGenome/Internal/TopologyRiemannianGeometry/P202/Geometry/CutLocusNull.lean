import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutLocusNull
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CutPolarDomain
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.Jacobian
import Batteries.Tactic.OpenPrivate
/-! Cut-locus nullity, paper.tex:4383–4402. The radial graph argument
uses ordinary linear tangent coordinates and the actual metric normalization.
The canonical volume is transferred using its accepted density chart formula. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology CompactlySupported
namespace P202.Geometry.CutLocusNull
universe u

/-- A measurable set meeting every positive ray at most once is Lebesgue null. -/
theorem radial_unique_null {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E}
    (hs : MeasurableSet s) (hzero : (0 : E) ∉ s)
    (hu : ∀ (x : Metric.sphere (0 : E) 1) (a b : Ioi (0 : ℝ)),
      a.val • x.val ∈ s → b.val • x.val ∈ s → a = b) : μ s = 0 := by
  let e := homeomorphUnitSphereProd E
  let t : Set (Metric.sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
    (fun z => (e.symm z).val) ⁻¹' s
  have ht : MeasurableSet t := hs.preimage
    (measurable_subtype_coe.comp e.symm.measurable)
  have hnull : (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) t = 0 := by
    apply Measure.measure_prod_null_of_ae_null ht
    apply Filter.Eventually.of_forall
    intro x
    have hsub : (Prod.mk x ⁻¹' t).Subsingleton := by
      intro a ha b hb
      exact hu x a b ha hb
    apply withDensity_absolutelyContinuous
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply]
    exact (hsub.image _).measure_zero volume
  have hp := μ.measurePreserving_homeomorphUnitSphereProd.measure_preimage ht.nullMeasurableSet
  have he : e ⁻¹' t = (Subtype.val : ({0}ᶜ : Set E) → E) ⁻¹' s := by
    ext x
    simp [t]
  rw [he, (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl).comap_apply] at hp
  have hsz : s ⊆ ({0}ᶜ : Set E) := fun x hx hx0 => hzero ((mem_singleton_iff.mp hx0) ▸ hx)
  rw [Subtype.image_preimage_coe, inter_eq_self_of_subset_right hsz] at hp
  exact hp.trans hnull

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.GeodesicData P202.ExponentialData P202.CutTimeData
  P202.CutPolarData
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem coordinate_metric_norm_continuous (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Continuous (fun x : Euclidean n => tangentNorm g p (E.symm x)) := by
  let B := ((g.form p).compl₁₂ E.symm.toLinearMap E.symm.toLinearMap).toContinuousBilinearMap
  have hB : ContDiff ℝ (⊤ : ℕ∞) (fun x => B x x) := B.contDiff.clm_apply contDiff_id
  exact Real.continuous_sqrt.comp hB.continuous

theorem coordinate_metric_norm_pos (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (x : ({0}ᶜ : Set (Euclidean n))) : 0 < tangentNorm g p (E.symm x.val) := by
  apply lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p _)
  intro hz
  have hv := (SmoothMetrics.tangentNorm_eq_zero_iff g p _).mp hz.symm
  have h0 : x.val = 0 := by simpa using congrArg E hv
  exact x.property h0

def coordinateDirection (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (x : ({0}ᶜ : Set (Euclidean n))) : UnitDirection g p :=
  ⟨(tangentNorm g p (E.symm x.val))⁻¹ • E.symm x.val, by
    rw [SmoothMetrics.tangentNorm_smul,
      abs_of_pos (inv_pos.mpr (coordinate_metric_norm_pos g p E x)),
      inv_mul_cancel₀ (ne_of_gt (coordinate_metric_norm_pos g p E x))]⟩

theorem coordinateDirection_continuous (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    letI := directionTopology g p E
    Continuous (coordinateDirection g p E) := by
  letI := directionTopology g p E
  apply continuous_induced_rng.mpr
  have hr : Continuous (fun x : ({0}ᶜ : Set (Euclidean n)) => tangentNorm g p (E.symm x.val)) :=
    (coordinate_metric_norm_continuous g p E).comp continuous_subtype_val
  have hi := hr.inv₀ (fun x => ne_of_gt (coordinate_metric_norm_pos g p E x))
  convert hi.smul continuous_subtype_val using 1
  funext x
  simp [coordinateDirection]

/-- Finite cut vectors in linear tangent coordinates, expressed by the radial graph
equation on the punctured tangent space. Equality to a finite real radius excludes ∞. -/
def coordinateCutVectors (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) : Set (Euclidean n) :=
  Subtype.val '' {x : ({0}ᶜ : Set (Euclidean n)) |
    ENNReal.ofReal (tangentNorm g p (E.symm x.val)) =
      cutTime g F p (coordinateDirection g p E x)}

theorem coordinateCutVectors_measurable (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hc : letI := directionTopology g p E; Continuous (cutTime g F p)) :
    MeasurableSet (coordinateCutVectors g F p E) := by
  letI := directionTopology g p E
  apply (measurableSet_singleton (0 : Euclidean n)).compl.subtype_image
  apply isClosed_eq _ _ |>.measurableSet
  · exact ENNReal.continuous_ofReal.comp
      ((coordinate_metric_norm_continuous g p E).comp continuous_subtype_val)
  · exact hc.comp (coordinateDirection_continuous g p E)

theorem coordinateDirection_smul (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (x : ({0}ᶜ : Set (Euclidean n))) (a : ℝ) (ha : 0 < a) :
    coordinateDirection g p E ⟨a • x.val, smul_ne_zero ha.ne' x.property⟩ =
      coordinateDirection g p E x := by
  apply Subtype.ext
  simp only [coordinateDirection, map_smul, SmoothMetrics.tangentNorm_smul,
    abs_of_pos ha, mul_inv_rev, smul_smul]
  congr 1
  field_simp

theorem coordinateCutVectors_null (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hc : letI := directionTopology g p E; Continuous (cutTime g F p)) :
    MeasureTheory.volume (coordinateCutVectors g F p E) = 0 := by
  apply radial_unique_null volume (coordinateCutVectors_measurable g F p E hc)
  · rintro ⟨x, hx, h0⟩
    exact x.property h0
  · intro x a b ha hb
    obtain ⟨y, hy, hya⟩ := ha
    obtain ⟨z, hz, hzb⟩ := hb
    have hx0 : x.val ≠ 0 := by
      intro h
      have hn := x.property
      simp [h] at hn
    let w : ({0}ᶜ : Set (Euclidean n)) := ⟨x.val, hx0⟩
    have hdy : coordinateDirection g p E y = coordinateDirection g p E w := by
      exact (congrArg (coordinateDirection g p E) (Subtype.ext hya)).trans
        (coordinateDirection_smul g p E w a.val a.property)
    have hdz : coordinateDirection g p E z = coordinateDirection g p E w := by
      exact (congrArg (coordinateDirection g p E) (Subtype.ext hzb)).trans
        (coordinateDirection_smul g p E w b.val b.property)
    change ENNReal.ofReal (tangentNorm g p (E.symm y.val)) = _ at hy
    change ENNReal.ofReal (tangentNorm g p (E.symm z.val)) = _ at hz
    have heq : ENNReal.ofReal (tangentNorm g p (E.symm y.val)) =
        ENNReal.ofReal (tangentNorm g p (E.symm z.val)) :=
      hy.trans ((congrArg (cutTime g F p) (hdy.trans hdz.symm)).trans hz.symm)
    have heq' := congrArg ENNReal.toReal heq
    rw [ENNReal.toReal_ofReal (SmoothMetrics.tangentNorm_nonneg g p _),
      ENNReal.toReal_ofReal (SmoothMetrics.tangentNorm_nonneg g p _)] at heq'
    simp only [hya, hzb, map_smul, SmoothMetrics.tangentNorm_smul,
      abs_of_pos a.property.out, abs_of_pos b.property.out] at heq'
    apply Subtype.ext
    exact mul_right_cancel₀ (ne_of_gt (coordinate_metric_norm_pos g p E w)) heq'

/-- Every cut endpoint is the exponential of a finite cut vector. -/
theorem cutPoint_mem_coordinate_image (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (v : UnitDirection g p)
    (hfin : cutTime g F p v ≠ ⊤) (hr : 0 < (cutTime g F p v).toReal) :
    cutPoint g F p v hfin ∈
      (fun x => fiberExponential F p (E.symm x)) '' coordinateCutVectors g F p E := by
  let r := (cutTime g F p v).toReal
  change 0 < r at hr
  have hv : v.val ≠ 0 := by
    intro h0
    have h1 := v.property
    rw [h0, SmoothMetrics.tangentNorm_zero] at h1
    exact zero_ne_one h1
  have hx0 : E (r • v.val) ≠ 0 := by
    intro h0
    have hzero : r • v.val = 0 := by simpa using congrArg E.symm h0
    exact smul_ne_zero hr.ne' hv hzero
  let x : ({0}ᶜ : Set (Euclidean n)) := ⟨E (r • v.val),hx0⟩
  have hrad : tangentNorm g p (E.symm x.val) = r := by
    simp only [x, E.symm_apply_apply, SmoothMetrics.tangentNorm_smul,
      abs_of_pos hr, v.property, mul_one]
  have hdir : coordinateDirection g p E x = v := by
    apply Subtype.ext
    change (tangentNorm g p (E.symm x.val))⁻¹ • E.symm x.val = v.val
    rw [hrad]
    simp only [x, E.symm_apply_apply, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  refine ⟨x.val, ?_, ?_⟩
  · refine ⟨x, ?_, rfl⟩
    change ENNReal.ofReal (tangentNorm g p (E.symm x.val)) =
      cutTime g F p (coordinateDirection g p E x)
    rw [hrad, hdir]
    exact ENNReal.ofReal_toReal hfin
  · simp only [x, E.symm_apply_apply]
    rfl

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.MetricVolumeData P202.MetricData P202.VolumeData

open private chartEmbedding chartEmbedding_measurableEmbedding chartWeight
  measure_chart_local from MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume

/-- The null-set bridge uses the measure with the constructed smooth metric
density, in each chart, followed by a countable chart cover. -/
theorem coordinate_null (g : RiemannianMetric S) (s : Set M)
    (hs : ∀ (c : ModelChart n .euclidean M), c ∈ S.smoothStructure.val →
      MeasureTheory.volume ((fun p => (c p).val) '' (s ∩ c.source)) = 0) :
    P202.CutNullData.volume g s = 0 := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
  let μ := P202.CutNullData.volume g
  have hμ := (RiemannianVolume.measure_representation_exists g).choose_spec.1
  letI : μ.Regular := hμ.1
  have hlocal (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val) :
      μ (s ∩ c.source) = 0 := by
    let K := (tangentStructure S).fiberCoordinates
    let t : Set c.source := Subtype.val ⁻¹' s
    have ht : (MeasureTheory.volume.comap (chartEmbedding c)) t = 0 := by
      rw [(chartEmbedding_measurableEmbedding c).comap_apply]
      convert hs c hc using 2
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.val, ⟨hp, p.property⟩, rfl⟩
      · rintro ⟨p, ⟨hp, hpc⟩, rfl⟩
        exact ⟨⟨p,hpc⟩, hp, rfl⟩
    have hz := withDensity_absolutelyContinuous
      (MeasureTheory.volume.comap (chartEmbedding c))
      (fun p => ENNReal.ofReal (chartWeight g K c hc p)) ht
    rw [← measure_chart_local g μ hμ.2.2 K c hc,
      (MeasurableEmbedding.subtype_coe c.open_source.measurableSet).comap_apply,
      Subtype.image_preimage_coe] at hz
    simpa only [inter_comm] using hz
  obtain ⟨r, hr, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun c : {c // c ∈ S.smoothStructure.val} => c.val.source)
    (fun c => c.val.open_source) (by
      intro p _
      obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p
      exact mem_iUnion.mpr ⟨⟨c,hc⟩,hp⟩)
  apply measure_mono_null (t := ⋃ c ∈ r, s ∩ c.val.source)
  · intro p hp
    obtain ⟨c,hcr,hpc⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
    exact mem_iUnion₂.mpr ⟨c,hcr,hp,hpc⟩
  · exact (measure_biUnion_null_iff hr).mpr (fun c _ => hlocal c.val c.property)

open P202.ConnectionData P202.CompleteExponentialData

/-- The smooth exponential sends coordinate null sets to Riemannian null
sets. The Euclidean differentiable-image theorem itself supplies the countable
local derivative-bound argument; no injectivity is needed. -/
theorem exponential_image_null (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (s : Set (Euclidean n)) (hs : MeasureTheory.volume s = 0) :
    P202.CutNullData.volume g ((fun x => fiberExponential F p (E.symm x)) '' s) = 0 := by
  apply coordinate_null g
  intro c hc
  let f : Euclidean n → M := fun x => fiberExponential F p (E.symm x)
  let h : Euclidean n → Euclidean n := fun x => (c (f x)).val
  have hd : DifferentiableOn ℝ h (s ∩ f ⁻¹' c.source) := by
    intro x hx
    exact (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis
      C F hF p E c hc x (hfull _) hx.2).differentiableAt (by simp) |>.differentiableWithinAt
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := MeasureTheory.volume) hd (measure_mono_null inter_subset_left hs)
  convert hz using 2
  ext y
  constructor
  · rintro ⟨q,⟨⟨x,hxs,rfl⟩,hxc⟩,rfl⟩
    exact ⟨x,⟨hxs,hxc⟩,rfl⟩
  · rintro ⟨x,⟨hxs,hxc⟩,rfl⟩
    exact ⟨f x,⟨⟨x,hxs,rfl⟩,hxc⟩,rfl⟩

open P202.LeviCivitaData P202.CompletenessData P202.CurvatureData

/-- Lemma `lem:p202-cut-null`, for the canonical Riemannian Borel measure. -/
theorem cut_locus_null : P202Specs.Geometry.CutLocusNull.cut_locus_nullType.{u} := by
  intro n M _ _ S g hn hcomplete C hC F hF p
  obtain ⟨R, hR, _⟩ := CurvatureAlgebra.tensor_exists_unique C
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  have hct : letI := directionTopology g p E; Continuous (cutTime g F p) :=
    CutPolarDomain.cut_time_continuous S g hn hcomplete C hC R hR F hF p E
  have hs := coordinateCutVectors_null g F p E hct
  have hfull : FullExponentialAt F p :=
    HopfRinow.full_exponential_of_geodesicallyComplete C
      ((HopfRinow.hopf_rinow S g C hC).1.mp hcomplete) F hF p
  apply measure_mono_null ?_ (exponential_image_null g C F hF p hfull E _ hs)
  rintro q ⟨v, hfin, rfl⟩
  exact cutPoint_mem_coordinate_image g F p E v hfin
    (((CutTime.cut_time_interval S g hn hcomplete C hC F hF p v).2.2.2.2.1 hfin).2.1)

end P202.Geometry.CutLocusNull
