import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RiemannianVolume
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Topology CompactlySupported ENNReal
namespace P202.Geometry.RiemannianVolume
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.MetricVolumeData
  SmoothManifolds.ExteriorData SmoothManifolds.OrientationData
  SmoothManifolds.DensityIntegrationData P202.MetricData P202.VolumeData
universe u

noncomputable abbrev riemannianDensity := @P202.VolumeData.density
noncomputable abbrev riemannianVolumeForm := @P202.VolumeData.volumeForm
noncomputable abbrev densityIntegral := @P202.VolumeData.densityIntegral
noncomputable abbrev integral := @P202.VolumeData.integral

theorem metric_bridge : P202Specs.Geometry.RiemannianVolume.metric_bridgeType.{u} := by
  intro n a M _ S g p
  rfl

theorem density_properties : P202Specs.Geometry.RiemannianVolume.density_propertiesType.{u} := by
  intro n a M _ S g
  refine ⟨(fun _ _ => rfl), MetricVolumeResults.metricDensity_smooth (libraryMetric g),
    ?_, MetricVolumeResults.metricDensity_positive (libraryMetric g),
    MetricVolumeResults.metricDensity_nonzero (libraryMetric g)⟩
  exact DensityIntegrationResults.smooth_density_continuous _
    (MetricVolumeResults.metricDensity_smooth (libraryMetric g))

theorem density_unique : P202Specs.Geometry.RiemannianVolume.density_uniqueType.{u} := by
  intro n a M _ S g ρ hρ
  exact MetricVolumeResults.metricDensity_unique (libraryMetric g) ρ hρ

theorem density_coordinates : P202Specs.Geometry.RiemannianVolume.density_coordinatesType.{u} := by
  intro n a M _ S g K c hc p
  exact ⟨MetricVolumeResults.metricDensity_coefficient (libraryMetric g) K c hc p,
    Real.sqrt_pos.mpr (MetricVolumeResults.metricMatrix_det_pos (libraryMetric g) K c hc p)⟩

theorem density_overlap : P202Specs.Geometry.RiemannianVolume.density_overlapType.{u} := by
  intro n a M _ S g K c d hc hd p
  exact MetricVolumeResults.density_transition K c d hc hd p (density g p.val)

theorem density_zero_dimension :
    P202Specs.Geometry.RiemannianVolume.density_zero_dimensionType.{u} := by
  intro a M _ S g p
  exact MetricVolumeResults.zero_norm (libraryMetric g) p

theorem volumeForm_normalization {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (o : Orientation S) : IsMetricVolume (libraryMetric g) o (volumeForm g o) :=
  (MetricVolumeResults.volume_exists_unique S (cotangentBundle S)
    (topFormBundle S) (libraryMetric g) o).choose_spec.1

theorem volumeForm_properties :
    P202Specs.Geometry.RiemannianVolume.volumeForm_propertiesType.{u} := by
  intro n a M _ S g o
  have hω := volumeForm_normalization g o
  refine ⟨hω, ?_, ?_⟩
  · obtain ⟨s, hs, _⟩ := (OrientationResults.signed_charts S o.val).mp o.property
    funext p
    apply Subtype.ext
    funext v
    exact MetricVolumeResults.metricVolume_abs_pairing (libraryMetric g) o
      (volumeForm g o) hω s hs p v
  · intro p v hv
    rw [MetricVolumeResults.metricVolume_evaluate_positive (libraryMetric g) o
      (volumeForm g o) hω p v hv]
    exact MetricVolumeResults.determinantNorm_pos (libraryMetric g) p v hv.choose

theorem volumeForm_coordinates :
    P202Specs.Geometry.RiemannianVolume.volumeForm_coordinatesType.{u} := by
  intro n a M _ S g o s hs K c hc p
  exact MetricVolumeResults.volume_coordinates S (cotangentBundle S) (topFormBundle S)
    (libraryMetric g) o (volumeForm g o) (volumeForm_normalization g o) s hs K c hc p

theorem densityIntegral_properties :
    P202Specs.Geometry.RiemannianVolume.densityIntegral_propertiesType.{u} := by
  intro n a M _ S
  exact (DensityIntegralResults.integral_exists_unique S).choose_spec

theorem integral_chart : P202Specs.Geometry.RiemannianVolume.integral_chartType.{u} := by
  intro n a M _ S g f K c hc hf
  apply (densityIntegral_properties S).1.2.2 K c hc
  intro p hp
  exact hf (DensityIntegralResults.support_weight_subset (fun p => f p) (density g) hp).1

theorem boundaryDensity_exists :
    P202Specs.Geometry.RiemannianVolume.boundaryDensity_existsType.{u} := by
  intro n a M _ S g
  obtain ⟨B, hB⟩ := BoundaryRegularLevels.natural_boundary_exists S
  let L := SmoothManifolds.differential B S Subtype.val hB.1
  have hL := SmoothManifolds.differential_spec B S Subtype.val hB.1
  let i : SmoothImmersion B S Subtype.val :=
    ⟨hB.1, L, hL, fun p =>
      BoundaryRegularLevels.natural_boundary_inclusion_injective S B hB p (L p) (hL p)⟩
  let gB := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i
  refine ⟨B, hB, gB, density gB, ?_, rfl, ?_, ?_⟩
  · intro p v w
    rfl
  · exact (density_properties gB).2.1
  · exact (density_properties gB).2.2.2.1

/-- Positivity follows from local Lebesgue integration and a nonnegative
partition of unity. It is not an extra axiom on the global density integral. -/
theorem densityIntegral_nonneg {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (ρ : CompactDensity S)
    (hρ : ∀ p v, 0 ≤ (ρ.field p).val v) : 0 ≤ densityIntegral S ρ := by
  change 0 ≤ P202.VolumeData.densityIntegral S ρ
  obtain ⟨w, hw, hsub⟩ := exists_smooth_partition S
    (fun c : {c // c ∈ S.smoothStructure.val} => c.val.source)
    (fun c => c.val.open_source) (fun p => by
      obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
      exact ⟨⟨c, hc⟩, hp⟩)
  let P : DensityIntegralResults.IntegrationPartition S :=
    ⟨w, (fun c => continuous_iff_continuousAt.mpr (fun p =>
      ((scalarContDiffAt_iff _ _ _ _).mp (hw.1 c p)).1)),
      hw.2.2.1, hsub, hw.2.2.2⟩
  obtain ⟨s, _, he⟩ := DensityIntegralResults.partition_decomposition P ρ
  rw [DensityIntegralResults.integral_sum (densityIntegral_properties S).1 s
    (fun c => DensityIntegralResults.partitionTerm P c ρ) ρ he]
  apply Finset.sum_nonneg
  intro c _
  rw [(densityIntegral_properties S).1.2.2 (tangentStructure S).fiberCoordinates c.val c.property _
    (DensityIntegralResults.partitionTerm_support P c ρ)]
  unfold DensityIntegrationData.coordinateIntegral
  apply MeasureTheory.integral_nonneg
  intro x
  unfold DensityIntegrationData.coordinateDensity LocalIntegrationData.extendModel
  split
  · dsimp only
    split
    · exact mul_nonneg (hw.2.1 c _) (hρ _ _)
    · exact le_rfl
  · exact le_rfl

/-- The Riemannian integral is nonnegative on nonnegative scalar functions. -/
theorem integral_nonneg {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f : C_c(M, ℝ)) (hf : ∀ p, 0 ≤ f p) : 0 ≤ integral g f := by
  apply densityIntegral_nonneg
  intro p v
  change 0 ≤ f p * (density g p).val v
  apply mul_nonneg (hf p)
  exact Real.sqrt_nonneg _

theorem integral_add {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f h : C_c(M, ℝ)) : integral g (f + h) = integral g f + integral g h := by
  apply (densityIntegral_properties S).1.1
  funext p
  exact add_smul (f p) (h p) (density g p)

theorem integral_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (t : ℝ) (f : C_c(M, ℝ)) : integral g (t • f) = t * integral g f := by
  apply (densityIntegral_properties S).1.2.1
  funext p
  exact mul_smul t (f p) (density g p)

/-- Riesz--Markov constructs the Borel volume from the positive density
integral. This proves compact finiteness, rather than assuming a measure. -/
theorem measure_representation_exists :
    P202Specs.Geometry.RiemannianVolume.measure_representation_existsType.{u} := by
  intro n a M _ S g
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  letI : T2Space M := S.topologicalManifold.hausdorff
  letI : LocallyCompactSpace M := SmoothManifolds.TopologicalManifold.locallyCompactSpace S.topologicalManifold
  let Λ₀ : C_c(M, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => integral g f
      map_add' := integral_add g
      map_smul' := integral_smul g }
  let Λ : C_c(M, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Λ₀
    (fun f hf => integral_nonneg g f hf)
  refine ⟨RealRMK.rieszMeasure Λ, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · intro C hC
    exact hC.measure_lt_top
  · intro f
    exact RealRMK.integral_rieszMeasure Λ f
  · intro ν hν
    letI : ν.Regular := hν.1
    apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    exact (hν.2.2 f).trans (RealRMK.integral_rieszMeasure Λ f).symm

theorem chart_weight_formula :
    P202Specs.Geometry.RiemannianVolume.chart_weight_formulaType.{u} := by
  intro n a M _ S g f K c hc
  funext x
  unfold coordinateDensity chartIntegrand LocalIntegrationData.extendModel
  split
  · dsimp only
    split
    · rw [map_smul]
      change f _ * densityCoefficient K c hc _ (density g _) = _
      rw [(density_coordinates g K c hc _).1]
    · rfl
  · rfl

theorem integral_chart_sqrt :
    P202Specs.Geometry.RiemannianVolume.integral_chart_sqrtType.{u} := by
  intro n a M _ S g f K c hc hf
  rw [integral_chart g f K c hc hf]
  unfold DensityIntegrationData.coordinateIntegral
  rw [chart_weight_formula g (fun p => f p) K c hc]

theorem localIntegral_overlap :
    P202Specs.Geometry.RiemannianVolume.localIntegral_overlapType.{u} := by
  intro n a M _ S g f K J c d hc hd hfc hfd
  let ρ : DensityField S := fun p => f p • density g p
  have hρc : sectionSupport ρ ⊆ c.source := fun p hp =>
    hfc (DensityIntegralResults.support_weight_subset f (density g) hp).1
  have hρd : sectionSupport ρ ⊆ d.source := fun p hp =>
    hfd (DensityIntegralResults.support_weight_subset f (density g) hp).1
  have h := (DensityChartResults.coordinateIntegral_eq S K c d hc hd ρ hρc hρd).trans
    (DensityChartResults.coordinateIntegral_coordinates_eq K J d hd ρ)
  change (∫ x, coordinateDensity K c hc (fun p => f p • density g p) x) =
    ∫ x, coordinateDensity J d hd (fun p => f p • density g p) x at h
  rw [chart_weight_formula g f K c hc, chart_weight_formula g f J d hd] at h
  exact h

theorem density_overlap_jacobian :
    P202Specs.Geometry.RiemannianVolume.density_overlap_jacobianType.{u} := by
  intro n a M _ S g K c d hc hd p U F hU hp hF he
  have hdet := OrientationResults.transition_jacobian S K d c hd hc
    ⟨p.val, p.property.2, p.property.1⟩ U F hU hp hF he
  exact (density_overlap g K c d hc hd p).trans
    (congrArg (fun t : ℝ => |t| *
      densityCoefficient K c hc ⟨p.val, p.property.1⟩ (density g p.val)) hdet)

open MeasureTheory in
private theorem integral_comap_of_support {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {e : X → Y} (he : MeasurableEmbedding e)
    (ν : Measure Y) (f : Y → ℝ) (hf : Function.support f ⊆ Set.range e) :
    (∫ p, f (e p) ∂ν.comap e) = ∫ x, f x ∂ν := by
  rw [← he.integral_map, he.map_comap]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => Function.support_subset_iff'.mp hf x hx)

open MeasureTheory in
private theorem lintegral_comap_of_support {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {e : X → Y} (he : MeasurableEmbedding e)
    (ν : Measure Y) (f : Y → ℝ≥0∞) (hf : Function.support f ⊆ Set.range e) :
    (∫⁻ p, f (e p) ∂ν.comap e) = ∫⁻ x, f x ∂ν := by
  rw [← he.lintegral_map, he.map_comap]
  exact setLIntegral_eq_of_support_subset hf

/-- The chart embedding retains the model boundary as a closed subset of the
ambient Euclidean space. -/
private def chartEmbedding {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (c : ModelChart n a M) (p : c.source) : Euclidean n :=
  (c p.val).val

private theorem chartEmbedding_continuous {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (c : ModelChart n a M) : Continuous (chartEmbedding c) :=
  continuous_subtype_val.comp (c.continuousOn.domRestrict)

private theorem chartEmbedding_measurableEmbedding {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] (c : ModelChart n a M) :
    MeasurableEmbedding (chartEmbedding c) := by
  exact (MeasurableEmbedding.subtype_coe (isClosed_modelSet n a).measurableSet).comp
    ((MeasurableEmbedding.subtype_coe c.open_target.measurableSet).comp
      c.toHomeomorphSourceTarget.measurableEmbedding)

private def chartWeight {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) : ℝ := densityCoefficient K c hc p (density g p.val)

private theorem chartWeight_continuous {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    Continuous (chartWeight g K c hc) := (density_properties g).2.2.1 K c hc

private theorem chartWeight_nonneg {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) : 0 ≤ chartWeight g K c hc p := by
  rw [chartWeight, (density_coordinates g K c hc p).1]
  exact Real.sqrt_nonneg _

private theorem chartIntegrand_embedding {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f : M → ℝ) (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    chartIntegrand g f K c hc (chartEmbedding c p) = f p.val * chartWeight g K c hc p := by
  unfold chartIntegrand LocalIntegrationData.extendModel chartEmbedding
  simp only [Subtype.coe_prop, dite_true, c.map_source p.property, c.left_inv p.property]
  rw [chartWeight, (density_coordinates g K c hc p).1]

private theorem chartIntegrand_support {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f : M → ℝ) (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    Function.support (chartIntegrand g f K c hc) ⊆ Set.range (chartEmbedding c) := by
  intro x hx
  change chartIntegrand g f K c hc x ≠ 0 at hx
  unfold chartIntegrand LocalIntegrationData.extendModel at hx
  split at hx
  · rename_i hm
    dsimp only at hx
    split at hx
    · rename_i ht
      exact ⟨⟨c.symm ⟨x, hm⟩, c.map_target ht⟩,
        congrArg Subtype.val (c.right_inv ht)⟩
    · exact False.elim (hx rfl)
  · exact False.elim (hx rfl)

open MeasureTheory in
private theorem chartMeasure_integral {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f : M → ℝ) (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    (∫ p : c.source, f p.val ∂(volume.comap (chartEmbedding c)).withDensity
      (fun p => ENNReal.ofReal (chartWeight g K c hc p))) =
      ∫ x, chartIntegrand g f K c hc x := by
  rw [integral_withDensity_eq_integral_toReal_smul
    ((chartWeight_continuous g K c hc).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (chartWeight_nonneg g K c hc _), smul_eq_mul]
  have he := integral_comap_of_support (chartEmbedding_measurableEmbedding c) volume
    (chartIntegrand g f K c hc) (chartIntegrand_support g f K c hc)
  rw [← he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by dsimp only; rw [chartIntegrand_embedding]; exact mul_comm _ _)

open MeasureTheory in
private theorem measure_chart_local {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (μ : Measure M) [μ.Regular]
    (hμ : ∀ f : C_c(M, ℝ), (∫ p, f p ∂μ) = integral g f)
    (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    μ.comap (Subtype.val : c.source → M) =
      (volume.comap (chartEmbedding c)).withDensity
        (fun p => ENNReal.ofReal (chartWeight g K c hc p)) := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
  letI : LocallyCompactSpace M := SmoothManifolds.TopologicalManifold.locallyCompactSpace S.topologicalManifold
  letI : LocallyCompactSpace c.source := c.open_source.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI : TopologicalSpace.PseudoMetrizableSpace c.source :=
    c.toHomeomorphSourceTarget.isInducing.pseudoMetrizableSpace
  letI : (μ.comap (Subtype.val : c.source → M)).Regular :=
    Measure.Regular.comap' μ c.open_source.isOpenEmbedding_subtypeVal
  letI : IsFiniteMeasureOnCompacts (volume.comap (chartEmbedding c)) :=
    IsFiniteMeasureOnCompacts.comap' volume (chartEmbedding_continuous c)
      (chartEmbedding_measurableEmbedding c)
  letI : IsLocallyFiniteMeasure ((volume.comap (chartEmbedding c)).withDensity
      (fun p => ENNReal.ofReal (chartWeight g K c hc p))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (chartWeight_continuous g K c hc)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro q
  let q₀ : C_c(M, ℝ) :=
    ⟨⟨Function.extend Subtype.val (fun p => q p) 0,
      HasCompactSupport.continuous_extend_zero c.open_source q.continuous q.hasCompactSupport⟩,
      q.hasCompactSupport.extend_zero continuous_subtype_val⟩
  have hqs : tsupport q₀ ⊆ c.source := by
    exact (q.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)
  have hqe (p : c.source) : q₀ p.val = q p :=
    congrFun (Function.extend_comp Subtype.val_injective (fun p => q p) 0) p
  calc
    (∫ p, q p ∂μ.comap (Subtype.val : c.source → M)) = ∫ p, q₀ p ∂μ := by
      simpa only [hqe] using integral_comap_of_support
        (MeasurableEmbedding.subtype_coe c.open_source.measurableSet) μ (fun p => q₀ p)
        (by simpa only [Subtype.range_coe] using (subset_tsupport q₀).trans hqs)
    _ = integral g q₀ := hμ q₀
    _ = ∫ x, chartIntegrand g (fun p => q₀ p) K c hc x := integral_chart_sqrt g q₀ K c hc hqs
    _ = _ := by
      rw [← chartMeasure_integral g (fun p => q₀ p) K c hc]
      simp_rw [hqe]

private theorem chartLIntegrand_embedding {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f : M → ℝ≥0∞) (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    chartLIntegrand g f K c hc (chartEmbedding c p) =
      f p.val * ENNReal.ofReal (chartWeight g K c hc p) := by
  unfold chartLIntegrand chartEmbedding
  simp only [Subtype.coe_prop, dite_true, c.map_source p.property, c.left_inv p.property]
  rw [chartWeight, (density_coordinates g K c hc p).1]

private theorem chartLIntegrand_support {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f : M → ℝ≥0∞) (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    Function.support (chartLIntegrand g f K c hc) ⊆ Set.range (chartEmbedding c) := by
  intro x hx
  change chartLIntegrand g f K c hc x ≠ 0 at hx
  unfold chartLIntegrand at hx
  split at hx
  · rename_i hm
    split at hx
    · rename_i ht
      exact ⟨⟨c.symm ⟨x, hm⟩, c.map_target ht⟩,
        congrArg Subtype.val (c.right_inv ht)⟩
    · exact False.elim (hx rfl)
  · exact False.elim (hx rfl)

open MeasureTheory in
private theorem chartMeasure_lintegral {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (f : M → ℝ≥0∞) (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    (∫⁻ p : c.source, f p.val ∂(volume.comap (chartEmbedding c)).withDensity
      (fun p => ENNReal.ofReal (chartWeight g K c hc p))) =
      ∫⁻ x, chartLIntegrand g f K c hc x := by
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    ((chartWeight_continuous g K c hc).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he := lintegral_comap_of_support (chartEmbedding_measurableEmbedding c) volume
    (chartLIntegrand g f K c hc) (chartLIntegrand_support g f K c hc)
  rw [← he]
  apply lintegral_congr
  intro p
  rw [chartLIntegrand_embedding]
  exact mul_comm _ _

/-- The regular Borel measure obtained from the intrinsic density integral has
both local Lebesgue formulas, including for functions without compact support. -/
theorem measure_chart_exists :
    P202Specs.Geometry.RiemannianVolume.measure_chart_existsType.{u} := by
  intro n a M _ S g
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  obtain ⟨μ, hμ, _⟩ := measure_representation_exists g
  letI : μ.Regular := hμ.1
  refine ⟨μ, hμ.1, hμ.2.1, hμ.2.2, ?_⟩
  intro K c hc
  constructor
  · intro f _ hf
    have he := lintegral_comap_of_support
      (MeasurableEmbedding.subtype_coe c.open_source.measurableSet) μ f
      (by simpa only [Subtype.range_coe] using hf)
    rw [← he, measure_chart_local g μ hμ.2.2 K c hc]
    exact chartMeasure_lintegral g f K c hc
  · intro f _ hf
    have he := integral_comap_of_support
      (MeasurableEmbedding.subtype_coe c.open_source.measurableSet) μ f
      (by simpa only [Subtype.range_coe] using hf)
    rw [← he, measure_chart_local g μ hμ.2.2 K c hc]
    exact chartMeasure_integral g f K c hc

theorem localLIntegral_overlap :
    P202Specs.Geometry.RiemannianVolume.localLIntegral_overlapType.{u} := by
  intro n a M _ S g
  letI : MeasurableSpace M := borel M
  intro f hf K J c d hc hd hfc hfd
  obtain ⟨μ, _, _, _, hμ⟩ := measure_chart_exists g
  exact ((hμ K c hc).1 f hf hfc).symm.trans ((hμ J d hd).1 f hf hfd)

end P202.Geometry.RiemannianVolume
