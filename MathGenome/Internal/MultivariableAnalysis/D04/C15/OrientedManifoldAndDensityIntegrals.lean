import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.OrientedManifoldAndDensityIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C14.FiniteCompactPartition
import MathGenome.Internal.MultivariableAnalysis.D04.C14.MetricTopFormsAndDensities
import MathGenome.Internal.MultivariableAnalysis.D04.C15.DirectedSubstitution

noncomputable section
open Set Function Topology
open scoped ContDiff BigOperators
namespace D04.ManifoldIntegral
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

/-- The range chart, viewed inside the manifold rather than inside ambient space. -/
def chartHomeomorph {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) : c.source ≃ₜ ↥(Subtype.val ⁻¹' c.ambient : Set M) where
  toFun u := ⟨chartPoint c u, (c.map_source u.property).2⟩
  invFun x := ⟨c.invFun x.val, c.map_target ⟨x.val.property, x.property⟩⟩
  left_inv u := Subtype.ext (c.left_inv u u.property)
  right_inv x := Subtype.ext (Subtype.ext (c.right_inv x.val ⟨x.val.property, x.property⟩))
  continuous_toFun := (c.continuous_toFun.mapsToRestrict
    (fun _ hu => (c.map_source hu).1)).subtype_mk _
  continuous_invFun := (c.continuous_invFun.comp_continuous
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun x => ⟨x.val.property, x.property⟩)).subtype_mk _

lemma chartPoint_continuous {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) : Continuous (chartPoint c) :=
  continuous_subtype_val.comp (chartHomeomorph c).continuous

lemma chart_weight_compact {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (w : E n → ℝ)
    (hw : IsCompact (tsupport (fun x : M => w x)))
    (hs : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    HasCompactSupport (fun u : c.source => w (c.toFun u)) := by
  let e := chartHomeomorph c
  have ht : IsCompact (Subtype.val ⁻¹' tsupport (fun x : M => w x) :
      Set ↥(Subtype.val ⁻¹' c.ambient : Set M)) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using hs)).mpr hw
  have hp := (e.isCompact_preimage).mpr ht
  apply hp.of_isClosed_subset (isClosed_tsupport _) _
  apply closure_minimal _ ((hw.isClosed.preimage continuous_subtype_val).preimage e.continuous)
  intro u hu
  exact subset_tsupport (fun x : M => w x) (show w (chartPoint c u) ≠ 0 from hu)

lemma localized_coefficient_integrable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (w : E n → ℝ) (f : c.source → ℝ)
    (hwc : Continuous w) (hf : Continuous f)
    (hw : IsCompact (tsupport (fun x : M => w x)))
    (hs : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    Continuous (fun u : c.source => w (c.toFun u) * f u) ∧
    HasCompactSupport (fun u : c.source => w (c.toFun u) * f u) ∧
    DirectedSubstitution.ProperIntegrable (fun u : c.source => w (c.toFun u) * f u) := by
  have hc : Continuous (fun u : c.source => w (c.toFun u)) :=
    hwc.comp (c.continuous_toFun.comp_continuous continuous_subtype_val (fun u => u.property))
  have hk := (chart_weight_compact c w hw hs).mul_right (f' := f)
  exact ⟨hc.mul hf, hk, DirectedSubstitution.parameter_integrable c.half c.source_open (hc.mul hf) hk⟩

theorem top_coefficients_integrable :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.top_coefficients_integrableType := by
  intro r k n M η hη K P i
  exact localized_coefficient_integrable (P.chart i) (P.weight i) _
    (P.partition.1 i).continuous (hη _) (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2

theorem localizedTopCoefficient_pullback :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.localizedTopCoefficient_pullbackType := by
  intro r k n M η c w u
  rfl

theorem density_coefficients_integrable :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.density_coefficients_integrableType := by
  intro r k n M hM ρ hρ K P i
  apply localized_coefficient_integrable (P.chart i) (P.weight i) _
    (P.partition.1 i).continuous _ (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2
  exact (hρ.comp (chartPoint_continuous _)).mul
    ((D04MetricDensity.chartDensity_continuous (P.chart i) hM.1).comp_continuous
      continuous_subtype_val (fun u => u.property))

theorem zero_support_finite :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.zero_support_finiteType := by
  intro r n M hM f hf
  let : DiscreteTopology M := isDiscrete_iff_discreteTopology.mp
    ((D04.zero_manifold_iff_discrete r M).mp hM).2
  exact (isCompact_iff_finite.mp hf).subset (subset_tsupport f)

theorem zero_integral_support_sum :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.zero_integral_support_sumType := by
  intro r n M hM o f hf
  have hs := zero_support_finite hM f hf
  refine ⟨hs, ?_⟩
  apply finsum_eq_finsetSum_of_support_subset
  intro x hx
  exact hs.mem_toFinset.mpr (support_mul_subset_right _ _ hx)

theorem compact_zero_agrees :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.compact_zero_agreesType := by
  intro r n M hM hcompact o f
  have h := hcompact.finite ((D04.zero_manifold_iff_discrete r M).mp hM).2
  refine ⟨h, ?_⟩
  let := h.fintype
  exact finsum_eq_sum_of_fintype _

theorem density_frame_change :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.density_frame_changeType := by
  intro r k n M ρ x F A
  dsimp only [densityValue]
  rw [D04MetricDensity.density_linear_change]
  ring

theorem density_coefficient_change :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.density_coefficient_changeType := by
  intro r k n M hM ρ c d u hu hv
  have he : chartPoint d ⟨chartTransition c d u, hv⟩ = chartPoint c ⟨u, hu.1⟩ :=
    Subtype.ext (d.right_inv _ ⟨(c.map_source hu.1).1, hu.2⟩)
  dsimp only [densityCoefficient]
  rw [he, D04MetricDensity.chartDensity_transition c d hM.1 hM.2.1 u hu]
  ring

theorem chart_partition_exists :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.chart_partition_existsType := by
  classical
  intro r k n M hM K hK
  obtain ⟨m, a, f, hf, hc⟩ := FiniteCompactPartition.finite_partition hM K hK
    (fun _ : Unit => (univ : Set M)) (fun _ => isOpen_univ) (by intro x hx; exact mem_iUnion.mpr ⟨(), mem_univ x⟩)
  choose c hc using hc
  refine ⟨⟨m, c, f, hf.1, hf.2.1, ?_, hf.2.2.2⟩⟩
  intro i
  exact ⟨(hf.2.2.1 i).1, hc i⟩

/-- Local constancy can be restricted on the relative source, including its
flat boundary. No reflection or positive-boundary-atlas assumption is used. -/
lemma constant_signed_chart_at {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (x : M) :
    ∃ (c : EmbeddedChart r k n M) (s : PointSign),
      (x : E n) ∈ c.ambient ∧
      ∀ v : c.source, chartSign o.atPoint c v v.property = s.val := by
  obtain ⟨c, u, hu, he⟩ := o.manifold.2.2 x x.property
  obtain ⟨U, hU, huU, hconst⟩ := (o.locally_constant c).exists_open ⟨u, hu.1⟩
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨d, hs, _, hf, _, _⟩ := embeddedChart_restrict_parameter c W hW
  have huW : u ∈ W := show (⟨u, hu.1⟩ : c.source) ∈ Subtype.val ⁻¹' W from hWU ▸ huU
  have hud : u ∈ d.source := hs ▸ ⟨hu.1, huW⟩
  refine ⟨d, ⟨chartSign o.atPoint c u hu.1,
    D04.Orientations.chartSign_values o.atPoint c o.manifold.1 o.manifold.2.1 u hu.1⟩, ?_, ?_⟩
  · have hd := (d.map_source hud).2
    rw [hf, he] at hd
    exact hd
  · intro v
    have hv : (v : E k) ∈ c.source ∩ W := hs ▸ v.property
    rw [D04.Orientations.restriction_sign o.atPoint c d o.manifold.1
      (by intro z hz; exact (hs ▸ hz).1) hf v v.property]
    exact hconst ⟨v, hv.1⟩ (hWU ▸ hv.2)

theorem signed_partition_exists :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.signed_partition_existsType := by
  classical
  intro r k n M o K hK
  choose c s hc hs using fun p : K => constant_signed_chart_at o p.val
  obtain ⟨m, a, p, f, hf, hsupport⟩ := FiniteCompactPartition.finite_partition_refined
    o.manifold K hK (fun _ : Unit => (univ : Set M)) (fun _ => isOpen_univ)
    (by intro x hx; exact mem_iUnion.mpr ⟨(), mem_univ x⟩) c hc (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _)
  let P : ChartPartition r k M K := ⟨m, (fun i => c (p i)), f,
    hf.1, hf.2.1, (fun i => ⟨(hf.2.2.1 i).1,
      fun x hx => (hsupport i hx).2⟩), hf.2.2.2⟩
  exact ⟨{ toChartPartition := P, sign := fun i => s (p i), agrees := fun i => hs (p i) }⟩

theorem densityCoefficient_frame :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.densityCoefficient_frameType := by
  intro r k n M ρ c u
  dsimp only [densityCoefficient, densityValue, chartPoint]
  rw [D04MetricDensity.density_chart]

theorem oriented_construction :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.oriented_constructionType := by
  intro r k n M o η hc hk
  obtain ⟨P⟩ := signed_partition_exists o (topSupport η) hk
  exact ⟨P, fun i => (top_coefficients_integrable η hc P.toChartPartition i).2.2, rfl⟩

theorem density_construction :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.density_constructionType := by
  intro r k n M hM ρ hc hk
  obtain ⟨P⟩ := chart_partition_exists hM (tsupport ρ) hk
  exact ⟨P, fun i => (density_coefficients_integrable hM ρ hc P i).2.2, rfl⟩

abbrev chartPoint := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.chartPoint
abbrev topCoefficient := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.topCoefficient
abbrev ContinuousTopField := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ContinuousTopField
abbrev topSupport := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.topSupport
abbrev localizedTopCoefficient := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.localizedTopCoefficient
abbrev orientedIntegral := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.orientedIntegral
abbrev densityValue := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityValue
abbrev densityCoefficient := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityCoefficient
abbrev localizedDensityCoefficient := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.localizedDensityCoefficient
abbrev densityIntegral := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral
abbrev zeroIntegral := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.zeroIntegral
abbrev compactZeroIntegral := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.compactZeroIntegral
abbrev ChartPartition := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition
abbrev SignedChartPartition := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.SignedChartPartition
abbrev DensityField := @Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.DensityField

end D04.ManifoldIntegral
