import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C15.IntrinsicExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C15.ManifoldIntegralIndependence
import MathGenome.Internal.MultivariableAnalysis.D04.C15.LocalStokesWithArtificialFaces

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped ContDiff BigOperators Classical
namespace D04Stokes
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.IntrinsicExteriorDerivative.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.GeneralizedStokes
open Model

/-- The support of an arbitrary-degree intrinsic field uses the same relative
closure convention as the upstream top-field support. -/
theorem formSupport_top {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) : formSupport η = topSupport η := rfl

/-- Under the manifold hypotheses the boundary restriction is the actual
inclusion of boundary tangent vectors into bulk tangent vectors. -/
theorem boundaryTangentInclusion_apply {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (x : intrinsicBoundary r (d+1) M)
    (v : tangentSpace r d (intrinsicBoundary r (d+1) M) x) :
    (boundaryTangentInclusion r d M x v).val = v.val := by
  rw [boundaryTangentInclusion, dite_eq_left (D04BoundaryOrientation.boundary_tangent_le hM x)]
  rfl

/-- Restricting an ambient form first to M and then to its boundary gives
exactly its direct tangential restriction to the boundary. -/
theorem boundaryRestriction_ambient {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (omega : FormField n d) :
    boundaryRestriction (tangentRestriction r (d+1) M omega) =
      tangentRestriction r d (intrinsicBoundary r (d+1) M) omega := by
  funext x
  ext v
  change omega x (fun j => (boundaryTangentInclusion r d M x (v j)).val) =
    omega x (fun j => (v j).val)
  simp_rw [boundaryTangentInclusion_apply hM]

/-- Continuity of all chart coefficients implies continuity of evaluation on
any fixed tuple; no topology on a heterogeneous covector family is assumed. -/
theorem intrinsic_evaluation_continuous {k n p : ℕ} {M : Set (E n)}
    (η : IntrinsicForm (k := k) M p) (hη : IntrinsicContinuous η)
    (c : EmbeddedChart 2 k n M) (v : Fin p → E k) :
    ContinuousOn (fun u => chartPullback c η u v) c.source := by
  have he : (fun u => chartPullback c η u v) = fun u =>
      ∑ I : MultiIndex k p,
        coefficient (standardBasis k) (chartPullback c η u) I * dx (standardBasis k) I v := by
    funext u
    conv_lhs => rw [D04.covector_expansion (standardBasis k) (chartPullback c η u)]
    simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [he]
  exact continuousOn_finsetSum _ (fun I _ => (hη c I).mul continuousOn_const)

theorem intrinsic_top_continuous : intrinsic_top_continuousType := by
  intro k n M η hη c
  have hc := (intrinsic_evaluation_continuous η hη c (standardBasis k)).domRestrict
  have he : (fun u : c.source => chartPullback c η u (standardBasis k)) =
      topCoefficient η c := by
    funext u
    simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
      dite_eq_left u.property]
    rfl
  change Continuous (fun u : c.source => chartPullback c η u (standardBasis k)) at hc
  rwa [he] at hc

/-- Exterior differentiation within any relative set sends the zero field
to zero, including on a flat boundary. -/
theorem withinExteriorDerivative_zero {k p : ℕ} (S : Set (E k)) (u : E k) :
    withinExteriorDerivative S (fun _ => (0 : Covector (E k) p)) u = 0 := by
  simp [withinExteriorDerivative,
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative,
    coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient]

/-- A field zero on a relative neighborhood has zero derivative there.
This is a germ statement and uses no ambient extension outside the manifold. -/
theorem intrinsic_derivative_zero_off_support {k n p : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 k M) (omega : IntrinsicForm (k := k) M p)
    (η : IntrinsicForm (k := k) M (p+1)) (hd : HasIntrinsicExteriorDerivative omega η)
    (x : M) (hx : x ∉ formSupport omega) : η x = 0 := by
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x x.property
  have hcx : (⟨c.toFun u, (c.map_source hu.1).1⟩ : M) = x := Subtype.ext hux
  have hn : {y : M | y ∉ formSupport omega} ∈ 𝓝 x :=
    (isClosed_closure.isOpen_compl).mem_nhds hx
  have he : chartPullback c omega =ᶠ[𝓝[c.source] u]
      (fun _ => (0 : Covector (E k) p)) := by
    rw [nhdsWithin_eq_map_subtype_coe hu.1]
    change ∀ᶠ v : c.source in 𝓝 ⟨u, hu.1⟩,
      chartPullback c omega v = (0 : Covector (E k) p)
    have hn' : {y : M | y ∉ formSupport omega} ∈ 𝓝 (chartPoint c ⟨u, hu.1⟩) := by
      simpa only [chartPoint, hcx] using hn
    have hnear := (D04.ManifoldIntegral.chartPoint_continuous c).continuousAt.eventually hn'
    filter_upwards [hnear] with v hv
    have hv0 : omega (chartPoint c v) = 0 := by
      by_contra hnz
      exact hv (subset_closure hnz)
    change Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c omega v = 0
    simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
      dite_eq_left v.property]
    change (omega (chartPoint c v)).compLinearMap _ = 0
    rw [hv0, AlternatingMap.zero_compLinearMap]
  have hz : chartPullback c η u = 0 := by
    exact (hd c u hu.1).trans
      ((D04.Intrinsic.withinExteriorDerivative_congr hu.1 _ _ he).trans
        (withinExteriorDerivative_zero c.source u))
  change Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c η u = 0 at hz
  simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
    dite_eq_left hu.1] at hz
  have hzero : (η ⟨c.toFun u, (c.map_source hu.1).1⟩).compLinearMap (chartTangentMap c u hu.1) =
      (0 : Covector (Tangent (k := k) M ⟨c.toFun u, (c.map_source hu.1).1⟩) (p+1)).compLinearMap
        (chartTangentMap c u hu.1) := by simpa using hz
  have ht := AlternatingMap.compLinearMap_injective _
    (D04.Intrinsic.chartTangentMap_surjective hM c hu.1) hzero
  rwa [hcx] at ht

theorem intrinsic_derivative_support : intrinsic_derivative_supportType := by
  intro k n p M hM omega homega
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hnot
  exact hx (intrinsic_derivative_zero_off_support hM omega _
    (D04.Intrinsic.intrinsicExteriorDerivative_spec hM omega homega).2 x hnot)

/-- Compactness of the whole manifold is sufficient for every relative
closed support; compactness of M is not needed by the other lemmas. -/
theorem formSupport_compact_of_compact {r : ℕ∞ω} {k n p : ℕ} {M : Set (E n)}
    (hc : IsCompact M) (omega : TangentForm r k M p) : IsCompact (formSupport omega) := by
  let : CompactSpace M := isCompact_iff_compactSpace.mp hc
  exact isClosed_closure.isCompact

/-- Tangential restriction can only decrease support. -/
theorem tangentRestriction_support {r : ℕ∞ω} {k n p : ℕ} {M : Set (E n)}
    (omega : FormField n p) :
    formSupport (tangentRestriction r k M omega) ⊆ Subtype.val ⁻¹' tsupport omega := by
  apply closure_minimal _ ((isClosed_tsupport omega).preimage continuous_subtype_val)
  intro x hx
  apply subset_tsupport omega
  intro hz
  exact hx (by simp [tangentRestriction, hz])

/-- The ambient version assumes compactness only of the relevant ambient
support along M, even when M is noncompact and nonclosed. -/
theorem tangentRestriction_support_compact {r : ℕ∞ω} {k n p : ℕ} {M : Set (E n)}
    (omega : FormField n p) (hc : IsCompact (M ∩ tsupport omega)) :
    IsCompact (formSupport (tangentRestriction r k M omega)) := by
  have hpre : IsCompact (Subtype.val ⁻¹' (M ∩ tsupport omega) : Set M) :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc (by
      simpa only [Subtype.range_coe] using (inter_subset_left : M ∩ tsupport omega ⊆ M))
  apply hpre.of_isClosed_subset isClosed_closure
  intro x hx
  exact ⟨x.property, tangentRestriction_support omega hx⟩

/-- All compactly supported continuous top fields possess the actual proper
Riemann integral, with the same value under every chart/weight choice. -/
theorem positive_integral_exists {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (eta : TangentTopField r k M)
    (heta : ContinuousTopField eta) (hc : IsCompact (topSupport eta)) :
    ∃ I, HasPositiveIntegral o eta I := by
  obtain ⟨P⟩ := D04.ManifoldIntegral.signed_partition_exists o (topSupport eta) hc
  refine ⟨orientedIntegral eta P, heta, hc, ⟨P⟩, ?_⟩
  intro Q
  exact ⟨fun i => (D04.ManifoldIntegral.top_coefficients_integrable eta heta Q.toChartPartition i).2.2,
    D04.ManifoldIntegralIndependence.oriented_independent o eta heta Q P⟩

theorem intrinsic_bulk_integral_exists : intrinsic_bulk_integral_existsType := by
  intro d n M o omega homega hcompact
  have hd := D04.Intrinsic.intrinsicExteriorDerivative_spec o.manifold omega homega
  apply positive_integral_exists o _ (intrinsic_top_continuous _ hd.1)
  exact hcompact.of_isClosed_subset isClosed_closure
    (intrinsic_derivative_support o.manifold omega homega)

/-- Construction of the genuine outward-first boundary orientation in every
positive bulk dimension, including the signed zero-dimensional boundary. -/
theorem outwardFirst_exists {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M) :
    ∃ bO : ManifoldOrientation r d (intrinsicBoundary r (d+1) M), OutwardFirst d o bO := by
  obtain ⟨nu, hnu, _⟩ := D04BoundaryOrientation.continuous_conormal o.manifold
  cases d with
  | zero =>
    obtain ⟨s, hs, _⟩ := D04BoundaryOrientation.boundary_point_sign o nu hnu.2
    exact ⟨s, nu, hnu.1, hnu.2, hs⟩
  | succ d =>
    obtain ⟨bO, hbO, _⟩ := D04BoundaryOrientation.boundary_orientation o nu hnu.2
    exact ⟨bO, nu, hnu.1, hnu.2, hbO⟩

/-- Multiplication by a smooth ambient weight preserves intrinsic C¹
regularity, using a genuine local chart extension at boundary points. -/
theorem intrinsicC1_weight {k n p : ℕ} {M : Set (E n)}
    (omega : IntrinsicForm (k := k) M p) (homega : IntrinsicC1 omega)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w) :
    IntrinsicC1 (fun x : M => w x • omega x) := by
  intro c u hu
  obtain ⟨W, alpha, hW, huW, ha, he⟩ := homega c u hu
  obtain ⟨V, g, hV, huV, heg, hg, _⟩ := c.regular u hu
  let A := W ∩ V
  have hA : IsOpen A := hW.inter hV
  have halpha : IsCrForm (some 1) A alpha := D04.Intrinsic.isCrForm_mono 1 ha hA inter_subset_left
  have hcomp : ContDiffOn ℝ 1 (w ∘ g) A :=
    hw.comp_contDiffOn ((hg.of_le (by norm_num)).mono inter_subset_right)
  refine ⟨A, fun v => w (g v) • alpha v, hA, ⟨huW, huV⟩,
    D04.isCrForm_function_smul 1 A (w ∘ g) alpha hA
      ((D04.crOn_iff_contDiffOn 1 A _ hA).mpr hcomp) halpha, ?_⟩
  intro v hv
  change w (g v) • alpha v = _
  rw [heg ⟨hv.1, hv.2.2⟩, he ⟨hv.1, hv.2.1⟩]
  simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
    dite_eq_left hv.1]
  rfl

/-- Chart coefficients of an intrinsic C¹ field are differentiable within
its source, including the genuine flat boundary. -/
theorem intrinsic_coefficient_differentiableWithin {k n p : ℕ} {M : Set (E n)}
    (omega : IntrinsicForm (k := k) M p) (homega : IntrinsicC1 omega)
    (c : EmbeddedChart 2 k n M) (u : E k) (hu : u ∈ c.source) (I : MultiIndex k p) :
    DifferentiableWithinAt ℝ
      (fun v => coefficient (standardBasis k) (chartPullback c omega v) I) c.source u := by
  obtain ⟨W, alpha, hW, huW, ha, he⟩ := homega c u hu
  apply (D04.isCrForm_coefficient_differentiableAt W alpha ha u huW I).differentiableWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW)] with v hv hvW
    exact congrArg (fun a => coefficient (standardBasis k) a I) (he ⟨hv, hvW⟩).symm
  · exact hu

/-- Pullback commutes with finite pointwise sums on the canonical tangent
spaces, without choosing ambient representatives. -/
theorem chartPullback_sum {k n p : ℕ} {M : Set (E n)} {ι : Type*} [Fintype ι]
    (omega : ι → IntrinsicForm (k := k) M p) (c : EmbeddedChart 2 k n M)
    (u : E k) : chartPullback c (fun x => ∑ i, omega i x) u =
      ∑ i, chartPullback c (omega i) u := by
  by_cases hu : u ∈ c.source
  · simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
      dite_eq_left hu]
    ext v
    simp only [AlternatingMap.compLinearMap_apply, sum_apply]
  · simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
      dite_eq_right hu, Finset.sum_const_zero]

/-- Linearity of the intrinsic differential is proved using derivatives
within chart sources, so it also holds at boundary points. -/
theorem intrinsic_hasDerivative_sum {k n p : ℕ} {M : Set (E n)} {ι : Type*} [Fintype ι]
    (omega : ι → IntrinsicForm (k := k) M p)
    (eta : ι → IntrinsicForm (k := k) M (p+1))
    (homega : ∀ i, IntrinsicC1 (omega i))
    (heta : ∀ i, HasIntrinsicExteriorDerivative (omega i) (eta i)) :
    HasIntrinsicExteriorDerivative (fun x => ∑ i, omega i x) (fun x => ∑ i, eta i x) := by
  intro c u hu
  rw [chartPullback_sum]
  simp_rw [heta _ c u hu]
  unfold Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative
  have hc (I : MultiIndex k p) :
      (fun v => coefficient (standardBasis k) (chartPullback c (fun x => ∑ i, omega i x) v) I) =
        fun v => ∑ i, coefficient (standardBasis k) (chartPullback c (omega i) v) I := by
    funext v
    rw [chartPullback_sum]
    simp only [Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient, sum_apply]
  simp_rw [hc]
  simp_rw [fderivWithin_fun_sum (D04.EmbeddedChart.source_uniqueDiff c u hu)
    (fun i _ => intrinsic_coefficient_differentiableWithin (omega i) (homega i) c u hu _)]
  simp only [sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_comm]

/-- The finite partition reconstructs the form everywhere, using only
sum-to-one near its relative support. -/
theorem partition_reconstruct {r : ℕ∞ω} {k n p m : ℕ} {M : Set (E n)}
    (omega : TangentForm r k M p) (U : Fin m → Set M)
    (w : Fin m → E n → ℝ)
    (hw : PartitionNear M (formSupport omega) U m id w) :
    (fun x : M => ∑ i, w i x • omega x) = omega := by
  funext x
  rw [← Finset.sum_smul]
  by_cases hx : omega x = 0
  · simp [hx]
  · obtain ⟨V, _, hV, hone⟩ := hw.2.2.2.1
    rw [hone x (hV (subset_closure hx)), one_smul]

/-- The cancellation used in global Stokes: the derivatives of localized
forms sum to the derivative of the original form. -/
theorem intrinsic_partition_derivative {k n p m : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 k M) (omega : IntrinsicForm (k := k) M p)
    (homega : IntrinsicC1 omega) (U : Fin m → Set M) (w : Fin m → E n → ℝ)
    (hw : PartitionNear M (formSupport omega) U m id w) :
    (fun x : M => ∑ i, intrinsicExteriorDerivative (fun y : M => w i y • omega y) x) =
      intrinsicExteriorDerivative omega := by
  have hlocal i : IntrinsicC1 (fun y : M => w i y • omega y) :=
    intrinsicC1_weight omega homega (w i) ((hw.1 i).of_le (by norm_num))
  have hd := intrinsic_hasDerivative_sum (fun i y => w i y • omega y)
    (fun i => intrinsicExteriorDerivative (fun y : M => w i y • omega y)) hlocal
    (fun i => (D04.Intrinsic.intrinsicExteriorDerivative_spec hM _ (hlocal i)).2)
  rw [partition_reconstruct omega U w hw] at hd
  exact D04.Intrinsic.intrinsic_exteriorDerivative_unique hM omega _ _ hd
    (D04.Intrinsic.intrinsicExteriorDerivative_spec hM omega homega).2

/-- The intrinsic boundary is closed in M, although M itself need not be
closed in ambient Euclidean space. -/
theorem intrinsicBoundary_closed_relative {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) :
    IsClosed (Subtype.val ⁻¹' intrinsicBoundary r k M : Set M) := by
  have hfb : IsClosed (flatBoundary k) := by
    cases k with
    | zero => exact isClosed_empty
    | succ d =>
      exact isClosed_eq (EuclideanSpace.proj (Fin.last d)).continuous continuous_const
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x x.property
  let V : Set c.source := {v | c.toFun v ∉ intrinsicBoundary r k M}
  have he : V = {v : c.source | ¬ IsBoundaryParameter c v} := by
    ext v
    exact not_congr (D04.chart_intrinsicBoundary c hM.1 hM.2.1 v v.property)
  have hV : IsOpen V := by
    rw [he]
    have hf : IsClosed {v : c.source | IsBoundaryParameter c v} := by
      by_cases hh : c.half = true
      · have hf' : IsClosed (Subtype.val ⁻¹' flatBoundary k : Set c.source) :=
          hfb.preimage (continuous_subtype_val : Continuous (Subtype.val : c.source → E k))
        convert hf' using 1
        ext v
        simp [IsBoundaryParameter, hh]
      · convert isClosed_empty (X := c.source) using 1
        ext v
        simp [IsBoundaryParameter, hh]
    exact hf.isOpen_compl
  have hcopen : IsOpenMap (chartPoint c) := by
    change IsOpenMap (Subtype.val ∘ D04.ManifoldIntegral.chartHomeomorph c)
    exact (c.ambient_open.preimage continuous_subtype_val).isOpenMap_subtype_val.comp
      (D04.ManifoldIntegral.chartHomeomorph c).isOpenMap
  have hxp : x ∈ chartPoint c '' V := by
    refine ⟨⟨u, hu.1⟩, ?_, Subtype.ext hux⟩
    change c.toFun u ∉ intrinsicBoundary r k M
    rwa [hux]
  apply mem_of_superset ((hcopen V hV).mem_nhds hxp)
  rintro _ ⟨v, hv, rfl⟩
  exact hv

/-- The boundary inclusion is a closed embedding into M. -/
theorem boundary_closedEmbedding {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) :
    IsClosedEmbedding (fun x : intrinsicBoundary r (d+1) M => (⟨x, x.property.1⟩ : M)) := by
  let f := fun x : intrinsicBoundary r (d+1) M => (⟨x, x.property.1⟩ : M)
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal
  refine ⟨hf, ?_⟩
  have he : range f = (Subtype.val ⁻¹' intrinsicBoundary r (d+1) M : Set M) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [he]
  exact intrinsicBoundary_closed_relative hM

/-- Restriction to the boundary can only decrease support. -/
theorem boundaryRestriction_support {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (omega : TangentForm r (d+1) M d) :
    formSupport (boundaryRestriction omega) ⊆
      (fun x : intrinsicBoundary r (d+1) M => (⟨x, x.property.1⟩ : M)) ⁻¹' formSupport omega := by
  have hf : Continuous (fun x : intrinsicBoundary r (d+1) M => (⟨x, x.property.1⟩ : M)) :=
    continuous_subtype_val.subtype_mk _
  apply closure_minimal _ (isClosed_closure.preimage hf)
  intro x hx
  apply subset_closure
  intro hz
  exact hx (by simp [boundaryRestriction, hz])

theorem boundaryRestriction_support_compact {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (omega : TangentForm r (d+1) M d)
    (hc : IsCompact (formSupport omega)) :
    IsCompact (topSupport (boundaryRestriction omega)) :=
  ((boundary_closedEmbedding hM).isCompact_preimage hc).of_isClosed_subset isClosed_closure
    (boundaryRestriction_support omega)

/-- A local equality of bulk fields descends to their boundary restrictions. -/
theorem boundaryRestriction_congr_at {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (alpha beta : TangentForm r (d+1) M d) (x : intrinsicBoundary r (d+1) M)
    (h : alpha ⟨x, x.property.1⟩ = beta ⟨x, x.property.1⟩) :
    boundaryRestriction alpha x = boundaryRestriction beta x :=
  congrArg (fun a => a.compLinearMap (boundaryTangentInclusion r d M x)) h

/-- The boundary restriction of a C¹ intrinsic form is C¹ in boundary
charts. The proof uses the already proved local ambient extension theorem. -/
theorem boundaryRestriction_C1 {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 (d+1) M) (omega : IntrinsicForm (k := d+1) M d)
    (homega : IntrinsicC1 omega) : IntrinsicC1 (boundaryRestriction omega) := by
  intro b u hu
  let x : intrinsicBoundary 2 (d+1) M := ⟨b.toFun u, (b.map_source hu).1⟩
  obtain ⟨O, alpha, hO, hxO, ha, he⟩ :=
    D04.Intrinsic.intrinsic_local_ambient hM omega homega (⟨x, x.property.1⟩ : M)
  obtain ⟨V, g, hV, huV, heg, hg, _⟩ := b.regular u hu
  let W := V ∩ g ⁻¹' O
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hV hO
  have huW : u ∈ W := ⟨huV, by
    change g u ∈ O
    rw [heg ⟨hu, huV⟩]
    exact hxO⟩
  have hgW : D04.CrOn 2 W g :=
    (D04.crOn_iff_contDiffOn 2 W g hW).mpr (hg.mono inter_subset_left)
  refine ⟨W, D04.pullback g alpha, hW, huW,
    D04.pullback_C1 W O g alpha hW (fun _ hv => hv.2) hgW ha, ?_⟩
  intro v hv
  have hvO : b.toFun v ∈ O := by
    rw [← heg ⟨hv.1, hv.2.1⟩]
    exact hv.2.2
  have heq : boundaryRestriction omega ⟨b.toFun v, (b.map_source hv.1).1⟩ =
      tangentRestriction 2 d (intrinsicBoundary 2 (d+1) M) alpha ⟨b.toFun v, (b.map_source hv.1).1⟩ := by
    rw [boundaryRestriction_congr_at omega (tangentRestriction 2 (d+1) M alpha) _
      (he ⟨b.toFun v, ((b.map_source hv.1).1).1⟩ hvO).symm,
      boundaryRestriction_ambient hM alpha]
  have hpb := D04.Intrinsic.chartPullback_ambient_extension b alpha hv.1 hV hv.2.1 heg
    ((hg.contDiffAt (hV.mem_nhds hv.2.1)).differentiableAt (by norm_num))
  refine hpb.symm.trans ?_
  change Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback b
    (tangentRestriction 2 d (intrinsicBoundary 2 (d+1) M) alpha) v = _
  simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
    dite_eq_left hv.1]
  rw [heq]

/-- Every continuous compactly supported top field has an integral,
including finite signed evaluation on noncompact zero-manifolds. -/
theorem manifold_integral_exists {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (o : ManifoldOrientation r k M)
    (eta : TangentTopField r k M) (heta : ContinuousTopField eta)
    (hc : IsCompact (topSupport eta)) : ∃ I, HasManifoldIntegral r k o eta I := by
  cases k with
  | zero =>
    let f : M → ℝ := fun x => eta x (fun j => Fin.elim0 j)
    have hs : tsupport f ⊆ topSupport eta := by
      apply closure_minimal _ isClosed_closure
      intro x hx
      apply subset_closure
      intro hz
      exact hx (by simp [f, hz])
    have hf : HasCompactSupport f := hc.of_isClosed_subset (isClosed_tsupport f) hs
    exact ⟨zeroIntegral o f, hM, hc,
      D04.ManifoldIntegral.zero_support_finite hM f hf, rfl⟩
  | succ k => exact positive_integral_exists o eta heta hc

/-- Both integrals in intrinsic Stokes exist before their values are
compared. The orientation is outward-first, including signed points. -/
theorem intrinsic_integrals_exist {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 (d+1) M)
    (omega : IntrinsicForm (k := d+1) M d) (homega : IntrinsicC1 omega)
    (hc : IsCompact (formSupport omega)) :
    ∃ bO : ManifoldOrientation 2 d (intrinsicBoundary 2 (d+1) M),
      OutwardFirst d o bO ∧ ∃ I J : ℝ,
        HasPositiveIntegral o (intrinsicExteriorDerivative omega) I ∧
        HasManifoldIntegral 2 d bO (boundaryRestriction omega) J := by
  obtain ⟨bO, hbO⟩ := outwardFirst_exists o
  obtain ⟨I, hI⟩ := intrinsic_bulk_integral_exists o omega homega hc
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  have hbc := intrinsic_top_continuous _
    (D04.Intrinsic.intrinsicC1_continuous _ (boundaryRestriction_C1 o.manifold omega homega))
  obtain ⟨J, hJ⟩ := manifold_integral_exists hbM bO _ hbc
    (boundaryRestriction_support_compact o.manifold omega hc)
  exact ⟨bO, hbO, I, J, hI, hJ⟩

/-- Ambient C⁰ top forms restrict continuously to C¹ manifolds. This proof
uses only first derivatives of local chart extensions. -/
theorem tangentRestriction_top_continuous {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (O : Set (E n)) (alpha : FormField n k)
    (hMO : M ⊆ O) (ha : IsCrForm (some 0) O alpha) :
    ContinuousTopField (tangentRestriction r k M alpha) := by
  intro c
  let f : E k → ℝ := fun u => alpha (c.toFun u)
    (fun j => chartDifferential c u (standardBasis k j))
  have hf : ContinuousOn f c.source := by
    apply continuousOn_of_locally_continuousOn
    intro u hu
    obtain ⟨V, g, hV, huV, heg, hg, _⟩ := c.regular u hu
    let W := V ∩ g ⁻¹' O
    have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hV ha.1
    have huW : u ∈ W := ⟨huV, by
      change g u ∈ O
      rw [heg ⟨hu, huV⟩]
      exact hMO (c.map_source hu).1⟩
    have hg1 : ContDiffOn ℝ 1 g W := (hg.of_le hM.1.1).mono inter_subset_left
    have hp := D04.pullback_continuous W O g alpha hW (fun _ hv => hv.2)
      ((D04.crOn_iff_contDiffOn 1 W g hW).mpr hg1) ha
    have heval := D04.LocalStokes.form_evaluation_continuous W _ hp (standardBasis k)
    refine ⟨W, hW, huW, (heval.mono inter_subset_right).congr ?_⟩
    intro v hv
    change f v = D04.pullback g alpha v (standardBasis k)
    change alpha (c.toFun v) (fun j => chartDifferential c v (standardBasis k j)) =
      alpha (g v) (fun j => fderiv ℝ g v (standardBasis k j))
    have hd : chartDifferential c v = fderiv ℝ g v :=
      D04.EmbeddedChart.differential_extension c hv.1 hV hv.2.1 heg
        ((hg1.contDiffAt (hW.mem_nhds hv.2)).differentiableAt (by norm_num))
    rw [heg ⟨hv.1, hv.2.1⟩, hd]
  exact hf.domRestrict

/-- The derivative of an ambient form has support in the original support.
This is true of the actual exterior-derivative selector by locality. -/
theorem ambient_derivative_tsupport {n p : ℕ} (alpha : FormField n p) :
    tsupport (exteriorDerivative alpha) ⊆ tsupport alpha :=
  closure_minimal (D04.LocalStokes.exteriorDerivative_support alpha) (isClosed_tsupport alpha)

/-- Both integrals in the full C¹ ambient theorem exist. The bulk integrand
is ambient d alpha evaluated only on tangent vectors. -/
theorem ambient_integrals_exist {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (O : Set (E n)) (alpha : FormField n d)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (hc : IsCompact (M ∩ tsupport alpha)) :
    ∃ bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M),
      OutwardFirst d o bO ∧ ∃ I J : ℝ,
        HasPositiveIntegral o (tangentRestriction 1 (d+1) M (exteriorDerivative alpha)) I ∧
        HasManifoldIntegral 1 d bO
          (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) alpha) J := by
  obtain ⟨bO, hbO⟩ := outwardFirst_exists o
  have hdc : IsCompact (M ∩ tsupport (exteriorDerivative alpha)) := by
    have he : M ∩ tsupport (exteriorDerivative alpha) =
        (M ∩ tsupport alpha) ∩ tsupport (exteriorDerivative alpha) := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨hx.1, ambient_derivative_tsupport alpha hx.2⟩, hx.2⟩
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
    rw [he]
    exact hc.inter_right (isClosed_tsupport _)
  obtain ⟨I, hI⟩ := positive_integral_exists o _
    (tangentRestriction_top_continuous o.manifold O _ hMO
      (D04.exteriorDerivative_continuous O alpha ha))
    (tangentRestriction_support_compact _ hdc)
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  have hbc := tangentRestriction_top_continuous hbM O alpha
    (fun _ hx => hMO hx.1) (D04.LocalStokes.form_C0 O alpha ha)
  have hbs : IsCompact (topSupport (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) alpha)) := by
    rw [← boundaryRestriction_ambient o.manifold alpha]
    exact boundaryRestriction_support_compact o.manifold _ (tangentRestriction_support_compact _ hc)
  obtain ⟨J, hJ⟩ := manifold_integral_exists hbM bO _ hbc hbs
  exact ⟨bO, hbO, I, J, hI, hJ⟩

/-- A scalar constant on a relative neighborhood has zero differential on
all tangent vectors, even for a merely C¹ manifold at a boundary point. -/
theorem fderiv_tangent_eq_zero {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (f : E n → ℝ) (x : M)
    (hf : DifferentiableAt ℝ f x) (V : Set M) (hV : IsOpen V) (hxV : x ∈ V)
    (a : ℝ) (he : ∀ y ∈ V, f y = a) (v : tangentSpace r k M x) :
    fderiv ℝ f x v = 0 := by
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x x.property
  have hcx : chartPoint c ⟨u, hu.1⟩ = x := Subtype.ext hux
  have hnear : (fun z => f (c.toFun z)) =ᶠ[𝓝[c.source] u] (fun _ => a) := by
    rw [nhdsWithin_eq_map_subtype_coe hu.1]
    change ∀ᶠ z : c.source in 𝓝 ⟨u, hu.1⟩, f (c.toFun z) = a
    have hn : V ∈ 𝓝 (chartPoint c ⟨u, hu.1⟩) := by rw [hcx]; exact hV.mem_nhds hxV
    have hn' := (D04.ManifoldIntegral.chartPoint_continuous c).continuousAt.eventually hn
    filter_upwards [hn'] with z hz
    exact he (chartPoint c z) hz
  have hf' : DifferentiableAt ℝ f (c.toFun u) := hux.symm ▸ hf
  have hchain := hf'.hasFDerivAt.comp_hasFDerivWithinAt u
    (D04.EmbeddedChart.hasDifferential c hM.1 hu.1)
  have hzero : (fderiv ℝ f (c.toFun u)).comp (chartDifferential c u) = 0 := by
    rw [← hchain.fderivWithin (D04.EmbeddedChart.source_uniqueDiff c u hu.1)]
    change fderivWithin ℝ (fun z => f (c.toFun z)) c.source u = 0
    rw [hnear.fderivWithin_eq_of_mem hu.1]
    exact fderivWithin_const_apply a
  have hv : v.val ∈ LinearMap.range (chartDifferential c u).toLinearMap := by
    rw [← D04.tangentSpace_chart c hM.1 hM.2.1 u hu.1, hux]
    exact v.property
  obtain ⟨w, hw⟩ := hv
  change chartDifferential c u w = v.val at hw
  have hz := congrArg (fun A : E k →L[ℝ] ℝ => A w) hzero
  change fderiv ℝ f (c.toFun u) (chartDifferential c u w) = 0 at hz
  rwa [hw, hux] at hz

/-- Wedge and degree transport preserve the zero covector on arbitrary
canonical tangent spaces, not just on coordinate Euclidean spaces. -/
theorem castCovector_zero_general {V : Type} [AddCommGroup V] [Module ℝ V]
    {a b : ℕ} (h : a = b) : castCovector h (0 : Covector V a) = 0 := by
  subst b
  rfl

theorem wedge_zero_left_general {V : Type} [AddCommGroup V] [Module ℝ V]
    {a b : ℕ} (beta : Covector V b) : wedge (0 : Covector V a) beta = 0 := by
  ext v
  simp [D04.wedge_apply]

/-- The finite derivative cancellation for ambient C¹ forms on C¹
manifolds. The compact set is the full ambient support along M. No derivative
of a pulled-back form or intrinsic C¹-manifold exterior derivative is used. -/
theorem ambient_partition_derivative {k n p m : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 k M) (O : Set (E n)) (alpha : FormField n p)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (U : Fin m → Set M) (w : Fin m → E n → ℝ)
    (hw : PartitionNear M (Subtype.val ⁻¹' tsupport alpha) U m id w) :
    (fun x : M => ∑ i, tangentRestriction 1 k M
      (exteriorDerivative (fun y => w i y • alpha y)) x) =
        tangentRestriction 1 k M (exteriorDerivative alpha) := by
  let f : E n → ℝ := fun y => ∑ i, w i y
  have hf : ContDiff ℝ 1 f := ContDiff.sum (fun i _ => (hw.1 i).of_le (by norm_num))
  have hc (i : Fin m) : IsCrForm (some 1) O (fun y => w i y • alpha y) :=
    D04.isCrForm_function_smul 1 O (w i) alpha ha.1
      ((D04.crOn_iff_contDiffOn 1 O _ ha.1).mpr ((hw.1 i).of_le (by norm_num)).contDiffOn) ha
  have hsum : (fun y => ∑ i, w i y • alpha y) = fun y => f y • alpha y := by
    funext y
    exact Finset.sum_smul.symm
  funext x
  have hcomp : (∑ i, tangentRestriction 1 k M
      (exteriorDerivative (fun y => w i y • alpha y)) x) =
      (∑ i, exteriorDerivative (fun y => w i y • alpha y) x).compLinearMap
        (tangentSpace 1 k M x).subtype := by
    ext v
    simp only [tangentRestriction, AlternatingMap.compLinearMap_apply, sum_apply]
  rw [hcomp, ← D04.exteriorDerivative_sum O _ ha.1 hc x (hMO x.property), hsum,
    D04.exteriorDerivative_function_smul O f alpha ha.1
      ((D04.crOn_iff_contDiffOn 1 O f ha.1).mpr hf.contDiffOn) ha x (hMO x.property)]
  change (D04.prependCovector _ _ + f x • exteriorDerivative alpha x).compLinearMap _ = _
  by_cases hx : x.val ∈ tsupport alpha
  · obtain ⟨V, hV, hKV, hone⟩ := hw.2.2.2.1
    have hxV := hKV hx
    have hfx : f x = 1 := hone x hxV
    have hdf : (exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x).compLinearMap
        (tangentSpace 1 k M x).subtype = 0 := by
      have hform : exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x =
          linearCovector (fderiv ℝ f x).toLinearMap :=
        D04.exteriorDerivative_function O f ha.1
          ((D04.crOn_iff_contDiffOn 1 O f ha.1).mpr hf.contDiffOn) x (hMO x.property)
      rw [hform]
      ext v
      change fderiv ℝ f x (v 0) = 0
      exact fderiv_tangent_eq_zero hM f x (hf.differentiable (by norm_num) x)
        V hV hxV 1 hone (v 0)
    have hp : (D04.prependCovector
        (exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x) (alpha x)).compLinearMap
        (tangentSpace 1 k M x).subtype = 0 := by
      unfold D04.prependCovector
      rw [D04.Intrinsic.cast_compLinearMap, D04.Intrinsic.wedge_compLinearMap, hdf]
      change castCovector (Nat.add_comm 1 p)
        (wedge (0 : Covector (tangentSpace 1 k M x) 1) _) = 0
      rw [wedge_zero_left_general, castCovector_zero_general]
    ext v
    change D04.prependCovector _ _ (fun j => (v j).val) +
      f x * exteriorDerivative alpha x (fun j => (v j).val) = _
    have hpv := congrArg (fun A => A v) hp
    change D04.prependCovector _ _ (fun j => (v j).val) = 0 at hpv
    rw [hpv, hfx, one_mul, zero_add]
    rfl
  · have haz : alpha x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hdz : exteriorDerivative alpha x = 0 := by
      by_contra h
      exact hx (D04.LocalStokes.exteriorDerivative_support alpha h)
    simp [haz, hdz, D04.prependCovector, D04.wedge_zero_right, D04.castCovector_zero,
      tangentRestriction]


open Function

/-! Integral value bridges. A support may meet the genuine flat boundary,
so a rectangle containing the support need not enclose it in its interior. -/

/-- Enlarging a rectangle does not change an integral supported in its
closed carrier. Extra subdivision cells contribute only on coordinate faces. -/
theorem integral_enlarge_closed_box {k : ℕ}
    {Q R : D04.Darboux.Box k} {f : E k → ℝ}
    (hq : D04.Darboux.Nondegenerate Q)
    (hl : ∀ i, R.lower i < Q.lower i) (hu : ∀ i, Q.upper i < R.upper i)
    (hs : support f ⊆ D04.Darboux.carrier Q)
    (hf : D04.Darboux.Integrable f R) :
    ∃ hQ : D04.Darboux.Integrable f Q,
      D04.Darboux.integral f R hf = D04.Darboux.integral f Q hQ := by
  classical
  let P : D04.Darboux.Grid R := fun i => D04.JordanRegions.threePartition
    (R.lower i) (Q.lower i) (Q.upper i) (R.upper i) (hl i) (hq i) (hu i)
  let c₀ : D04.Darboux.CellIndex P := fun _ => (1 : Fin 3)
  have hmid : D04.Darboux.cellBox P c₀ = Q := by
    apply D04.Darboux.Subdivision.box_ext <;> ext i <;> rfl
  have hi (c : D04.Darboux.CellIndex P) :
      D04.Darboux.Integrable f (D04.Darboux.cellBox P c) :=
    (D04.Darboux.subdivision_integrable f R hf.1 P).mp hf c
  have hQ : D04.Darboux.Integrable f Q := hmid ▸ hi c₀
  refine ⟨hQ, ?_⟩
  rw [D04.Darboux.subdivision_integral f R P hf hi, Finset.sum_eq_single c₀]
  · change D04.Darboux.lowerIntegral f _ = D04.Darboux.lowerIntegral f Q
    rw [hmid]
  · intro c _ hc
    obtain ⟨i, hi₀⟩ : ∃ i, c i ≠ (1 : Fin 3) := by
      by_contra! he
      exact hc (funext he)
    let T := D04.NullCovers.coordinateFace (D04.Darboux.cellBox P c) i (Q.lower i) ∪
      D04.NullCovers.coordinateFace (D04.Darboux.cellBox P c) i (Q.upper i)
    have hT : D04.NullCovers.Null T := by
      apply D04.JordanRegions.null_union
      · exact D04.NullCovers.contentZero_null (by
          simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left] using
            D04.NullCovers.finite_faces_contentZero (D04.Darboux.cellBox P c) {(i, Q.lower i)})
      · exact D04.NullCovers.contentZero_null (by
          simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left] using
            D04.NullCovers.finite_faces_contentZero (D04.Darboux.cellBox P c) {(i, Q.upper i)})
    apply D04.ExceptionalSets.integral_zero_off_null (hi c) hT
    intro x hx hxT
    by_contra hx0
    have hxQ := hs hx0
    have hxc := hx i
    change ![R.lower i, Q.lower i, Q.upper i, R.upper i] (c i).castSucc ≤ x i ∧
      x i ≤ ![R.lower i, Q.lower i, Q.upper i, R.upper i] (c i).succ at hxc
    have hxlo : x i ≠ Q.lower i := fun he => hxT (Or.inl ⟨hx, he⟩)
    have hxhi : x i ≠ Q.upper i := fun he => hxT (Or.inr ⟨hx, he⟩)
    generalize hci : c i = j at hxc hi₀
    fin_cases j
    · norm_num at hxc
      exact hxlo (le_antisymm hxc.2 (hxQ i).1)
    · exact hi₀ rfl
    · norm_num at hxc
      exact hxhi (le_antisymm (hxQ i).2 hxc.1)
  · simp

/-- A canonical relative-domain coefficient integral can be computed on a
nondegenerate closed rectangle containing its support, even on its faces. -/
theorem proper_on_closed_box {k : ℕ} {S : Set (E k)} {f : S → ℝ}
    (hf : ProperIntegrable f) (Q : D04.Darboux.Box k)
    (hq : D04.Darboux.Nondegenerate Q)
    (hs : support (D04.JordanRegions.zeroExtension f) ⊆ D04.Darboux.carrier Q) :
    ∃ hi : D04.Darboux.Integrable (D04.JordanRegions.zeroExtension f) Q,
      coefficientIntegral f = D04.Darboux.integral (D04.JordanRegions.zeroExtension f) Q hi := by
  let R : D04.Darboux.Box k := {
    lower := WithLp.toLp 2 (fun i => Q.lower i - 1)
    upper := WithLp.toLp 2 (fun i => Q.upper i + 1)
    ordered i := by change Q.lower i - 1 ≤ Q.upper i + 1; linarith [Q.ordered i] }
  have hR : D04.JordanRegions.Encloses (support (D04.JordanRegions.zeroExtension f)) R := by
    change closure _ ⊆ interior (D04.Darboux.carrier R)
    rw [D04.JordanRegions.interior_carrier]
    have hc : closure (support (D04.JordanRegions.zeroExtension f)) ⊆ D04.Darboux.carrier Q :=
      closure_minimal hs (D04.DiscontinuityCriterion.carrier_compact Q).isClosed
    intro x hx i
    obtain ⟨hlo, hhi⟩ := hc hx i
    constructor <;> dsimp [R] <;> linarith
  obtain ⟨hiR, hv⟩ := D04.DirectedSubstitution.proper_on_box hf R hR
  obtain ⟨hiQ, he⟩ := integral_enlarge_closed_box hq
    (fun i => by change Q.lower i - 1 < Q.lower i; linarith)
    (fun i => by change Q.upper i < Q.upper i + 1; linarith) hs hiR
  exact ⟨hiQ, hv.trans he⟩


open Specs.D04.C15.LocalStokesWithArtificialFaces.Model in
/-- The closed flat-bottom rectangle is a subset of the model half-space. -/
theorem halfBox_subset_halfSpace {k : ℕ} (Q : D04.Darboux.Box (k+1))
    (hb : Q.lower (Fin.last k) = 0) :
    D04.Darboux.carrier Q ⊆ halfSpace (k+1) := by
  intro x hx
  change 0 ≤ x (Fin.last k)
  simpa only [hb] using (hx (Fin.last k)).1

open Specs.D04.C15.LocalStokesWithArtificialFaces.Model in
/-- Artificial-face support control implies closed-rectangle support control. -/
theorem halfBoxInterior_subset_carrier {k : ℕ} (Q : D04.Darboux.Box (k+1)) :
    halfBoxInterior Q ⊆ D04.Darboux.carrier Q := by
  intro x hx i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨hx.2.1, hx.2.2.le⟩
  · exact ⟨(hx.1 j).1.le, (hx.1 j).2.le⟩

open Specs.D04.C15.LocalStokesWithArtificialFaces.Model in
/-- The genuine lower face uses the canonical flat inclusion. -/
theorem rectangle_lowerFace_eq_flatInclusion {k : ℕ} (Q : D04.Darboux.Box (k+1))
    (hb : Q.lower (Fin.last k) = 0) (x : E k) :
    rectangleFacePoint Q (Fin.last k) false x = D04.flatInclusion k x := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [rectangleFacePoint, hb]
  · simp [rectangleFacePoint]

open Specs.D04.C15.LocalStokesWithArtificialFaces.Model in
/-- Stokes on the whole model half-space in the canonical relative-domain
Riemann integrals. The flat face includes signed evaluation in dimension zero. -/
theorem halfspace_stokes_coefficientIntegral {k : ℕ} (theta : FormField (k+1) k)
    (ht : IsCrForm (some 1) univ theta)
    (hc : IsCompact (tsupport (fun x : halfSpace (k+1) => theta x))) :
    let f : halfSpace (k+1) → ℝ := fun x =>
      exteriorDerivative theta x (standardBasis (k+1))
    let g : ↥(univ : Set (E k)) → ℝ := fun x =>
      theta (D04.flatInclusion k x) (fun j => standardBasis (k+1) j.castSucc)
    ProperIntegrable f ∧ ProperIntegrable g ∧
      ∀ sigma : ℝ, sigma * coefficientIntegral f =
        (sigma * (-1 : ℝ)^(k+1)) * coefficientIntegral g := by
  classical
  dsimp only
  let H := halfSpace (k+1)
  let K := Subtype.val '' tsupport (fun x : H => theta x)
  have hK : IsCompact K := hc.image continuous_subtype_val
  have hKH : K ⊆ H := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hH : IsClosed H := isClosed_le continuous_const
    (EuclideanSpace.proj (Fin.last k)).continuous
  have hst : support theta ∩ H ⊆ K := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, subset_tsupport _ hx.1, rfl⟩
  have hsd := D04.LocalStokes.relative_derivative_support theta ht K hK.isClosed hst
  obtain ⟨Q, hq, hb, hsQ⟩ := D04.LocalStokes.enclose_compact_halfspace K hK hKH
  have hQH : D04.Darboux.carrier Q ⊆ H := halfBox_subset_halfSpace Q hb
  let f : H → ℝ := fun x => exteriorDerivative theta x (standardBasis (k+1))
  have hfc : Continuous f := by
    have he := D04.LocalStokes.form_evaluation_continuous univ (exteriorDerivative theta)
      (D04.exteriorDerivative_continuous univ theta ht) (standardBasis (k+1))
    exact (continuousOn_univ.mp he).comp continuous_subtype_val
  have hsf : tsupport f ⊆ Subtype.val ⁻¹' K := by
    apply closure_minimal _ (hK.isClosed.preimage continuous_subtype_val)
    intro x hx
    apply hsd
    refine ⟨?_, x.property⟩
    intro hz
    exact hx (by simp [f, hz])
  have hfk : HasCompactSupport f :=
    (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).of_isClosed_subset
      (isClosed_tsupport f) hsf
  have hfp : ProperIntegrable f := D04.DirectedSubstitution.halfspace_integrable H
    ⟨univ, isOpen_univ, by simp [H]⟩ f hfc hfk
  have hsfQ : support (D04.JordanRegions.zeroExtension f) ⊆ D04.Darboux.carrier Q := by
    intro x hx
    by_cases hxH : x ∈ H
    · have hf0 : f ⟨x, hxH⟩ ≠ 0 := by
        simpa only [mem_support, D04.JordanRegions.zeroExtension_apply f ⟨x, hxH⟩] using hx
      exact halfBoxInterior_subset_carrier Q (hsQ (hsf (subset_tsupport f hf0)))
    · exact (hx (D04.JordanRegions.zeroExtension_of_not_mem f hxH)).elim
  obtain ⟨hiF, hvF⟩ := proper_on_closed_box hfp Q hq hsfQ
  have hvFC : coefficientIntegral f = coordinateIntegral Q (exteriorDerivative theta) := by
    refine hvF.trans (D04.JordanRegions.lowerIntegral_congr ?_)
    intro x hx
    exact D04.JordanRegions.zeroExtension_apply f ⟨x, hQH hx⟩
  let g : ↥(univ : Set (E k)) → ℝ := fun x =>
    theta (D04.flatInclusion k x) (fun j => standardBasis (k+1) j.castSucc)
  have hgc : Continuous g := by
    have he := D04.LocalStokes.form_evaluation_continuous univ theta
      (D04.LocalStokes.form_C0 univ theta ht) (fun j : Fin k => standardBasis (k+1) j.castSucc)
    exact (continuousOn_univ.mp he).comp ((D04.flatInclusion k).continuous.comp continuous_subtype_val)
  have hgs (x : (univ : Set (E k))) (hx : g x ≠ 0) : D04.flatInclusion k x ∈ K := by
    apply hst
    refine ⟨?_, ?_⟩
    · intro hz
      exact hx (by simp [g, hz])
    · change 0 ≤ D04.flatInclusion k x (Fin.last k)
      simp
  have hgK : tsupport g ⊆ Subtype.val ⁻¹' (D04.flatProjection k '' K) := by
    apply closure_minimal _ (((hK.image (D04.flatProjection k).continuous).isClosed).preimage
      continuous_subtype_val)
    intro x hx
    exact ⟨D04.flatInclusion k x, hgs x hx, D04.flatProjection_inclusion k x⟩
  have hgk : HasCompactSupport g :=
    (isClosed_univ.isClosedEmbedding_subtypeVal.isCompact_preimage
      (hK.image (D04.flatProjection k).continuous)).of_isClosed_subset (isClosed_tsupport g) hgK
  have hgp : ProperIntegrable g := D04.DirectedSubstitution.parameter_integrable false
    ⟨univ, isOpen_univ, by simp [parameterSpace]⟩ hgc hgk
  let B := rectangleFaceBox Q (Fin.last k)
  have hB : D04.Darboux.Nondegenerate B := fun j => hq ((Fin.last k).succAbove j)
  have hsgB : support (D04.JordanRegions.zeroExtension g) ⊆ D04.Darboux.carrier B := by
    intro x hx
    have hg0 : g ⟨x, mem_univ x⟩ ≠ 0 := by
      simpa only [mem_support, D04.JordanRegions.zeroExtension_apply g ⟨x, mem_univ x⟩] using hx
    have hxQ := halfBoxInterior_subset_carrier Q (hsQ (hgs _ hg0))
    intro j
    simpa [B, rectangleFaceBox] using hxQ j.castSucc
  obtain ⟨hiG, hvG⟩ := proper_on_closed_box hgp B hB hsgB
  have hvGC : coefficientIntegral g = coordinateFaceIntegral Q theta (Fin.last k) false := by
    refine hvG.trans (D04.JordanRegions.lowerIntegral_congr ?_)
    intro x hx
    rw [D04.JordanRegions.zeroExtension_apply g ⟨x, mem_univ x⟩]
    change theta (D04.flatInclusion k x) _ = theta (rectangleFacePoint Q (Fin.last k) false x) _
    rw [rectangle_lowerFace_eq_flatInclusion Q hb]
    simp
  refine ⟨hfp, hgp, ?_⟩
  intro sigma
  change sigma * coefficientIntegral f = (sigma * (-1 : ℝ)^(k+1)) * coefficientIntegral g
  rw [hvFC, hvGC, D04.LocalStokes.coordinate_halfspace Q univ theta ht (subset_univ _)]
  · ring
  · intro x hx
    exact hsQ (hst ⟨hx.1, hQH hx.2⟩)


/-- A C¹ extension determines the exterior derivative on any uniquely
 differentiable relative source. No values of the representative off S enter. -/
theorem withinExteriorDerivative_of_extension {a p : ℕ} {S : Set (E a)} {u : E a}
    (hu : u ∈ S) (hS : UniqueDiffWithinAt ℝ S u)
    (alpha beta : FormField a p) (ha : IsCrForm (some 1) univ alpha)
    (he : alpha =ᶠ[𝓝[S] u] beta) :
    withinExteriorDerivative S beta u = exteriorDerivative alpha u := by
  have hcongr : withinExteriorDerivative S beta u = withinExteriorDerivative S alpha u :=
    D04.Intrinsic.withinExteriorDerivative_congr hu beta alpha he.symm
  rw [hcongr]
  conv_rhs =>
    change D04.exteriorDerivative alpha u
    rw [D04.exteriorDerivative_formula]
  simp only [withinExteriorDerivative,
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  have hd := D04.isCrForm_coefficient_differentiableAt univ alpha ha u (mem_univ _) I
  change (fderivWithin ℝ (fun y => D04.coefficient (D04.standardBasis a) (alpha y) I) S u)
    (D04.standardBasis a j) • _ = _
  rw [hd.fderivWithin hS, D04.scalarPartialDerivative_eq_fderiv _ _ hd]
  rfl

open Specs.D04.C15.LocalStokesWithArtificialFaces.Model in
/-- Local Stokes on any relatively open half-space domain, in the original
within-source derivative and the canonical zero-extension coefficient integrals.
The extension needed for the proof is constructed from local C¹ data. -/
theorem compact_relative_halfspace_stokes {k : ℕ} (U : Set (E (k+1)))
    (eta : FormField (k+1) k) (hU : IsOpen U)
    (hl : LocallyC1On (U ∩ halfSpace (k+1)) eta)
    (hc : IsCompact (tsupport (fun x : ↥(U ∩ halfSpace (k+1)) => eta x))) :
    let S := U ∩ halfSpace (k+1)
    let T := (D04.flatInclusion k) ⁻¹' S
    let f : S → ℝ := fun x => withinExteriorDerivative S eta x (standardBasis (k+1))
    let g : T → ℝ := fun x => eta (D04.flatInclusion k x)
      (fun j => standardBasis (k+1) j.castSucc)
    ProperIntegrable f ∧ ProperIntegrable g ∧
      ∀ sigma : ℝ, sigma * coefficientIntegral f =
        (sigma * (-1 : ℝ)^(k+1)) * coefficientIntegral g := by
  classical
  dsimp only
  let H := halfSpace (k+1)
  let S := U ∩ H
  let T := (D04.flatInclusion k) ⁻¹' S
  let K := Subtype.val '' tsupport (fun x : S => eta x)
  have hK : IsCompact K := hc.image continuous_subtype_val
  have hKU : K ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property.1
  have hKH : K ⊆ H := by rintro _ ⟨x, _, rfl⟩; exact x.property.2
  obtain ⟨theta, ht, he⟩ := D04.LocalStokes.compact_relative_extension H U eta hU hl hc
  have hH : IsClosed H := isClosed_le continuous_const
    (EuclideanSpace.proj (Fin.last k)).continuous
  have hst : support theta ∩ H ⊆ K := by
    intro x hx
    have hxU : x ∈ U := by
      by_contra hn
      exact hx.1 ((he hx.2).trans (by simp [extendForm, hn]))
    have heta : eta x ≠ 0 := by
      intro hz
      exact hx.1 ((he hx.2).trans (by simp [extendForm, hxU, hz]))
    exact ⟨⟨x, hxU, hx.2⟩, subset_tsupport _ heta, rfl⟩
  have hts : tsupport (fun x : H => theta x) ⊆ Subtype.val ⁻¹' K := by
    apply closure_minimal _ (hK.isClosed.preimage continuous_subtype_val)
    intro x hx
    exact hst ⟨hx, x.property⟩
  have htc : IsCompact (tsupport (fun x : H => theta x)) :=
    (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).of_isClosed_subset
      (isClosed_tsupport _) hts
  obtain ⟨hfp, hgp, hv⟩ := halfspace_stokes_coefficientIntegral theta ht htc
  let F : H → ℝ := fun x => exteriorDerivative theta x (standardBasis (k+1))
  let G : ↥(univ : Set (E k)) → ℝ := fun x =>
    theta (D04.flatInclusion k x) (fun j => standardBasis (k+1) j.castSucc)
  let f : S → ℝ := fun x => withinExteriorDerivative S eta x (standardBasis (k+1))
  let g : T → ℝ := fun x => eta (D04.flatInclusion k x)
    (fun j => standardBasis (k+1) j.castSucc)
  have huq : UniqueDiffOn ℝ S := by
    have hh := (D04.parameterSpace_uniqueDiff (k+1) true).inter hU
    simpa only [parameterSpace, ite_true, inter_comm] using hh
  have hd (x : E (k+1)) (hx : x ∈ S) :
      withinExteriorDerivative S eta x = exteriorDerivative theta x := by
    apply withinExteriorDerivative_of_extension hx (huq x hx) theta eta ht
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (he hy.2).trans (by simp [extendForm, hy.1])
  have hsd := D04.LocalStokes.relative_derivative_support theta ht K hK.isClosed hst
  have hfz : D04.JordanRegions.zeroExtension f = D04.JordanRegions.zeroExtension F := by
    funext x
    by_cases hxS : x ∈ S
    · rw [D04.JordanRegions.zeroExtension_apply f ⟨x, hxS⟩,
        D04.JordanRegions.zeroExtension_apply F ⟨x, hxS.2⟩]
      exact congrArg (fun a => a (standardBasis (k+1))) (hd x hxS)
    · rw [D04.JordanRegions.zeroExtension_of_not_mem f hxS]
      by_cases hxH : x ∈ H
      · rw [D04.JordanRegions.zeroExtension_apply F ⟨x, hxH⟩]
        have hz : exteriorDerivative theta x = 0 := by
          by_contra hn
          exact hxS ⟨hKU (hsd ⟨hn, hxH⟩), hxH⟩
        simp [F, hz]
      · rw [D04.JordanRegions.zeroExtension_of_not_mem F hxH]
  have hgz : D04.JordanRegions.zeroExtension g = D04.JordanRegions.zeroExtension G := by
    funext x
    rw [D04.JordanRegions.zeroExtension_apply G ⟨x, mem_univ x⟩]
    have hxH : D04.flatInclusion k x ∈ H := by
      change 0 ≤ D04.flatInclusion k x (Fin.last k)
      simp
    have he' := he hxH
    by_cases hxT : x ∈ T
    · rw [D04.JordanRegions.zeroExtension_apply g ⟨x, hxT⟩]
      have hh : theta (D04.flatInclusion k x) = eta (D04.flatInclusion k x) :=
        he'.trans (by simp [extendForm, hxT.1])
      change eta _ _ = theta _ _
      rw [hh]
    · rw [D04.JordanRegions.zeroExtension_of_not_mem g hxT]
      have hxU : D04.flatInclusion k x ∉ U := fun hu => hxT ⟨hu, hxH⟩
      have hz : theta (D04.flatInclusion k x) = 0 := he'.trans (by simp [extendForm, hxU])
      simp [G, hz]
  have hf := D04.DirectedSubstitution.proper_congr hfz
  have hg := D04.DirectedSubstitution.proper_congr hgz
  refine ⟨hf.1.mpr hfp, hg.1.mpr hgp, ?_⟩
  intro sigma
  change sigma * coefficientIntegral f = (sigma * (-1 : ℝ)^(k+1)) * coefficientIntegral g
  have hfv : coefficientIntegral f = coefficientIntegral F := hf.2
  have hgv : coefficientIntegral g = coefficientIntegral G := hg.2
  rw [hfv, hgv]
  exact hv sigma

/-- Compact support contained in a chart pulls back to compact relative
support of the entire coordinate form, in every degree. -/
theorem chartPullback_support_compact {k n p : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 2 k n M) (omega : IntrinsicForm (k := k) M p)
    (hc : IsCompact (formSupport omega))
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient) :
    IsCompact (tsupport (fun u : c.source => chartPullback c omega u)) := by
  let e := D04.ManifoldIntegral.chartHomeomorph c
  have ht : IsCompact (Subtype.val ⁻¹' formSupport omega :
      Set ↥(Subtype.val ⁻¹' c.ambient : Set M)) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using hs)).mpr hc
  have hp := (e.isCompact_preimage).mpr ht
  apply hp.of_isClosed_subset (isClosed_tsupport _) _
  apply closure_minimal _ ((hc.isClosed.preimage continuous_subtype_val).preimage e.continuous)
  intro u hu
  apply subset_closure
  intro hz
  apply hu
  change chartPullback c omega u = 0
  simp only [chartPullback, dite_eq_left u.property]
  change (omega (chartPoint c u)).compLinearMap _ = 0
  have hz' : omega (chartPoint c u) = 0 := hz
  rw [hz']
  rfl

/-- The intrinsic chart formula on a half-space chart, expressed in the
canonical coefficient integrals of the original coordinate forms. -/
theorem intrinsic_chart_halfspace_stokes {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 (d+1) M) (c : EmbeddedChart 2 (d+1) n M)
    (hh : c.half = true) (omega : IntrinsicForm (k := d+1) M d)
    (homega : IntrinsicC1 omega) (hc : IsCompact (formSupport omega))
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient) :
    let T := (D04.flatInclusion d) ⁻¹' c.source
    let g : T → ℝ := fun u => chartPullback c omega (D04.flatInclusion d u)
      (fun j => standardBasis (d+1) j.castSucc)
    ProperIntegrable (topCoefficient (intrinsicExteriorDerivative omega) c) ∧
      ProperIntegrable g ∧ ∀ sigma : ℝ,
        sigma * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) =
          (sigma * (-1 : ℝ)^(d+1)) * coefficientIntegral g := by
  obtain ⟨U, hU, he⟩ := c.source_open
  have he' : c.source = U ∩ halfSpace (d+1) := by
    simpa only [parameterSpace, hh, ite_true, inter_comm] using he
  have hl : Specs.D04.C15.LocalStokesWithArtificialFaces.Model.LocallyC1On
      (U ∩ halfSpace (d+1)) (chartPullback c omega) := by
    intro u hu
    obtain ⟨W, eta, hW, huW, heta, het⟩ := homega c u (he' ▸ hu)
    exact ⟨W, eta, huW, heta, fun v hv => het ⟨he' ▸ hv.2, hv.1⟩⟩
  have hcs : IsCompact (tsupport (fun u : ↥(U ∩ halfSpace (d+1)) =>
      chartPullback c omega u)) := he' ▸ chartPullback_support_compact c omega hc hs
  have ht := compact_relative_halfspace_stokes U (chartPullback c omega) hU hl hcs
  rw [← he'] at ht
  have heq : (fun u : c.source => withinExteriorDerivative c.source
      (chartPullback c omega) u (standardBasis (d+1))) =
      topCoefficient (intrinsicExteriorDerivative omega) c := by
    funext u
    have hd := (D04.Intrinsic.intrinsicExteriorDerivative_spec hM omega homega).2 c u u.property
    rw [← hd]
    simp only [chartPullback, dite_eq_left u.property]
    rfl
  simpa only [heq] using ht

/-- Local C¹ extensions on an open domain give its ordinary C¹ form
regularity; the representative away from that domain is irrelevant. -/
theorem locallyC1On_open {a p : ℕ} (U : Set (E a)) (eta : FormField a p)
    (hU : IsOpen U)
    (hl : Specs.D04.C15.LocalStokesWithArtificialFaces.Model.LocallyC1On U eta) :
    IsCrForm (some 1) U eta := by
  apply (D04.isCrForm_finite_contDiffOn 1 U eta hU).mpr
  intro I
  apply contDiffOn_of_locally_contDiffOn
  intro u hu
  obtain ⟨W, theta, huW, ht, he⟩ := hl u hu
  refine ⟨W, ht.1, huW, ?_⟩
  have hc := (D04.isCrForm_finite_contDiffOn 1 W theta ht.1).mp ht I
  apply (hc.mono inter_subset_right).congr
  intro v hv
  exact congrArg (fun cov => D04.coefficient (D04.standardBasis a) cov I)
    (he ⟨hv.2, hv.1⟩).symm

/-- On an open domain the within-source formula agrees with the ordinary
exterior derivative of the same C¹ representative. -/
theorem withinExteriorDerivative_open {a p : ℕ} (U : Set (E a))
    (eta : FormField a p) (ht : IsCrForm (some 1) U eta) {u : E a} (hu : u ∈ U) :
    withinExteriorDerivative U eta u = exteriorDerivative eta u := by
  conv_rhs =>
    change D04.exteriorDerivative eta u
    rw [D04.exteriorDerivative_formula]
  simp only [withinExteriorDerivative]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  have hd := D04.isCrForm_coefficient_differentiableAt U eta ht u hu I
  change (fderivWithin ℝ (fun y => D04.coefficient (D04.standardBasis a) (eta y) I) U u)
    (D04.standardBasis a j) • _ = _
  rw [fderivWithin_of_isOpen ht.1 hu, D04.scalarPartialDerivative_eq_fderiv _ _ hd]
  rfl

/-- The local interior formula with a within-source derivative and only
local C¹ extensions assumed. -/
theorem compact_relative_interior_stokes {k : ℕ} (U : Set (E (k+1)))
    (eta : FormField (k+1) k) (hU : IsOpen U)
    (hl : Specs.D04.C15.LocalStokesWithArtificialFaces.Model.LocallyC1On U eta)
    (hc : IsCompact (tsupport (fun x : U => eta x))) :
    let f : U → ℝ := fun x => withinExteriorDerivative U eta x (standardBasis (k+1))
    ProperIntegrable f ∧ coefficientIntegral f = 0 := by
  have ht := locallyC1On_open U eta hU hl
  have hv := D04.LocalStokes.compact_interior_openIntegral U eta ht hc
  have heq : (fun x : U => withinExteriorDerivative U eta x (standardBasis (k+1))) =
      (fun x : U => exteriorDerivative eta x (standardBasis (k+1))) := by
    funext x
    rw [withinExteriorDerivative_open U eta ht x.property]
  dsimp only
  rw [heq]
  exact ⟨hv.1.2, hv.2⟩

/-- A compactly supported intrinsic form contained in an interior chart has
zero integral of its intrinsic exterior derivative in that chart. -/
theorem intrinsic_chart_interior_stokes {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 (d+1) M) (c : EmbeddedChart 2 (d+1) n M)
    (hh : c.half = false) (omega : IntrinsicForm (k := d+1) M d)
    (homega : IntrinsicC1 omega) (hc : IsCompact (formSupport omega))
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient) :
    ProperIntegrable (topCoefficient (intrinsicExteriorDerivative omega) c) ∧
      coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) = 0 := by
  have hU : IsOpen c.source := by
    obtain ⟨U, hU, he⟩ := c.source_open
    simpa only [he, parameterSpace, hh, Bool.false_eq_true, ite_false, univ_inter] using hU
  have hl : Specs.D04.C15.LocalStokesWithArtificialFaces.Model.LocallyC1On
      c.source (chartPullback c omega) := by
    intro u hu
    obtain ⟨W, eta, hW, huW, heta, het⟩ := homega c u hu
    exact ⟨W, eta, huW, heta, fun v hv => het ⟨hv.2, hv.1⟩⟩
  have ht := compact_relative_interior_stokes c.source (chartPullback c omega) hU hl
    (chartPullback_support_compact c omega hc hs)
  have heq : (fun u : c.source => withinExteriorDerivative c.source
      (chartPullback c omega) u (standardBasis (d+1))) =
      topCoefficient (intrinsicExteriorDerivative omega) c := by
    funext u
    have hd := (D04.Intrinsic.intrinsicExteriorDerivative_spec hM omega homega).2 c u u.property
    rw [← hd]
    simp only [chartPullback, dite_eq_left u.property]
    rfl
  simpa only [heq] using ht

/-- Restriction to the actual manifold boundary, in the boundary chart
constructed from a half-space chart, is precisely the flat coordinate trace.
This statement also includes degree zero. -/
theorem boundaryChart_trace {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 (d+1) M) (c : EmbeddedChart 2 (d+1) n M)
    (hh : c.half = true) (omega : IntrinsicForm (k := d+1) M d)
    (v : E d)
    (hv : v ∈ (D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh).source) :
    topCoefficient (boundaryRestriction omega)
      (D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh) ⟨v, hv⟩ =
        chartPullback c omega (D04.flatInclusion d v)
          (fun j => standardBasis (d+1) j.castSucc) := by
  let b := D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh
  have hu : D04.flatInclusion d v ∈ c.source := hv
  let x : intrinsicBoundary 2 (d+1) M := ⟨b.toFun v, (b.map_source hv).1⟩
  have he (j : Fin d) :
      boundaryTangentInclusion 2 d M x (tangentChartMap b v hv (standardBasis d j)) =
        chartTangentMap c (D04.flatInclusion d v) hu (standardBasis (d+1) j.castSucc) := by
    apply Subtype.ext
    rw [boundaryTangentInclusion_apply hM]
    change chartDifferential b v (standardBasis d j) =
      chartDifferential c (D04.flatInclusion d v) (standardBasis (d+1) j.castSucc)
    have hd : chartDifferential b v =
        (chartDifferential c (D04.flatInclusion d v)).comp (D04.flatInclusion d) :=
      D04BoundaryOrientation.boundaryChart_differential c hM.1 hM.2.1 hh v hv
    rw [hd, ContinuousLinearMap.comp_apply, D04BoundaryOrientation.flatInclusion_basis]
  have hp : chartPullback c omega (D04.flatInclusion d v) =
      (omega ⟨c.toFun (D04.flatInclusion d v), (c.map_source hu).1⟩).compLinearMap
        (chartTangentMap c (D04.flatInclusion d v) hu) :=
    D04.Intrinsic.chartPullback_of_mem c omega hu
  rw [hp]
  exact congrArg (omega ⟨c.toFun (D04.flatInclusion d v), (c.map_source hu).1⟩) (funext he)

/-- The local half-space identity directly relates the coefficients of the
bulk intrinsic derivative and of the actual boundary restriction. -/
theorem intrinsic_chart_boundary_integrals {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 (d+1) M) (c : EmbeddedChart 2 (d+1) n M)
    (hh : c.half = true) (omega : IntrinsicForm (k := d+1) M d)
    (homega : IntrinsicC1 omega) (hc : IsCompact (formSupport omega))
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient) :
    ∃ b : EmbeddedChart 2 d n (intrinsicBoundary 2 (d+1) M),
      b.half = false ∧ b.ambient = c.ambient ∧
      b.source = (D04.flatInclusion d) ⁻¹' c.source ∧
      ProperIntegrable (topCoefficient (intrinsicExteriorDerivative omega) c) ∧
      ProperIntegrable (topCoefficient (boundaryRestriction omega) b) ∧
      ∀ sigma : ℝ,
        sigma * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) =
          (sigma * (-1 : ℝ)^(d+1)) *
            coefficientIntegral (topCoefficient (boundaryRestriction omega) b) := by
  let b := D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh
  have ht := intrinsic_chart_halfspace_stokes hM c hh omega homega hc hs
  have he : (fun v : b.source => chartPullback c omega (D04.flatInclusion d v)
      (fun j => standardBasis (d+1) j.castSucc)) =
      topCoefficient (boundaryRestriction omega) b := by
    funext v
    exact (boundaryChart_trace hM c hh omega v v.property).symm
  change ProperIntegrable (topCoefficient (intrinsicExteriorDerivative omega) c) ∧
    ProperIntegrable (fun v : b.source => chartPullback c omega (D04.flatInclusion d v)
      (fun j => standardBasis (d+1) j.castSucc)) ∧
    ∀ sigma : ℝ, sigma * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) =
      (sigma * (-1 : ℝ)^(d+1)) * coefficientIntegral
        (fun v : b.source => chartPullback c omega (D04.flatInclusion d v)
          (fun j => standardBasis (d+1) j.castSucc)) at ht
  rw [he] at ht
  exact ⟨b, rfl, rfl, rfl, ht⟩

/-- For positive-dimensional boundaries, the coordinate identity gives the
actual manifold-integral equality for a form supported in one signed chart.
The boundary orientation is any orientation satisfying outward-first. -/
theorem intrinsic_single_chart_halfspace_positive {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 (d+2) M)
    (bO : PositiveManifoldOrientation 2 (d+1) (intrinsicBoundary 2 (d+2) M))
    (hout : OutwardFirst (d+1) o bO)
    (c : EmbeddedChart 2 (d+2) n M) (hh : c.half = true)
    (s : PointSign) (hsgn : ∀ u : c.source, chartSign o.atPoint c u u.property = s.val)
    (omega : IntrinsicForm (k := d+2) M (d+1)) (homega : IntrinsicC1 omega)
    (hc : IsCompact (formSupport omega))
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient)
    {I J : ℝ} (hI : HasPositiveIntegral o (intrinsicExteriorDerivative omega) I)
    (hJ : HasPositiveIntegral bO (boundaryRestriction omega) J) : I = J := by
  classical
  obtain ⟨nu, _, hnu, hpos⟩ := hout
  obtain ⟨q, _, huniq⟩ := D04BoundaryOrientation.boundary_orientation o nu hnu
  have hbO : bO = D04BoundaryOrientation.inducedBoundaryOrientation o nu hnu :=
    (huniq bO hpos).trans (huniq _ (D04BoundaryOrientation.boundaryOrientationField_positive o nu hnu)).symm
  let b := D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh
  let t : PointSign := ⟨s.val * (-1 : ℝ)^(d+2), by
    rcases s.property with h | h <;> rcases neg_one_pow_eq_or ℝ (d+2) with hp | hp <;>
      simp [h, hp]⟩
  have hbt : ∀ v : b.source, chartSign bO.atPoint b v v.property = t.val := by
    intro v
    have hb : bO.atPoint = D04BoundaryOrientation.boundaryOrientationField o nu hnu :=
      congrArg (fun q => q.atPoint) hbO
    rw [hb]
    have hsign : chartSign (D04BoundaryOrientation.boundaryOrientationField o nu hnu)
        b v v.property = chartSign o.atPoint c (D04.flatInclusion (d+1) v) v.property *
          (-1 : ℝ)^(d+2) :=
      D04BoundaryOrientation.boundary_chart_sign o nu hnu c hh v v.property
    rw [hsign, hsgn ⟨D04.flatInclusion (d+1) v, v.property⟩]
  have hbs : topSupport (boundaryRestriction omega) ⊆ Subtype.val ⁻¹' b.ambient := by
    intro x hx
    exact hs (boundaryRestriction_support omega hx)
  have hds : topSupport (intrinsicExteriorDerivative omega) ⊆ Subtype.val ⁻¹' c.ambient :=
    (intrinsic_derivative_support o.manifold omega homega).trans hs
  obtain ⟨P⟩ := hI.2.2.1
  obtain ⟨Q⟩ := hJ.2.2.1
  have hi : I = s.val * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) :=
    ((hI.2.2.2 P).2).symm.trans
      (D04.ManifoldIntegralIndependence.oriented_single_chart o _ hI.1 hI.2.1 P c hds s hsgn).2
  have hj : J = (s.val * (-1 : ℝ)^(d+2)) *
      coefficientIntegral (topCoefficient (boundaryRestriction omega) b) :=
    ((hJ.2.2.2 Q).2).symm.trans
      (D04.ManifoldIntegralIndependence.oriented_single_chart bO _ hJ.1 hJ.2.1 Q b hbs t hbt).2
  have ht := (intrinsic_chart_halfspace_stokes o.manifold c hh omega homega hc hs).2.2 s.val
  have he : (fun v : b.source => chartPullback c omega (D04.flatInclusion (d+1) v)
      (fun j => standardBasis (d+2) j.castSucc)) =
      topCoefficient (boundaryRestriction omega) b := by
    funext v
    exact (boundaryChart_trace o.manifold c hh omega v v.property).symm
  change s.val * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) =
    (s.val * (-1 : ℝ)^(d+2)) * coefficientIntegral
      (fun v : b.source => chartPullback c omega (D04.flatInclusion (d+1) v)
        (fun j => standardBasis (d+2) j.castSucc)) at ht
  rw [he] at ht
  exact hi.trans (ht.trans hj.symm)

/-- Canonical coefficient integration of the zero function, on any source. -/
theorem coefficientIntegral_zero {k : ℕ} (S : Set (E k)) :
    ProperIntegrable (fun _ : S => (0 : ℝ)) ∧
      coefficientIntegral (fun _ : S => (0 : ℝ)) = 0 := by
  let e : (∅ : Set (E k)) → ℝ := fun _ => 0
  have he : D04.JordanRegions.zeroExtension (fun _ : S => (0 : ℝ)) =
      D04.JordanRegions.zeroExtension e := by
    funext x
    simp [D04.JordanRegions.zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension]
  have hc := D04.DirectedSubstitution.proper_congr he
  have hz := D04.DirectedSubstitution.empty_integral e
  exact ⟨hc.1.mpr hz.1, hc.2.trans hz.2⟩

/-- The zero top field has the actual manifold integral zero. -/
theorem positive_integral_zero {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) :
    HasPositiveIntegral o (0 : TangentTopField r k M) 0 := by
  have hc : ContinuousTopField (0 : TangentTopField r k M) := by
    intro c
    change Continuous (fun _ : c.source => (0 : ℝ))
    exact continuous_const
  have hk : IsCompact (topSupport (0 : TangentTopField r k M)) := by
    simp [topSupport]
  obtain ⟨I, hi⟩ := positive_integral_exists o 0 hc hk
  obtain ⟨P⟩ := hi.2.2.1
  have hv : orientedIntegral (0 : TangentTopField r k M) P = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have he : localizedTopCoefficient (0 : TangentTopField r k M) (P.chart i) (P.weight i) =
        (fun _ : (P.chart i).source => (0 : ℝ)) := by
      funext u
      change P.weight i ((P.chart i).toFun u) * 0 = 0
      exact mul_zero _
    rw [he, (coefficientIntegral_zero (P.chart i).source).2, mul_zero]
  have hI : I = 0 := ((hi.2.2.2 P).2).symm.trans hv
  rwa [hI] at hi

/-- Additivity for the quantified, partition-independent integral predicate. -/
theorem positive_integral_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (eta xi : TangentTopField r k M)
    {I J : ℝ} (hI : HasPositiveIntegral o eta I) (hJ : HasPositiveIntegral o xi J) :
    HasPositiveIntegral o (eta + xi) (I + J) := by
  have hc := D04.ManifoldIntegralIndependence.continuousTopField_add hI.1 hJ.1
  have hk : IsCompact (topSupport (eta + xi)) :=
    (hI.2.1.union hJ.2.1).of_isClosed_subset isClosed_closure
      (D04.ManifoldIntegralIndependence.topSupport_add_subset eta xi)
  obtain ⟨K, hK⟩ := positive_integral_exists o (eta + xi) hc hk
  obtain ⟨P⟩ := hI.2.2.1
  obtain ⟨Q⟩ := hJ.2.2.1
  obtain ⟨R⟩ := hK.2.2.1
  have hv : K = I + J := by
    rw [← (hK.2.2.2 R).2,
      D04.ManifoldIntegralIndependence.oriented_add o eta xi hI.1 hJ.1 hI.2.1 hJ.2.1 P Q R,
      (hI.2.2.2 P).2, (hJ.2.2.2 Q).2]
  rwa [hv] at hK

/-- Finite additivity for arbitrary top fields; no derivative identity is
assumed in this analytic lemma. -/
theorem positive_integral_sum {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} {ι : Type*}
    (o : PositiveManifoldOrientation r k M) (eta : ι → TangentTopField r k M)
    (I : ι → ℝ) (s : Finset ι) (hi : ∀ i ∈ s, HasPositiveIntegral o (eta i) (I i)) :
    HasPositiveIntegral o (∑ i ∈ s, eta i) (∑ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using positive_integral_zero o
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using positive_integral_add o (eta a)
      (∑ i ∈ s, eta i) (hi a (Finset.mem_insert_self a s))
      (ih (fun i h => hi i (Finset.mem_insert_of_mem h)))

/-- The actual integral value is unique, even when its partition is chosen
independently in the two assertions. -/
theorem positive_integral_unique {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (eta : TangentTopField r k M)
    {I J : ℝ} (hi : HasPositiveIntegral o eta I) (hj : HasPositiveIntegral o eta J) : I = J := by
  obtain ⟨P⟩ := hi.2.2.1
  exact ((hi.2.2.2 P).2).symm.trans (hj.2.2.2 P).2

/-- An interior chart contains no intrinsic boundary point. Consequently a
form supported in its image restricts to zero on the boundary. -/
theorem boundaryRestriction_eq_zero_of_interior_support {r : ℕ∞ω} {d n : ℕ}
    {M : Set (E n)} (hM : IsEmbeddedManifold r (d+1) M)
    (c : EmbeddedChart r (d+1) n M) (hh : c.half = false)
    (omega : TangentForm r (d+1) M d)
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient) :
    boundaryRestriction omega = 0 := by
  funext x
  have hz : omega ⟨x, x.property.1⟩ = 0 := by
    by_contra hn
    have hxA := hs (subset_closure hn)
    have hxT : (x : E n) ∈ M ∩ c.ambient := ⟨x.property.1, hxA⟩
    have hu := c.map_target hxT
    have hxB : c.toFun (c.invFun x) ∈ intrinsicBoundary r (d+1) M := by
      rw [c.right_inv x hxT]
      exact x.property
    have hb := (D04.chart_intrinsicBoundary c hM.1 hM.2.1 _ hu).mp hxB
    have hfalse : false = true := hh.symm.trans hb.1
    cases hfalse
  simp [boundaryRestriction, hz]

/-- Interior-chart local Stokes as equality of the actual two positive
manifold integrals. -/
theorem intrinsic_single_chart_interior_positive {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 (d+2) M)
    (bO : PositiveManifoldOrientation 2 (d+1) (intrinsicBoundary 2 (d+2) M))
    (c : EmbeddedChart 2 (d+2) n M) (hh : c.half = false)
    (s : PointSign) (hsgn : ∀ u : c.source, chartSign o.atPoint c u u.property = s.val)
    (omega : IntrinsicForm (k := d+2) M (d+1)) (homega : IntrinsicC1 omega)
    (hc : IsCompact (formSupport omega))
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient)
    {I J : ℝ} (hI : HasPositiveIntegral o (intrinsicExteriorDerivative omega) I)
    (hJ : HasPositiveIntegral bO (boundaryRestriction omega) J) : I = J := by
  obtain ⟨P⟩ := hI.2.2.1
  have hds : topSupport (intrinsicExteriorDerivative omega) ⊆ Subtype.val ⁻¹' c.ambient :=
    (intrinsic_derivative_support o.manifold omega homega).trans hs
  have hi : I = s.val * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) :=
    ((hI.2.2.2 P).2).symm.trans
      (D04.ManifoldIntegralIndependence.oriented_single_chart o _ hI.1 hI.2.1 P c hds s hsgn).2
  rw [(intrinsic_chart_interior_stokes o.manifold c hh omega homega hc hs).2, mul_zero] at hi
  have hz := boundaryRestriction_eq_zero_of_interior_support o.manifold c hh omega hs
  rw [hz] at hJ
  exact hi.trans (positive_integral_unique bO 0 hJ (positive_integral_zero bO)).symm

/-- The support of a weighted form lies in the relative support of the
weight; this supplies compactness and chart support from ambient partitions. -/
theorem formSupport_weight_subset {r : ℕ∞ω} {k n p : ℕ} {M : Set (E n)}
    (omega : TangentForm r k M p) (w : E n → ℝ) :
    formSupport (fun x : M => w x • omega x) ⊆ tsupport (fun x : M => w x) := by
  apply closure_mono
  intro x hx
  intro hz
  exact hx (by simp [hz])

/-- Boundary restriction commutes with the finite pointwise sums used by
the ambient smooth partition. -/
theorem boundaryRestriction_sum {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    {ι : Type*} [Fintype ι] (omega : ι → TangentForm r (d+1) M d) :
    boundaryRestriction (fun x : M => ∑ i, omega i x) =
      (fun x => ∑ i, boundaryRestriction (omega i) x) := by
  funext x
  ext v
  simp only [boundaryRestriction, AlternatingMap.compLinearMap_apply, sum_apply]

/-- Generalized intrinsic Stokes in every bulk dimension at least two.
Localization uses finite ambient smooth weights near the original support,
and each local equality is proved from the interior or half-space formula. -/
theorem intrinsic_stokes_positive_boundary {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 (d+2) M)
    (omega : IntrinsicForm (k := d+2) M (d+1)) (homega : IntrinsicC1 omega)
    (hc : IsCompact (formSupport omega)) : IntrinsicStokesConclusion o omega := by
  classical
  obtain ⟨bO, hout⟩ := outwardFirst_exists o
  obtain ⟨P⟩ := D04.ManifoldIntegral.signed_partition_exists o (formSupport omega) hc
  let alpha : Fin P.count → IntrinsicForm (k := d+2) M (d+1) :=
    fun i x => P.weight i x • omega x
  have ha (i : Fin P.count) : IntrinsicC1 (alpha i) :=
    intrinsicC1_weight omega homega (P.weight i) ((P.partition.1 i).of_le (by norm_num))
  have hka (i : Fin P.count) : IsCompact (formSupport (alpha i)) :=
    (P.partition.2.2.1 i).1.of_isClosed_subset isClosed_closure
      (formSupport_weight_subset omega (P.weight i))
  have hsa (i : Fin P.count) : formSupport (alpha i) ⊆
      Subtype.val ⁻¹' (P.chart i).ambient :=
    (formSupport_weight_subset omega (P.weight i)).trans (P.partition.2.2.1 i).2
  have hex (i : Fin P.count) : ∃ I J : ℝ,
      HasPositiveIntegral o (intrinsicExteriorDerivative (alpha i)) I ∧
        HasPositiveIntegral bO (boundaryRestriction (alpha i)) J := by
    obtain ⟨I, hI⟩ := intrinsic_bulk_integral_exists o (alpha i) (ha i) (hka i)
    have hbcont := intrinsic_top_continuous _
      (D04.Intrinsic.intrinsicC1_continuous _ (boundaryRestriction_C1 o.manifold (alpha i) (ha i)))
    obtain ⟨J, hJ⟩ := positive_integral_exists bO _ hbcont
      (boundaryRestriction_support_compact o.manifold (alpha i) (hka i))
    exact ⟨I, J, hI, hJ⟩
  choose I J hI hJ using hex
  have hij (i : Fin P.count) : I i = J i := by
    cases hh : (P.chart i).half with
    | false =>
      exact intrinsic_single_chart_interior_positive o bO (P.chart i) hh
        (P.sign i) (P.agrees i) (alpha i) (ha i) (hka i) (hsa i) (hI i) (hJ i)
    | true =>
      exact intrinsic_single_chart_halfspace_positive o bO hout (P.chart i) hh
        (P.sign i) (P.agrees i) (alpha i) (ha i) (hka i) (hsa i) (hI i) (hJ i)
  have hbulk := positive_integral_sum o (fun i => intrinsicExteriorDerivative (alpha i))
    I Finset.univ (fun i _ => hI i)
  have hboundary := positive_integral_sum bO (fun i => boundaryRestriction (alpha i))
    J Finset.univ (fun i _ => hJ i)
  have hdiff : (fun x : M => ∑ i, intrinsicExteriorDerivative (alpha i) x) =
      intrinsicExteriorDerivative omega :=
    intrinsic_partition_derivative o.manifold omega homega _ P.weight P.partition
  have hbfield : (∑ i, intrinsicExteriorDerivative (alpha i)) =
      (fun x : M => ∑ i, intrinsicExteriorDerivative (alpha i) x) := by
    funext x
    exact Finset.sum_apply x _ _
  rw [hbfield, hdiff] at hbulk
  have hrecon : (fun x : M => ∑ i, alpha i x) = omega :=
    partition_reconstruct omega _ P.weight P.partition
  have htrace : (fun x => ∑ i, boundaryRestriction (alpha i) x) = boundaryRestriction omega :=
    (boundaryRestriction_sum alpha).symm.trans (congrArg (fun a => boundaryRestriction a) hrecon)
  have htfield : (∑ i, boundaryRestriction (alpha i)) =
      (fun x => ∑ i, boundaryRestriction (alpha i) x) := by
    funext x
    exact Finset.sum_apply x _ _
  rw [htfield, htrace] at hboundary
  have hsums : (∑ i, I i) = ∑ i, J i := Finset.sum_congr rfl (fun i _ => hij i)
  refine ⟨bO, hout, ∑ i, I i, hbulk, ?_⟩
  change HasPositiveIntegral bO (boundaryRestriction omega) (∑ i, I i)
  rw [hsums]
  exact hboundary

/-- The outward-first sign of a boundary point agrees with the chart sign
of the canonical outward boundary orientation field. -/
theorem boundary_point_chart_sign {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r 1 M)
    (nu : intrinsicBoundary r 1 M → E n)
    (hnu : ∀ x : intrinsicBoundary r 1 M, IsOutwardUnitConormal r 0 M x (nu x))
    (s : ZeroManifoldOrientation (intrinsicBoundary r 1 M))
    (hs : ∀ x, ((s x).val = 1 ↔ PositiveOutwardLine o x (nu x)) ∧
      ((s x).val = -1 ↔ ¬ PositiveOutwardLine o x (nu x)))
    (c : EmbeddedChart r 1 n M) (hh : c.half = true)
    (v : E 0) (hv : v ∈ (D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh).source) :
    (s (chartPoint (D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh)
      ⟨v, hv⟩)).val = -chartSign o.atPoint c (D04.flatInclusion 0 v) hv := by
  let b := D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh
  let x := chartPoint b ⟨v, hv⟩
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  let e := D04.Orientations.chartBasis b hbM.1 hbM.2.1 v hv
  have hsignpos : chartSign (D04BoundaryOrientation.boundaryOrientationField o nu hnu) b v hv = 1 ↔
      PositiveOutwardLine o x (nu x) := by
    have hc := D04.Orientations.chartSign_basis
      (D04BoundaryOrientation.boundaryOrientationField o nu hnu) b v hv e
      (fun i => Fin.elim0 i)
    have hp := D04BoundaryOrientation.boundaryOrientationField_positive o nu hnu x e
    apply hc.trans (hp.trans ?_)
    constructor
    · rintro ⟨B, hB, _, hO⟩
      exact ⟨B, hB, hO⟩
    · rintro ⟨B, hB, hO⟩
      exact ⟨B, hB, fun i => Fin.elim0 i, hO⟩
  have he : (s x).val = chartSign (D04BoundaryOrientation.boundaryOrientationField o nu hnu) b v hv := by
    rcases (s x).property with h | h
    · exact h.trans (hsignpos.mpr ((hs x).1.mp h)).symm
    · rcases D04.Orientations.chartSign_values
        (D04BoundaryOrientation.boundaryOrientationField o nu hnu) b hbM.1 hbM.2.1 v hv with hp | hp
      · have hpos := (hs x).1.mpr (hsignpos.mp hp)
        linarith
      · exact h.trans hp.symm
  have hb : chartSign (D04BoundaryOrientation.boundaryOrientationField o nu hnu) b v hv =
      chartSign o.atPoint c (D04.flatInclusion 0 v) hv * (-1 : ℝ)^1 :=
    D04BoundaryOrientation.boundary_chart_sign o nu hnu c hh v hv
  exact he.trans (hb.trans (by ring))

/-- A zero-dimensional chart contributes its single signed value, or zero
when the source is empty, in exactly the canonical coefficient integral. -/
theorem zero_integral_single_chart {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (s : ZeroManifoldOrientation M) (eta : TangentTopField r 0 M)
    (c : EmbeddedChart r 0 n M) (hs : topSupport eta ⊆ Subtype.val ⁻¹' c.ambient)
    (t : ℝ) (ht : ∀ u : c.source, (s (chartPoint c u)).val = t) :
    zeroIntegral s (fun x => eta x (fun j => Fin.elim0 j)) =
      t * coefficientIntegral (topCoefficient eta c) := by
  classical
  by_cases h0 : (0 : E 0) ∈ c.source
  · let p := chartPoint c ⟨0, h0⟩
    have hsupp : support (fun x => eta x (fun j => Fin.elim0 j)) ⊆ {p} := by
      intro x hx
      have hn : eta x ≠ 0 := by intro hz; exact hx (by simp [hz])
      have hxA := hs (subset_closure hn)
      have he := c.right_inv x ⟨x.property, hxA⟩
      rw [Subsingleton.elim (c.invFun x) 0] at he
      exact mem_singleton_iff.mpr (Subtype.ext he.symm)
    have hi := D04.ManifoldIntegralIndependence.zero_single_point s
      (fun x => eta x (fun j => Fin.elim0 j)) p hsupp
    have hv : coefficientIntegral (topCoefficient eta c) = eta p (fun j => Fin.elim0 j) := by
      have hz : coefficientIntegral (topCoefficient eta c) =
          D04.JordanRegions.zeroExtension (topCoefficient eta c) 0 :=
        D04.ManifoldIntegralIndependence.coefficientIntegral_zero_dimension _
      rw [hz, D04.JordanRegions.zeroExtension_apply _ ⟨0, h0⟩]
      change eta p (fun j => tangentChartMap c 0 h0 (standardBasis 0 j)) =
        eta p (fun j => Fin.elim0 j)
      apply congrArg (eta p)
      funext j
      exact Fin.elim0 j
    have htp : (s p).val = t := ht ⟨0, h0⟩
    rw [hi, hv, htp]
  · have he : eta = 0 := by
      funext x
      by_contra hn
      have hxA := hs (subset_closure hn)
      have hxS := c.map_target ⟨x.property, hxA⟩
      rw [Subsingleton.elim (c.invFun x) 0] at hxS
      exact h0 hxS
    rw [he]
    have hc0 : topCoefficient (0 : TangentTopField r 0 M) c =
        (fun _ : c.source => (0 : ℝ)) := rfl
    rw [hc0, (coefficientIntegral_zero c.source).2, mul_zero]
    change zeroIntegral s (fun _ => (0 : ℝ)) = 0
    simp [zeroIntegral]

/-- Stokes for a one-dimensional intrinsic form supported in one signed
chart, with the actual outward-first signed boundary point sum. -/
theorem intrinsic_single_chart_line {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 1 M)
    (s : ZeroManifoldOrientation (intrinsicBoundary 2 1 M)) (hout : OutwardFirst 0 o s)
    (c : EmbeddedChart 2 1 n M) (sigma : PointSign)
    (hsgn : ∀ u : c.source, chartSign o.atPoint c u u.property = sigma.val)
    (omega : IntrinsicForm (k := 1) M 0) (homega : IntrinsicC1 omega)
    (hc : IsCompact (formSupport omega))
    (hs : formSupport omega ⊆ Subtype.val ⁻¹' c.ambient)
    {I : ℝ} (hI : HasPositiveIntegral o (intrinsicExteriorDerivative omega) I) :
    I = zeroIntegral s (fun x => boundaryRestriction omega x (fun j => Fin.elim0 j)) := by
  obtain ⟨P⟩ := hI.2.2.1
  have hds : topSupport (intrinsicExteriorDerivative omega) ⊆ Subtype.val ⁻¹' c.ambient :=
    (intrinsic_derivative_support o.manifold omega homega).trans hs
  have hi : I = sigma.val * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) :=
    ((hI.2.2.2 P).2).symm.trans
      (D04.ManifoldIntegralIndependence.oriented_single_chart o _ hI.1 hI.2.1 P c hds sigma hsgn).2
  cases hh : c.half with
  | false =>
    rw [(intrinsic_chart_interior_stokes o.manifold c hh omega homega hc hs).2, mul_zero] at hi
    have hz := boundaryRestriction_eq_zero_of_interior_support o.manifold c hh omega hs
    rw [hz]
    simpa only [Pi.zero_apply, zero_apply, zeroIntegral, mul_zero, finsum_zero] using hi
  | true =>
    obtain ⟨nu, _, hnu, hsign⟩ := hout
    let b := D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh
    have hbt : ∀ v : b.source, (s (chartPoint b v)).val = -sigma.val := by
      intro v
      have he := boundary_point_chart_sign o nu hnu s hsign c hh v v.property
      have hsc : chartSign o.atPoint c (D04.flatInclusion 0 v) v.property = sigma.val :=
        hsgn ⟨D04.flatInclusion 0 v, v.property⟩
      exact he.trans (congrArg Neg.neg hsc)
    have hbs : topSupport (boundaryRestriction omega) ⊆ Subtype.val ⁻¹' b.ambient := by
      intro x hx
      exact hs (boundaryRestriction_support omega hx)
    have hj := zero_integral_single_chart s (boundaryRestriction omega) b hbs (-sigma.val) hbt
    have ht := (intrinsic_chart_halfspace_stokes o.manifold c hh omega homega hc hs).2.2 sigma.val
    have he : (fun v : b.source => chartPullback c omega (D04.flatInclusion 0 v)
        (fun j => standardBasis 1 j.castSucc)) =
        topCoefficient (boundaryRestriction omega) b := by
      funext v
      exact (boundaryChart_trace o.manifold c hh omega v v.property).symm
    change sigma.val * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) =
      (sigma.val * (-1 : ℝ)^1) * coefficientIntegral
        (fun v : b.source => chartPullback c omega (D04.flatInclusion 0 v)
          (fun j => standardBasis 1 j.castSucc)) at ht
    rw [he, pow_one, mul_neg_one] at ht
    exact hi.trans (ht.trans hj.symm)

/-- Intrinsic Stokes on oriented one-manifolds, including noncompact
manifolds with compactly supported forms and finite signed boundaries. -/
theorem intrinsic_stokes_line {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 1 M)
    (omega : IntrinsicForm (k := 1) M 0) (homega : IntrinsicC1 omega)
    (hc : IsCompact (formSupport omega)) : IntrinsicStokesConclusion o omega := by
  classical
  obtain ⟨s, hout⟩ := outwardFirst_exists o
  obtain ⟨P⟩ := D04.ManifoldIntegral.signed_partition_exists o (formSupport omega) hc
  let alpha : Fin P.count → IntrinsicForm (k := 1) M 0 := fun i x => P.weight i x • omega x
  have ha (i : Fin P.count) : IntrinsicC1 (alpha i) :=
    intrinsicC1_weight omega homega (P.weight i) ((P.partition.1 i).of_le (by norm_num))
  have hka (i : Fin P.count) : IsCompact (formSupport (alpha i)) :=
    (P.partition.2.2.1 i).1.of_isClosed_subset isClosed_closure
      (formSupport_weight_subset omega (P.weight i))
  have hsa (i : Fin P.count) : formSupport (alpha i) ⊆ Subtype.val ⁻¹' (P.chart i).ambient :=
    (formSupport_weight_subset omega (P.weight i)).trans (P.partition.2.2.1 i).2
  choose I hI using fun i => intrinsic_bulk_integral_exists o (alpha i) (ha i) (hka i)
  let f : intrinsicBoundary 2 1 M → ℝ := fun x => boundaryRestriction omega x (fun j => Fin.elim0 j)
  have hij (i : Fin P.count) : I i = zeroIntegral s (fun x => P.weight i x * f x) := by
    have hi := intrinsic_single_chart_line o s hout (P.chart i) (P.sign i) (P.agrees i)
      (alpha i) (ha i) (hka i) (hsa i) (hI i)
    have he : (fun x => boundaryRestriction (alpha i) x (fun j => Fin.elim0 j)) =
        (fun x : intrinsicBoundary 2 1 M => P.weight i x * f x) := by
      funext x
      rfl
    exact hi.trans (congrArg (zeroIntegral s) he)
  have hbulk := positive_integral_sum o (fun i => intrinsicExteriorDerivative (alpha i))
    I Finset.univ (fun i _ => hI i)
  have hbfield : (∑ i, intrinsicExteriorDerivative (alpha i)) =
      (fun x : M => ∑ i, intrinsicExteriorDerivative (alpha i) x) := by
    funext x
    exact Finset.sum_apply x _ _
  rw [hbfield, intrinsic_partition_derivative o.manifold omega homega _ P.weight P.partition] at hbulk
  have hkb := boundaryRestriction_support_compact o.manifold omega hc
  have hf : HasCompactSupport f := by
    apply hkb.of_isClosed_subset (isClosed_tsupport f)
    apply closure_mono
    intro x hx hz
    exact hx (by simp [f, hz])
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  have hsum : ∀ x : intrinsicBoundary 2 1 M, f x ≠ 0 → ∑ i, P.weight i x = 1 := by
    intro x hx
    obtain ⟨V, _, hV, hone⟩ := P.partition.2.2.2.1
    apply hone (⟨x, x.property.1⟩ : M)
    apply hV
    apply subset_closure
    intro hz
    exact hx (by simp [f, boundaryRestriction, hz])
  have hv := D04.ManifoldIntegralIndependence.zero_finite_localization hbM s f hf
    (fun i x => P.weight i x) hsum
  have heval : zeroIntegral s f = ∑ i, I i :=
    hv.trans (Finset.sum_congr rfl (fun i _ => (hij i).symm))
  refine ⟨s, hout, ∑ i, I i, hbulk, ?_⟩
  exact ⟨hbM, hkb, D04.ManifoldIntegral.zero_support_finite hbM f hf, heval⟩

/-- Generalized intrinsic Stokes in every positive bulk dimension. -/
theorem intrinsic_stokes : intrinsic_stokesType := by
  intro d n M o omega homega hc
  cases d with
  | zero => exact intrinsic_stokes_line o omega homega hc
  | succ d => exact intrinsic_stokes_positive_boundary o omega homega hc

/-- Integration over an empty manifold has value zero, including the signed
zero-dimensional definition. -/
theorem manifold_integral_eq_zero_of_empty {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : ManifoldOrientation r k M) (eta : TangentTopField r k M) {I : ℝ}
    (he : M = ∅) (hi : HasManifoldIntegral r k o eta I) : I = 0 := by
  subst M
  have hz : eta = 0 := by
    funext x
    exact False.elim x.property
  rw [hz] at hi
  cases k with
  | zero =>
    have hv := hi.2.2.2
    change zeroIntegral o (fun _ => (0 : ℝ)) = I at hv
    exact hv.symm.trans (by simp [zeroIntegral])
  | succ d => exact positive_integral_unique o 0 hi (positive_integral_zero o)

/-- Every C¹ intrinsic form of the relevant degree is admissible on a
compact oriented C² manifold. -/
theorem intrinsic_stokes_compact : intrinsic_stokes_compactType := by
  intro d n M o hc omega homega
  exact intrinsic_stokes o omega homega (formSupport_compact_of_compact hc omega)

/-- On a manifold with empty intrinsic boundary the integral of the
intrinsic exterior derivative is zero. -/
theorem intrinsic_stokes_boundaryless : intrinsic_stokes_boundarylessType := by
  intro d n M o omega homega hc he
  obtain ⟨bO, _, I, hI, hB⟩ := intrinsic_stokes o omega homega hc
  have hzero := manifold_integral_eq_zero_of_empty bO (boundaryRestriction omega) he hB
  rwa [hzero] at hI


/-! Affine value bridges for the C¹ ambient cell calculation. -/
open Specs.D04.C15.LocalStokesWithArtificialFaces.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C13.PullbackCalculus.Model

/-- Region and proper coefficient integrals agree whenever the region integral exists. -/
theorem regionIntegral_eq_coefficientIntegral {k : ℕ} {S : Set (E k)} {f : S → ℝ}
    (hf : D04.JordanRegions.RegionIntegrable f) :
    D04.JordanRegions.regionIntegral f = coefficientIntegral f := by
  obtain ⟨hb, Q, hQ, hi⟩ := hf
  have hs := D04.RegionSubstitution.support_zeroExtension_subset f
  have hsq : D04.JordanRegions.Encloses
      (support (D04.JordanRegions.zeroExtension f)) Q :=
    (closure_mono hs).trans hQ
  have hp : ProperIntegrable f :=
    ⟨(D04.JordanRegions.encloses_bounded hQ).subset hs, Q, hsq, hi⟩
  exact (D04.JordanRegions.integral_eq_on_enclosing_box f ⟨hb, Q, hQ, hi⟩ hQ hi).trans
    (D04.DirectedSubstitution.proper_on_box hp Q hsq).2.symm

/-- Continuous functions on compact rectangles have the actual region integral,
including the evaluation convention in dimension zero. -/
theorem regionIntegrable_box {k : ℕ} (Q : D04.Darboux.Box k) (f : E k → ℝ)
    (hf : ContinuousOn f (D04.Darboux.carrier Q)) :
    D04.JordanRegions.RegionIntegrable (fun x : D04.Darboux.carrier Q => f x) := by
  cases k with
  | zero => exact D04.JordanRegions.region_integrable_zero_dim _ _
  | succ k =>
    have hc := (D04.DiscontinuityCriterion.carrier_compact Q).isClosed.closure_eq
    have h := D04.JordanRegions.integrable_continuous_on_closure (Nat.succ_pos k)
      (D04.OneCoordinate.Boxes.jordan_carrier Q)
      (fun x => f x) ((hf.mono (by rw [hc])).domRestrict)
    simpa using h

/-- A continuous rectangle integral is the region integral on its closed carrier. -/
theorem box_integral_eq_region {k : ℕ} (Q : D04.Darboux.Box k)
    (hq : D04.Darboux.Nondegenerate Q) (f : E k → ℝ)
    (hf : ContinuousOn f (D04.Darboux.carrier Q)) :
    D04.Darboux.lowerIntegral f Q =
      D04.JordanRegions.regionIntegral (fun x : D04.Darboux.carrier Q => f x) := by
  have hi := regionIntegrable_box Q f hf
  let F : D04.Darboux.carrier Q → ℝ := fun x => f x
  obtain ⟨hb, R, hR, hiR⟩ := hi
  have hs := D04.RegionSubstitution.support_zeroExtension_subset F
  have hp : ProperIntegrable F :=
    ⟨(D04.JordanRegions.encloses_bounded hR).subset hs, R,
      (closure_mono hs).trans hR, hiR⟩
  obtain ⟨hiQ, hv⟩ := proper_on_closed_box hp Q hq hs
  have he : EqOn (D04.JordanRegions.zeroExtension F) f (D04.Darboux.carrier Q) :=
    fun x hx => D04.JordanRegions.zeroExtension_apply F ⟨x, hx⟩
  exact (D04.JordanRegions.lowerIntegral_congr he).symm.trans
    (hv.symm.trans (regionIntegral_eq_coefficientIntegral ⟨hb, R, hR, hiR⟩).symm)

/-- The positive affine rectangle map, with its explicit inverse on all of space. -/
def rectangleHomeomorph {k : ℕ} (Q : D04.Darboux.Box k)
    (hq : D04.Darboux.Nondegenerate Q) : E k ≃ₜ E k where
  toFun := rectangleMap Q
  invFun := fun y => WithLp.toLp 2 (fun i => (y i - Q.lower i) / (Q.upper i - Q.lower i))
  left_inv x := by
    apply PiLp.ext; intro i
    change (Q.lower i + (Q.upper i - Q.lower i) * x i - Q.lower i) /
      (Q.upper i - Q.lower i) = x i
    field_simp [ne_of_gt (sub_pos.mpr (hq i))]
    ring
  right_inv y := by
    apply PiLp.ext; intro i
    change Q.lower i + (Q.upper i - Q.lower i) *
      ((y i - Q.lower i) / (Q.upper i - Q.lower i)) = y i
    field_simp [ne_of_gt (sub_pos.mpr (hq i))]
    ring
  continuous_toFun := (rectangleMap_C1 Q).continuous
  continuous_invFun := by
    apply (coordinates k).symm.toContinuousLinearEquiv.continuous.comp
    apply continuous_pi
    intro i
    exact ((EuclideanSpace.proj i).continuous.sub continuous_const).div_const _

theorem rectangleHomeomorph_symm_C1 {k : ℕ} (Q : D04.Darboux.Box k)
    (hq : D04.Darboux.Nondegenerate Q) : ContDiff ℝ 1 (rectangleHomeomorph Q hq).symm := by
  apply (coordinates k).symm.toContinuousLinearEquiv.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  exact ((EuclideanSpace.proj i : E k →L[ℝ] ℝ).contDiff.sub contDiff_const).div_const _

theorem rectangleMap_det {k : ℕ} (Q : D04.Darboux.Box k) (x : E k) :
    (fderiv ℝ (rectangleMap Q) x).det = D04.Darboux.content Q := by
  have h := D04.Orientation.pullback_coefficient (rectangleMap Q) (fun _ => 1) x
  simp only [one_mul] at h
  rw [← h]
  rw [D04.pullback_apply, one_smul]
  change D04.volumeForm k (fun j => fderiv ℝ (rectangleMap Q) x (D04.standardBasis k j)) = _
  simp_rw [D04.LocalStokes.rectangleMap_derivative_basis]
  rw [AlternatingMap.map_smul_univ, D04.Orientation.volumeForm_basis, smul_eq_mul, mul_one]
  rfl

theorem rectangleMap_image_cube {k : ℕ} (Q : D04.Darboux.Box k)
    (hq : D04.Darboux.Nondegenerate Q) : rectangleMap Q '' cube k = D04.Darboux.carrier Q := by
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact rectangleMap_mem Q hx
  · intro y hy
    refine ⟨(rectangleHomeomorph Q hq).symm y, ?_, (rectangleHomeomorph Q hq).apply_symm_apply y⟩
    intro i
    change 0 ≤ (y i - Q.lower i) / (Q.upper i - Q.lower i) ∧
      (y i - Q.lower i) / (Q.upper i - Q.lower i) ≤ 1
    exact ⟨div_nonneg (sub_nonneg.mpr (hy i).1) (sub_pos.mpr (hq i)).le,
      (div_le_one (sub_pos.mpr (hq i))).mpr (sub_le_sub_right (hy i).2 _)⟩

/-- Scalar substitution by the positive affine map of a nondegenerate rectangle.
Both sides are the original closed-box Darboux integrals. -/
theorem rectangle_integral_substitution {k : ℕ} (Q : D04.Darboux.Box k)
    (hq : D04.Darboux.Nondegenerate Q) (f : E k → ℝ)
    (hf : ContinuousOn f (D04.Darboux.carrier Q)) :
    D04.Darboux.lowerIntegral
      (fun x => D04.Darboux.content Q * f (rectangleMap Q x)) (cubeBox k) =
        D04.Darboux.lowerIntegral f Q := by
  let e := (rectangleHomeomorph Q hq).toOpenPartialHomeomorph
  have he : (e : E k → E k) = rectangleMap Q := rfl
  have himage : e '' cube k = D04.Darboux.carrier Q := rectangleMap_image_cube Q hq
  have hfi := regionIntegrable_box Q f hf
  have hfi' : D04.JordanRegions.RegionIntegrable (fun y : e '' cube k => f y) := by
    change Specs.D04.C06.JordanRegions.Model.RegionIntegrable (S := e '' cube k) (fun y => f y)
    rw [himage]
    exact hfi
  have hsub := D04.RegionSubstitution.region_substitution e
    (rectangleMap_C1 Q).contDiffOn (rectangleHomeomorph_symm_C1 Q hq).contDiffOn
    (cube k) (D04.OneCoordinate.Boxes.jordan_carrier (cubeBox k))
    (by change IsCompact (closure (D04.Darboux.carrier (cubeBox k)))
        rw [(D04.DiscontinuityCriterion.carrier_compact (cubeBox k)).isClosed.closure_eq];
        exact D04.DiscontinuityCriterion.carrier_compact (cubeBox k))
    (subset_univ _) (fun y : e '' cube k => f y) hfi'.1
  have hv := hsub.2.2 (Or.inl hfi')
  have hdet (x : E k) : |(fderiv ℝ e x).det| = D04.Darboux.content Q := by
    rw [he, rectangleMap_det, abs_of_nonneg]
    exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (Q.ordered i))
  simp only [hdet, mul_comm (f _) (D04.Darboux.content Q)] at hv
  have hcont : ContinuousOn (fun x => D04.Darboux.content Q * f (rectangleMap Q x)) (cube k) :=
    continuousOn_const.mul (hf.comp (rectangleMap_C1 Q).continuous.continuousOn
      (fun _ hx => rectangleMap_mem Q hx))
  rw [box_integral_eq_region (cubeBox k) (fun i => by norm_num [cubeBox]) _ hcont,
    box_integral_eq_region Q hq f hf]
  change Specs.D04.C06.JordanRegions.Model.regionIntegral _ =
    Specs.D04.C06.JordanRegions.Model.regionIntegral _
  change Specs.D04.C06.JordanRegions.Model.regionIntegral _ =
    Specs.D04.C06.JordanRegions.Model.regionIntegral _ at hv
  rw [himage] at hv
  exact hv.symm

/-- A C¹ chart's cube cell integral is precisely its unscaled rectangle integral.
Only continuity of the ambient top form is needed. -/
theorem rectangle_cell_integral {k n : ℕ} (Q : D04.Darboux.Box k)
    (hq : D04.Darboux.Nondegenerate Q) (phi : E k → E n)
    (W : Set (E k)) (hW : IsOpen W) (hQ : D04.Darboux.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 0) V eta) (hmap : MapsTo phi (D04.Darboux.carrier Q) V) :
    cellIntegral (rectangleChartCell Q phi W hW hQ hphi) eta =
      D04.Darboux.lowerIntegral (fun u => pullback phi eta u (standardBasis k)) Q := by
  have hc : ContinuousOn (fun u => pullback phi eta u (standardBasis k))
      (D04.Darboux.carrier Q) :=
    D04.Cells.C1.pullback_evaluation_continuousOn eta heta (standardBasis k)
      (hphi.continuousOn.mono hQ)
      ((hphi.continuousOn_fderiv_of_isOpen hW le_rfl).mono hQ) hmap
  have he : D04.Darboux.lowerIntegral
      (cellCoefficient (rectangleChartCell Q phi W hW hQ hphi) eta) (cubeBox k) =
      D04.Darboux.lowerIntegral
        (fun x => D04.Darboux.content Q * pullback phi eta (rectangleMap Q x) (standardBasis k))
        (cubeBox k) := by
    exact D04.JordanRegions.lowerIntegral_congr (Q := cubeBox k)
      (f := cellCoefficient (rectangleChartCell Q phi W hW hQ hphi) eta)
      (g := fun x => D04.Darboux.content Q * pullback phi eta (rectangleMap Q x) (standardBasis k))
      (fun x hx => D04.LocalStokes.rectangle_bulk_coefficient Q phi W hW hQ hphi eta x hx)
  exact he.trans (rectangle_integral_substitution Q hq
    (fun u : E k => pullback phi eta u (standardBasis k)) hc)

/-- Differentiation along M does not enlarge the relative support of an
ambient scalar weight. No compactness of its ambient support is assumed. -/
theorem tangentRestriction_weighted_derivative_support {k n p : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 k M) (O : Set (E n)) (alpha : FormField n p)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w) :
    formSupport (tangentRestriction 1 k M (exteriorDerivative (fun y => w y • alpha y))) ⊆
      tsupport (fun x : M => w x) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxw
  have hwx : w x = 0 := image_eq_zero_of_notMem_tsupport (f := fun y : M => w y) hxw
  have hwcr : D04.CrOn 1 O w :=
    (D04.crOn_iff_contDiffOn 1 O w ha.1).mpr hw.contDiffOn
  have hdf : (exteriorDerivative (fun y => scalarCovector (V := E n) (w y)) x).compLinearMap
      (tangentSpace 1 k M x).subtype = 0 := by
    have he := D04.exteriorDerivative_function O w ha.1 hwcr x (hMO x.property)
    rw [show exteriorDerivative (fun y => scalarCovector (V := E n) (w y)) x =
      linearCovector (fderiv ℝ w x).toLinearMap from he]
    ext v
    change fderiv ℝ w x (v 0) = 0
    exact fderiv_tangent_eq_zero hM w x (hw.differentiable (by norm_num) x)
      (tsupport (fun y : M => w y))ᶜ (isClosed_tsupport _).isOpen_compl hxw 0
      (fun y hy => image_eq_zero_of_notMem_tsupport (f := fun z : M => w z) hy) (v 0)
  have hp : (D04.prependCovector
      (exteriorDerivative (fun y => scalarCovector (V := E n) (w y)) x) (alpha x)).compLinearMap
      (tangentSpace 1 k M x).subtype = 0 := by
    unfold D04.prependCovector
    rw [D04.Intrinsic.cast_compLinearMap, D04.Intrinsic.wedge_compLinearMap, hdf]
    change castCovector (Nat.add_comm 1 p)
      (wedge (0 : Covector (tangentSpace 1 k M x) 1) _) = 0
    rw [wedge_zero_left_general, castCovector_zero_general]
  apply hx
  ext v
  change D04.exteriorDerivative (fun y => w y • alpha y) x (fun j => (v j).val) = 0
  rw [D04.exteriorDerivative_function_smul O w alpha ha.1 hwcr ha x (hMO x.property)]
  change D04.prependCovector _ _ (fun j => (v j).val) +
    w x * exteriorDerivative alpha x (fun j => (v j).val) = 0
  have hpv := congrArg (fun A => A v) hp
  change D04.prependCovector _ _ (fun j => (v j).val) = 0 at hpv
  rw [hpv, hwx, zero_mul, zero_add]

/-- Compact relative support of a partition weight suffices for both localized
ambient integrals. Their equality remains a separate Stokes obligation. -/
theorem ambient_weighted_integrals_exist {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (O : Set (E n)) (alpha : FormField n d)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w)
    (hc : IsCompact (tsupport (fun x : M => w x))) :
    ∃ bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M),
      OutwardFirst d o bO ∧ ∃ I J : ℝ,
        HasPositiveIntegral o
          (tangentRestriction 1 (d+1) M (exteriorDerivative (fun y => w y • alpha y))) I ∧
        HasManifoldIntegral 1 d bO
          (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) (fun y => w y • alpha y)) J := by
  let beta : FormField n d := fun y => w y • alpha y
  have hb : IsCrForm (some 1) O beta := D04.isCrForm_function_smul 1 O w alpha ha.1
    ((D04.crOn_iff_contDiffOn 1 O w ha.1).mpr hw.contDiffOn) ha
  have hs : formSupport (tangentRestriction 1 (d+1) M beta) ⊆ tsupport (fun x : M => w x) := by
    have he : tangentRestriction 1 (d+1) M beta =
        (fun x : M => w x • tangentRestriction 1 (d+1) M alpha x) := by
      funext x; ext v; rfl
    rw [he]
    exact formSupport_weight_subset _ w
  have hdcomp : IsCompact (formSupport
      (tangentRestriction 1 (d+1) M (exteriorDerivative beta))) :=
    hc.of_isClosed_subset isClosed_closure
      (tangentRestriction_weighted_derivative_support o.manifold O alpha hMO ha w hw)
  obtain ⟨I, hI⟩ := positive_integral_exists o _
    (tangentRestriction_top_continuous o.manifold O _ hMO
      (D04.exteriorDerivative_continuous O beta hb)) (by rwa [formSupport_top] at hdcomp)
  obtain ⟨bO, hbO⟩ := outwardFirst_exists o
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  have hbc := tangentRestriction_top_continuous hbM O beta
    (fun _ hx => hMO hx.1) (D04.LocalStokes.form_C0 O beta hb)
  have hbs : IsCompact (topSupport (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) beta)) := by
    rw [← boundaryRestriction_ambient o.manifold beta]
    exact boundaryRestriction_support_compact o.manifold _
      (hc.of_isClosed_subset isClosed_closure hs)
  obtain ⟨J, hJ⟩ := manifold_integral_exists hbM bO _ hbc hbs
  exact ⟨bO, hbO, I, J, hI, hJ⟩

/-- Rescaling a face before or after inserting its endpoint gives the same point. -/
theorem rectangleMap_faceInsertion {k : ℕ} (Q : D04.Darboux.Box (k+1))
    (i : Fin (k+1)) (eps : Bool) (x : E k) :
    rectangleMap Q (faceInsertion i eps x) =
      rectangleFacePoint Q i eps (rectangleMap (rectangleFaceBox Q i) x) := by
  apply PiLp.ext
  intro j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · rw [D04.LocalStokes.rectangleFacePoint_same, D04.LocalStokes.rectangle_face_coordinate]
  · rw [D04.LocalStokes.rectangleFacePoint_other]
    change Q.lower (i.succAbove l) + (Q.upper (i.succAbove l) - Q.lower (i.succAbove l)) *
      faceInsertion i eps x (i.succAbove l) = _
    simp only [faceInsertion, Fin.insertNth_apply_succAbove]
    rfl

/-- Each rescaled face integral is the unscaled integral in the original
remaining coordinates; in dimension zero it is evaluation. -/
theorem rectangle_face_cell_integral {k n : ℕ} (Q : D04.Darboux.Box (k+1))
    (hq : D04.Darboux.Nondegenerate Q) (phi : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : D04.Darboux.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 0) V eta) (hmap : MapsTo phi (D04.Darboux.carrier Q) V)
    (i : Fin (k+1)) (eps : Bool) :
    cellIntegral (cellFace (rectangleChartCell Q phi W hW hQ hphi) i eps) eta =
      D04.Darboux.lowerIntegral
        (fun u => pullback phi eta (rectangleFacePoint Q i eps u)
          (fun j => standardBasis (k+1) (i.succAbove j))) (rectangleFaceBox Q i) := by
  have hc := D04.Cells.C1.pullback_evaluation_continuousOn eta heta
    (fun j => standardBasis (k+1) (i.succAbove j))
    (hphi.continuousOn.mono hQ)
    ((hphi.continuousOn_fderiv_of_isOpen hW le_rfl).mono hQ) hmap
  have hfc : ContinuousOn
      (fun u => pullback phi eta (rectangleFacePoint Q i eps u)
        (fun j => standardBasis (k+1) (i.succAbove j)))
      (D04.Darboux.carrier (rectangleFaceBox Q i)) :=
    hc.comp (D04.LocalStokes.rectangleFacePoint_continuous Q i eps).continuousOn
      (fun _ hx => D04.LocalStokes.rectangleFacePoint_mem Q i eps hx)
  change D04.Cells.cellIntegral (D04.Cells.cellFace
    (rectangleChartCell Q phi W hW hQ hphi) i eps) eta = _
  rw [D04.Cells.C1.face_integral_eq_evaluation]
  calc
    D04.Darboux.lowerIntegral _ (cubeBox k) = D04.Darboux.lowerIntegral
        (fun x => D04.Darboux.content (rectangleFaceBox Q i) *
          pullback phi eta (rectangleFacePoint Q i eps (rectangleMap (rectangleFaceBox Q i) x))
            (fun j => standardBasis (k+1) (i.succAbove j))) (cubeBox k) := by
      apply D04.JordanRegions.lowerIntegral_congr
      intro x hx
      have h := D04.LocalStokes.rectangle_face_coefficient Q phi W hW hQ hphi eta i eps x hx
      rw [rectangleMap_faceInsertion] at h
      exact h
    _ = _ := rectangle_integral_substitution (rectangleFaceBox Q i)
      (fun j => hq (i.succAbove j))
      (fun u => pullback phi eta (rectangleFacePoint Q i eps u)
        (fun j => standardBasis (k+1) (i.succAbove j))) hfc

/-- C¹ ambient Stokes on a rectangle in the actual unscaled coordinates.
The bulk integrand is the pullback of ambient d eta. -/
theorem ambient_rectangle_integral {k n : ℕ} (Q : D04.Darboux.Box (k+1))
    (hq : D04.Darboux.Nondegenerate Q) (phi : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : D04.Darboux.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 1) V eta) (hmap : MapsTo phi (D04.Darboux.carrier Q) V)
    (hs : support (pullback phi eta) ∩ D04.Darboux.carrier Q ⊆ halfBoxInterior Q)
    (sigma : ℝ) :
    sigma * D04.Darboux.lowerIntegral
      (fun u => pullback phi (exteriorDerivative eta) u (standardBasis (k+1))) Q =
    (sigma * (-1 : ℝ)^(k+1)) * D04.Darboux.lowerIntegral
      (fun u => pullback phi eta (rectangleFacePoint Q (Fin.last k) false u)
        (fun j => standardBasis (k+1) j.castSucc)) (rectangleFaceBox Q (Fin.last k)) := by
  have h := D04.LocalStokes.ambient_rectangle Q phi W hW hQ hphi V eta heta hmap hs sigma
  rw [rectangle_cell_integral Q hq phi W hW hQ hphi V _
    (D04.exteriorDerivative_continuous V eta heta) hmap,
    rectangle_face_cell_integral Q hq phi W hW hQ hphi V eta
      (D04.LocalStokes.form_C0 V eta heta) hmap] at h
  simpa only [Fin.succAbove_last] using h

/-- The interior C¹ ambient formula in the actual closed rectangle integral. -/
theorem ambient_interior_rectangle_integral {k n : ℕ} (Q : D04.Darboux.Box (k+1))
    (hq : D04.Darboux.Nondegenerate Q) (phi : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : D04.Darboux.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 1) V eta) (hmap : MapsTo phi (D04.Darboux.carrier Q) V)
    (hs : support (pullback phi eta) ∩ D04.Darboux.carrier Q ⊆ boxInterior Q) :
    D04.Darboux.lowerIntegral
      (fun u => pullback phi (exteriorDerivative eta) u (standardBasis (k+1))) Q = 0 := by
  have h := D04.LocalStokes.ambient_interior_rectangle Q phi W hW hQ hphi V eta heta hmap hs
  rwa [rectangle_cell_integral Q hq phi W hW hQ hphi V _
    (D04.exteriorDerivative_continuous V eta heta) hmap] at h

/-- A genuine local extension computes the actual tangent-restriction chart
coefficient, using its first derivative only. -/
theorem tangentRestriction_chart_extension {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (eta : FormField n k)
    (W : Set (E k)) (hW : IsOpen W) (g : E k → E n)
    (hg : ContDiffOn ℝ 1 g W) (he : EqOn g c.toFun (c.source ∩ W))
    (u : E k) (hu : u ∈ c.source) (huw : u ∈ W) :
    topCoefficient (tangentRestriction r k M eta) c ⟨u, hu⟩ =
      pullback g eta u (standardBasis k) := by
  have hd : chartDifferential c u = fderiv ℝ g u :=
    D04.EmbeddedChart.differential_extension c hu hW huw he
      ((hg.contDiffAt (hW.mem_nhds huw)).differentiableAt (by norm_num))
  change eta (c.toFun u) (fun j => chartDifferential c u (standardBasis k j)) =
    eta (g u) (fun j => fderiv ℝ g u (standardBasis k j))
  rw [hd, he ⟨hu, huw⟩]

/-- Geometric support control in inverse chart coordinates bounds the actual
ambient zero extension of the coefficient, retaining genuine boundary values. -/
theorem chart_coefficient_support_box {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (eta : TangentTopField r k M) (Q : D04.Darboux.Box k)
    (hs : ∀ x ∈ topSupport eta, c.invFun x ∈ D04.Darboux.carrier Q) :
    support (D04.JordanRegions.zeroExtension (topCoefficient eta c)) ⊆ D04.Darboux.carrier Q := by
  intro u hu
  change D04.JordanRegions.zeroExtension (topCoefficient eta c) u ≠ 0 at hu
  by_cases hum : u ∈ c.source
  · have hn : topCoefficient eta c ⟨u, hum⟩ ≠ 0 := by
      simpa only [D04.JordanRegions.zeroExtension_apply (topCoefficient eta c) ⟨u, hum⟩] using hu
    have h := hs (chartPoint c ⟨u, hum⟩)
      (D04.ManifoldIntegralIndependence.topCoefficient_support eta c ⟨u, hum⟩ hn)
    simpa only [chartPoint, c.left_inv u hum] using h
  · exact False.elim (hu (D04.JordanRegions.zeroExtension_of_not_mem _ hum))

/-- A chart-supported continuous tangent restriction has the same canonical
proper integral as its local extension's coefficient on a closed rectangle. -/
theorem ambient_chart_rectangle_coefficient {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (eta : FormField n k)
    (hcont : ContinuousTopField (tangentRestriction 1 k M eta))
    (hc : IsCompact (topSupport (tangentRestriction 1 k M eta)))
    (hs : topSupport (tangentRestriction 1 k M eta) ⊆ Subtype.val ⁻¹' c.ambient)
    (Q : D04.Darboux.Box k) (hq : D04.Darboux.Nondegenerate Q)
    (hqs : D04.Darboux.carrier Q ⊆ c.source)
    (hks : ∀ x ∈ topSupport (tangentRestriction 1 k M eta), c.invFun x ∈ D04.Darboux.carrier Q)
    (W : Set (E k)) (hW : IsOpen W) (hqw : D04.Darboux.carrier Q ⊆ W)
    (g : E k → E n) (hg : ContDiffOn ℝ 1 g W)
    (he : EqOn g c.toFun (c.source ∩ W)) :
    ProperIntegrable (topCoefficient (tangentRestriction 1 k M eta) c) ∧
      coefficientIntegral (topCoefficient (tangentRestriction 1 k M eta) c) =
        D04.Darboux.lowerIntegral (fun u => pullback g eta u (standardBasis k)) Q := by
  let beta := tangentRestriction 1 k M eta
  have hcomp := D04.ManifoldIntegralIndependence.chart_coefficient_compact
    (topCoefficient beta) c hc hs
    (D04.ManifoldIntegralIndependence.topCoefficient_support beta c)
  have hi := D04.DirectedSubstitution.parameter_integrable c.half c.source_open (hcont c) hcomp
  obtain ⟨hiQ, hv⟩ := proper_on_closed_box hi Q hq (chart_coefficient_support_box c beta Q hks)
  refine ⟨hi, hv.trans ?_⟩
  apply D04.JordanRegions.lowerIntegral_congr
  intro u hu
  rw [D04.JordanRegions.zeroExtension_apply (topCoefficient beta c) ⟨u, hqs hu⟩]
  exact tangentRestriction_chart_extension c eta W hW g hg he u (hqs hu) (hqw hu)

/-- Ambient restriction in the genuine boundary chart is the flat trace.
Only first chart derivatives occur, and degree zero is included. -/
theorem ambient_boundaryChart_trace {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (c : EmbeddedChart r (d+1) n M)
    (hh : c.half = true) (omega : FormField n d)
    (v : E d)
    (hv : v ∈ (D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh).source) :
    topCoefficient (tangentRestriction r d (intrinsicBoundary r (d+1) M) omega)
      (D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh) ⟨v, hv⟩ =
        omega (c.toFun (D04.flatInclusion d v))
          (fun j => chartDifferential c (D04.flatInclusion d v) (standardBasis (d+1) j.castSucc)) := by
  let b := D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh
  have he (j : Fin d) : chartDifferential b v (standardBasis d j) =
      chartDifferential c (D04.flatInclusion d v) (standardBasis (d+1) j.castSucc) := by
    have hd : chartDifferential b v =
        (chartDifferential c (D04.flatInclusion d v)).comp (D04.flatInclusion d) :=
      D04BoundaryOrientation.boundaryChart_differential c hM.1 hM.2.1 hh v hv
    rw [hd, ContinuousLinearMap.comp_apply, D04BoundaryOrientation.flatInclusion_basis]
  exact congrArg (omega (c.toFun (D04.flatInclusion d v))) (funext he)
/-- The genuine boundary chart integral is the unscaled lower-face integral.
This includes the zero-dimensional face, whose integral is evaluation. -/
theorem ambient_boundary_rectangle_coefficient {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 (d+1) M) (c : EmbeddedChart 1 (d+1) n M)
    (hh : c.half = true) (eta : FormField n d)
    (hcont : ContinuousTopField (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) eta))
    (hc : IsCompact (topSupport (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) eta)))
    (hs : topSupport (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) eta) ⊆
      Subtype.val ⁻¹' c.ambient)
    (Q : D04.Darboux.Box (d+1)) (hq : D04.Darboux.Nondegenerate Q)
    (hbottom : Q.lower (Fin.last d) = 0) (hqs : D04.Darboux.carrier Q ⊆ c.source)
    (hks : ∀ x ∈ topSupport (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) eta),
      c.invFun x ∈ D04.Darboux.carrier Q)
    (W : Set (E (d+1))) (hW : IsOpen W) (hqw : D04.Darboux.carrier Q ⊆ W)
    (g : E (d+1) → E n) (hg : ContDiffOn ℝ 1 g W)
    (he : EqOn g c.toFun (c.source ∩ W)) :
    let b := D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh
    ProperIntegrable (topCoefficient (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) eta) b) ∧
      coefficientIntegral (topCoefficient (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) eta) b) =
        D04.Darboux.lowerIntegral
          (fun u => pullback g eta (rectangleFacePoint Q (Fin.last d) false u)
            (fun j => standardBasis (d+1) j.castSucc)) (rectangleFaceBox Q (Fin.last d)) := by
  let b := D04.EmbeddedChart.boundaryChart c hM.1 hM.2.1 hh
  let beta := tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) eta
  let R := rectangleFaceBox Q (Fin.last d)
  have hbs : topSupport beta ⊆ Subtype.val ⁻¹' b.ambient := hs
  have hi := D04.DirectedSubstitution.parameter_integrable b.half b.source_open (hcont b)
    (D04.ManifoldIntegralIndependence.chart_coefficient_compact
      (topCoefficient beta) b hc hbs (D04.ManifoldIntegralIndependence.topCoefficient_support beta b))
  have hflat (u : E d) : rectangleFacePoint Q (Fin.last d) false u = D04.flatInclusion d u :=
    rectangle_lowerFace_eq_flatInclusion Q hbottom u
  have hRs (u : E d) (hu : u ∈ D04.Darboux.carrier R) : D04.flatInclusion d u ∈ c.source := by
    rw [← hflat]
    exact hqs (D04.LocalStokes.rectangleFacePoint_mem Q (Fin.last d) false hu)
  have hRw (u : E d) (hu : u ∈ D04.Darboux.carrier R) : D04.flatInclusion d u ∈ W := by
    rw [← hflat]
    exact hqw (D04.LocalStokes.rectangleFacePoint_mem Q (Fin.last d) false hu)
  have hbox : ∀ x ∈ topSupport beta, b.invFun x ∈ D04.Darboux.carrier R := by
    intro x hx j
    have ht := hks x hx (Fin.castSucc j)
    change Q.lower ((Fin.last d).succAbove j) ≤ c.invFun x j.castSucc ∧
      c.invFun x j.castSucc ≤ Q.upper ((Fin.last d).succAbove j)
    simpa only [Fin.succAbove_last] using (show _ ∧ _ from ht)
  obtain ⟨hiR, hv⟩ := proper_on_closed_box hi R
    (fun j => hq ((Fin.last d).succAbove j)) (chart_coefficient_support_box b beta R hbox)
  refine ⟨hi, hv.trans ?_⟩
  apply D04.JordanRegions.lowerIntegral_congr
  intro u hu
  have hus : u ∈ b.source := hRs u hu
  rw [D04.JordanRegions.zeroExtension_apply (topCoefficient beta b) ⟨u, hus⟩]
  rw [ambient_boundaryChart_trace hM c hh eta u hus]
  change eta (c.toFun _) _ = pullback g eta (rectangleFacePoint Q (Fin.last d) false u) _
  rw [hflat]
  have hd : chartDifferential c (D04.flatInclusion d u) = fderiv ℝ g (D04.flatInclusion d u) :=
    D04.EmbeddedChart.differential_extension c (hRs u hu) hW (hRw u hu) he
      ((hg.contDiffAt (hW.mem_nhds (hRw u hu))).differentiableAt (by norm_num))
  change eta (c.toFun _) (fun j => chartDifferential c _ (standardBasis (d+1) j.castSucc)) =
    eta (g _) (fun j => fderiv ℝ g _ (standardBasis (d+1) j.castSucc))
  rw [hd, he ⟨hRs u hu, hRw u hu⟩]

/-- Restrict local constancy while retaining the centered parameter witness.
A negative sign is allowed at one-dimensional boundary charts. -/
theorem constant_signed_centered_chart_at {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (x : M) :
    ∃ (c : EmbeddedChart r k n M) (s : PointSign) (u : E k),
      CenteredAt c u ∧ c.toFun u = x ∧
      ∀ v : c.source, chartSign o.atPoint c v v.property = s.val := by
  obtain ⟨c, u, hu, he⟩ := o.manifold.2.2 x x.property
  obtain ⟨U, hU, huU, hconst⟩ := (o.locally_constant c).exists_open ⟨u, hu.1⟩
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨a, hs, _, hf, _, hh⟩ := D04.embeddedChart_restrict_parameter c W hW
  have huW : u ∈ W := show (⟨u, hu.1⟩ : c.source) ∈ Subtype.val ⁻¹' W from hWU ▸ huU
  have hua : u ∈ a.source := hs ▸ ⟨hu.1, huW⟩
  refine ⟨a, ⟨chartSign o.atPoint c u hu.1,
    D04.Orientations.chartSign_values o.atPoint c o.manifold.1 o.manifold.2.1 u hu.1⟩,
    u, ⟨hua, fun h => hu.2 (hh ▸ h)⟩, hf ▸ he, ?_⟩
  intro v
  have hv : (v : E k) ∈ c.source ∩ W := hs ▸ v.property
  rw [D04.Orientations.restriction_sign o.atPoint c a o.manifold.1
    (by intro z hz; exact (hs ▸ hz).1) hf v v.property]
  exact hconst ⟨v, hv.1⟩ (hWU ▸ hv.2)

/-- Data chosen before the partition: a signed chart, an actual closed
rectangle, one genuine C¹ extension on that rectangle, and a relative open
neighborhood whose coordinates avoid every artificial face. -/
structure AmbientStokesChart {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) where
  chart : EmbeddedChart 1 (d+1) n M
  sign : PointSign
  agrees : ∀ u : chart.source, chartSign o.atPoint chart u u.property = sign.val
  box : D04.Darboux.Box (d+1)
  nondegenerate : D04.Darboux.Nondegenerate box
  source_box : D04.Darboux.carrier box ⊆ chart.source
  domain : Set (E (d+1))
  open_domain : IsOpen domain
  domain_box : D04.Darboux.carrier box ⊆ domain
  extension : E (d+1) → E n
  regular : ContDiffOn ℝ 1 extension domain
  agrees_extension : EqOn extension chart.toFun (chart.source ∩ domain)
  bottom : chart.half = true → box.lower (Fin.last d) = 0
  neighborhood : Set M
  open_neighborhood : IsOpen neighborhood
  in_chart : neighborhood ⊆ Subtype.val ⁻¹' chart.ambient
  coordinates : ∀ x ∈ neighborhood, chart.invFun x ∈
    if chart.half then halfBoxInterior box else boxInterior box

/-- Strict rectangle interiors are Euclidean open sets. -/
theorem boxInterior_isOpen {k : ℕ} (Q : D04.Darboux.Box k) : IsOpen (boxInterior Q) := by
  change IsOpen {x : E k | ∀ i, Q.lower i < x i ∧ x i < Q.upper i}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
    (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)

/-- Every point lies in a rectangle-refined signed chart neighborhood.
Only local C¹ extension of charts is used. -/
theorem ambientStokesChart_at {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (x : M) :
    ∃ R : AmbientStokesChart o, x ∈ R.neighborhood := by
  obtain ⟨c, s, u, hu, hux, hsign⟩ := constant_signed_centered_chart_at o x
  obtain ⟨U, hU, hsource⟩ := c.source_open
  obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu.1
  have huU : u ∈ U := (hsource ▸ hu.1).2
  cases hh : c.half with
  | false =>
    have hsource' : c.source = U := by simpa [parameterSpace, hh] using hsource
    obtain ⟨delta, hd, hQ, hsmall, hnest⟩ := D04.LocalStokes.interior_rectangles
      (U ∩ W) (hU.inter hW) u ⟨huU, huW⟩
    let Q := centeredBox u delta hd.le
    let V := boxInterior (centeredBox u (delta/2) (half_pos hd).le)
    obtain ⟨a, has, hac, hat, hai, hah⟩ := D04.embeddedChart_restrict_parameter c V
      (boxInterior_isOpen _)
    have hua : u ∈ a.source := has ▸ ⟨hu.1, hsmall⟩
    refine ⟨⟨c, s, hsign, Q, ?_, ?_, W, hW, ?_, g, hg, he, ?_,
      Subtype.val ⁻¹' a.ambient, a.ambient_open.preimage continuous_subtype_val,
      ?_, ?_⟩, ?_⟩
    · intro i; change u i - delta < u i + delta; linarith
    · intro v hv; rw [hsource']; exact (hQ hv).1
    · intro v hv; exact (hQ hv).2
    · simp [hh]
    · intro y hy; exact hac hy
    · intro y hy
      have hv : c.invFun y ∈ c.source ∩ V := by
        rw [← hai]
        exact has ▸ a.map_target ⟨y.property, hy⟩
      simp only [hh, Bool.false_eq_true, ↓reduceIte]
      apply hnest
      intro i
      exact ⟨(hv.2 i).1.le, (hv.2 i).2.le⟩
    · have hp := (a.map_source hua).2
      rwa [hat, hux] at hp
  | true =>
    have hu0 : u (Fin.last d) = 0 := hu.2 hh
    obtain ⟨delta, hd, hQ, _, _⟩ := D04.LocalStokes.boundary_rectangles
      (U ∩ W) (hU.inter hW) u ⟨huU, huW⟩ hu0
    let Q := halfCenteredBox u delta hd.le hu0
    let V := boxInterior (centeredBox u (delta/2) (half_pos hd).le)
    obtain ⟨a, has, hac, hat, hai, hah⟩ := D04.embeddedChart_restrict_parameter c V
      (boxInterior_isOpen _)
    have hsmall : u ∈ V := by intro i; exact ⟨by dsimp [V, centeredBox]; linarith,
      by dsimp [V, centeredBox]; linarith⟩
    have hua : u ∈ a.source := has ▸ ⟨hu.1, hsmall⟩
    refine ⟨⟨c, s, hsign, Q, ?_, ?_, W, hW, ?_, g, hg, he, ?_,
      Subtype.val ⁻¹' a.ambient, a.ambient_open.preimage continuous_subtype_val,
      ?_, ?_⟩, ?_⟩
    · intro i
      by_cases hi : i = Fin.last d
      · subst i; simp only [Q, halfCenteredBox, ite_true, hu0, zero_add]; exact hd
      · simp only [Q, halfCenteredBox, hi, ite_false]; linarith
    · intro v hv
      rw [hsource]
      exact ⟨by simpa [parameterSpace, hh] using (hQ hv).2, (hQ hv).1.1⟩
    · intro v hv; exact (hQ hv).1.2
    · intro _; simp [Q, halfCenteredBox]
    · intro y hy; exact hac hy
    · intro y hy
      have hv : c.invFun y ∈ c.source ∩ V := by
        rw [← hai]
        exact has ▸ a.map_target ⟨y.property, hy⟩
      simp only [hh, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have hi := hv.2 i.castSucc
        simp only [Q, halfCenteredBox, Fin.castSucc_ne_last, ite_false]
        change u i.castSucc - delta < c.invFun y i.castSucc ∧
          c.invFun y i.castSucc < u i.castSucc + delta
        dsimp [V, centeredBox] at hi
        constructor <;> linarith [hi.1, hi.2]
      · have ht := (hsource ▸ hv.1).1
        simpa [parameterSpace, hh, halfSpace, Q, halfCenteredBox] using ht
      · have hi := (hv.2 (Fin.last d)).2
        change c.invFun y (Fin.last d) < u (Fin.last d) + delta
        dsimp [V, centeredBox] at hi
        linarith
    · have hp := (a.map_source hua).2
      rwa [hat, hux] at hp

/-- Finite smooth ambient weights are chosen only after rectangle refinement. -/
theorem finite_ambient_stokes_partition {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (K : Set M) (hc : IsCompact K) :
    ∃ (m : ℕ) (R : Fin m → AmbientStokesChart o) (w : Fin m → E n → ℝ),
      PartitionNear M K (fun i => (R i).neighborhood) m id w := by
  choose R hR using fun x : K => ambientStokesChart_at o x.val
  obtain ⟨m, a, p, w, hw, hs⟩ := D04.FiniteCompactPartition.finite_partition_refined
    o.manifold K hc (fun _ : Unit => (univ : Set M)) (fun _ => isOpen_univ)
    (by intro x hx; exact mem_iUnion.mpr ⟨(), mem_univ x⟩)
    (fun x => (R x).chart) (fun x => (R x).in_chart (hR x))
    (fun x => (R x).neighborhood) (fun x => (R x).open_neighborhood) hR
  exact ⟨m, fun i => R (p i), w, hw.1, hw.2.1,
    fun i => ⟨(hw.2.2.1 i).1, fun x hx => (hs i hx).1⟩, hw.2.2.2⟩

/-- Restriction of a weighted ambient form has relative support in its weight. -/
theorem tangentRestriction_weight_support {r : ℕ∞ω} {k n p : ℕ} {M : Set (E n)}
    (alpha : FormField n p) (w : E n → ℝ) :
    formSupport (tangentRestriction r k M (fun y => w y • alpha y)) ⊆
      tsupport (fun x : M => w x) := by
  have he : tangentRestriction r k M (fun y => w y • alpha y) =
      (fun x : M => w x • tangentRestriction r k M alpha x) := by
    funext x; ext v; rfl
  rw [he]
  exact formSupport_weight_subset _ w

/-- The coefficient identity for a weighted ambient form in a boundary
rectangle; no derivative of its chart pullback is taken. -/
theorem ambient_weighted_chart_halfspace {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (R : AmbientStokesChart o)
    (hh : R.chart.half = true) (O : Set (E n)) (alpha : FormField n d)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w)
    (hc : IsCompact (tsupport (fun x : M => w x)))
    (hs : tsupport (fun x : M => w x) ⊆ R.neighborhood) :
    let beta := fun y => w y • alpha y
    let b := D04.EmbeddedChart.boundaryChart R.chart o.manifold.1 o.manifold.2.1 hh
    R.sign.val * coefficientIntegral
      (topCoefficient (tangentRestriction 1 (d+1) M (exteriorDerivative beta)) R.chart) =
    (R.sign.val * (-1 : ℝ)^(d+1)) * coefficientIntegral
      (topCoefficient (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) beta) b) := by
  let beta : FormField n d := fun y => w y • alpha y
  let A := tangentRestriction 1 (d+1) M beta
  let D := tangentRestriction 1 (d+1) M (exteriorDerivative beta)
  have hb : IsCrForm (some 1) O beta := D04.isCrForm_function_smul 1 O w alpha ha.1
    ((D04.crOn_iff_contDiffOn 1 O w ha.1).mpr hw.contDiffOn) ha
  have hDs : topSupport D ⊆ tsupport (fun x : M => w x) :=
    tangentRestriction_weighted_derivative_support o.manifold O alpha hMO ha w hw
  have hAs : formSupport A ⊆ tsupport (fun x : M => w x) :=
    tangentRestriction_weight_support alpha w
  have hcoord (x : M) (hx : x ∈ tsupport (fun y : M => w y)) :
      R.chart.invFun x ∈ D04.Darboux.carrier R.box := by
    have ht := R.coordinates x (hs hx)
    simp only [hh, ↓reduceIte] at ht
    exact halfBoxInterior_subset_carrier R.box ht
  have hbulk := ambient_chart_rectangle_coefficient R.chart (exteriorDerivative beta)
    (tangentRestriction_top_continuous o.manifold O _ hMO (D04.exteriorDerivative_continuous O beta hb))
    (hc.of_isClosed_subset isClosed_closure hDs) (hDs.trans (hs.trans R.in_chart))
    R.box R.nondegenerate R.source_box (fun x hx => hcoord x (hDs hx))
    R.domain R.open_domain R.domain_box R.extension R.regular R.agrees_extension
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  have hbcont := tangentRestriction_top_continuous hbM O beta (fun x hx => hMO hx.1)
    (D04.LocalStokes.form_C0 O beta hb)
  have hbs : topSupport (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) beta) ⊆
      (fun x : intrinsicBoundary 1 (d+1) M => (⟨x, x.property.1⟩ : M)) ⁻¹'
        tsupport (fun y : M => w y) := by
    rw [← boundaryRestriction_ambient o.manifold beta]
    exact (boundaryRestriction_support A).trans (preimage_mono hAs)
  have hbcomp : IsCompact (topSupport (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) beta)) := by
    rw [← boundaryRestriction_ambient o.manifold beta]
    exact boundaryRestriction_support_compact o.manifold A
      (hc.of_isClosed_subset isClosed_closure hAs)
  have hboundary := ambient_boundary_rectangle_coefficient o.manifold R.chart hh beta hbcont hbcomp
    (fun x hx => R.in_chart (hs (hbs hx))) R.box R.nondegenerate (R.bottom hh) R.source_box
    (fun x hx => hcoord ⟨x, x.property.1⟩ (hbs hx)) R.domain R.open_domain R.domain_box
    R.extension R.regular R.agrees_extension
  have hmap : MapsTo R.extension (D04.Darboux.carrier R.box) O := by
    intro u hu
    rw [R.agrees_extension ⟨R.source_box hu, R.domain_box hu⟩]
    exact hMO (R.chart.map_source (R.source_box hu)).1
  have hsupp : support (pullback R.extension beta) ∩ D04.Darboux.carrier R.box ⊆ halfBoxInterior R.box := by
    intro u hu
    let x : M := ⟨R.chart.toFun u, (R.chart.map_source (R.source_box hu.2)).1⟩
    have he : R.extension u = x := R.agrees_extension ⟨R.source_box hu.2, R.domain_box hu.2⟩
    have hn : w x ≠ 0 := by
      intro hz
      apply hu.1
      ext v
      change w (R.extension u) * alpha (R.extension u) _ = 0
      rw [he, hz, zero_mul]
    have ht := R.coordinates x (hs (subset_tsupport (fun y : M => w y) hn))
    simp only [hh, ↓reduceIte] at ht
    simpa only [x, R.chart.left_inv u (R.source_box hu.2)] using ht
  have hlocal := ambient_rectangle_integral R.box R.nondegenerate R.extension
    R.domain R.open_domain R.domain_box R.regular O beta hb hmap hsupp R.sign.val
  change R.sign.val * coefficientIntegral (topCoefficient D R.chart) = _
  rw [hbulk.2, hboundary.2]
  exact hlocal

/-- The corresponding weighted ambient coefficient vanishes after integration
in an interior rectangle. -/
theorem ambient_weighted_chart_interior {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (R : AmbientStokesChart o)
    (hh : R.chart.half = false) (O : Set (E n)) (alpha : FormField n d)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w)
    (hc : IsCompact (tsupport (fun x : M => w x)))
    (hs : tsupport (fun x : M => w x) ⊆ R.neighborhood) :
    coefficientIntegral (topCoefficient
      (tangentRestriction 1 (d+1) M (exteriorDerivative (fun y => w y • alpha y))) R.chart) = 0 := by
  let beta : FormField n d := fun y => w y • alpha y
  let D := tangentRestriction 1 (d+1) M (exteriorDerivative beta)
  have hb : IsCrForm (some 1) O beta := D04.isCrForm_function_smul 1 O w alpha ha.1
    ((D04.crOn_iff_contDiffOn 1 O w ha.1).mpr hw.contDiffOn) ha
  have hDs : topSupport D ⊆ tsupport (fun x : M => w x) :=
    tangentRestriction_weighted_derivative_support o.manifold O alpha hMO ha w hw
  have hcoord (x : M) (hx : x ∈ tsupport (fun y : M => w y)) :
      R.chart.invFun x ∈ D04.Darboux.carrier R.box := by
    have ht := R.coordinates x (hs hx)
    simp only [hh, Bool.false_eq_true, ↓reduceIte] at ht
    intro i; exact ⟨(ht i).1.le, (ht i).2.le⟩
  have hbulk := ambient_chart_rectangle_coefficient R.chart (exteriorDerivative beta)
    (tangentRestriction_top_continuous o.manifold O _ hMO (D04.exteriorDerivative_continuous O beta hb))
    (hc.of_isClosed_subset isClosed_closure hDs) (hDs.trans (hs.trans R.in_chart))
    R.box R.nondegenerate R.source_box (fun x hx => hcoord x (hDs hx))
    R.domain R.open_domain R.domain_box R.extension R.regular R.agrees_extension
  have hmap : MapsTo R.extension (D04.Darboux.carrier R.box) O := by
    intro u hu
    rw [R.agrees_extension ⟨R.source_box hu, R.domain_box hu⟩]
    exact hMO (R.chart.map_source (R.source_box hu)).1
  have hsupp : support (pullback R.extension beta) ∩ D04.Darboux.carrier R.box ⊆ boxInterior R.box := by
    intro u hu
    let x : M := ⟨R.chart.toFun u, (R.chart.map_source (R.source_box hu.2)).1⟩
    have he : R.extension u = x := R.agrees_extension ⟨R.source_box hu.2, R.domain_box hu.2⟩
    have hn : w x ≠ 0 := by
      intro hz
      apply hu.1
      ext v
      change w (R.extension u) * alpha (R.extension u) _ = 0
      rw [he, hz, zero_mul]
    have ht := R.coordinates x (hs (subset_tsupport (fun y : M => w y) hn))
    simp only [hh, Bool.false_eq_true, ↓reduceIte] at ht
    simpa only [x, R.chart.left_inv u (R.source_box hu.2)] using ht
  exact hbulk.2.trans (ambient_interior_rectangle_integral R.box R.nondegenerate R.extension
    R.domain R.open_domain R.domain_box R.regular O beta hb hmap hsupp)

/-- Uniqueness of integral values, also for independently signed points. -/
theorem manifold_integral_unique {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : ManifoldOrientation r k M) (eta : TangentTopField r k M)
    {I J : ℝ} (hi : HasManifoldIntegral r k o eta I)
    (hj : HasManifoldIntegral r k o eta J) : I = J := by
  cases k with
  | zero => exact hi.2.2.2.symm.trans hj.2.2.2
  | succ k => exact positive_integral_unique o eta hi hj

/-- The zero field has integral zero in every dimension. -/
theorem manifold_integral_zero {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (o : ManifoldOrientation r k M) :
    HasManifoldIntegral r k o (0 : TangentTopField r k M) 0 := by
  cases k with
  | zero =>
    refine ⟨hM, ?_, ?_, ?_⟩
    · have he : topSupport (0 : TangentTopField r 0 M) = ∅ := by
        simp [topSupport]
      rw [he]; exact isCompact_empty
    · exact finite_empty.subset (fun x hx => False.elim (hx rfl))
    · simp [zeroIntegral]
  | succ k => exact positive_integral_zero o

/-- Integral additivity includes the signed zero-dimensional definition. -/
theorem manifold_integral_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : ManifoldOrientation r k M) (eta xi : TangentTopField r k M)
    {I J : ℝ} (hi : HasManifoldIntegral r k o eta I)
    (hj : HasManifoldIntegral r k o xi J) :
    HasManifoldIntegral r k o (eta + xi) (I + J) := by
  cases k with
  | succ k => exact positive_integral_add o eta xi hi hj
  | zero =>
    have hk : IsCompact (topSupport (eta + xi)) :=
      (hi.2.1.union hj.2.1).of_isClosed_subset isClosed_closure
        (D04.ManifoldIntegralIndependence.topSupport_add_subset eta xi)
    let f : M → ℝ := fun x => eta x (fun j => Fin.elim0 j)
    let g : M → ℝ := fun x => xi x (fun j => Fin.elim0 j)
    have hf : HasCompactSupport f := hi.2.1.of_isClosed_subset (isClosed_tsupport f)
      (closure_mono (fun x hx hz => hx (by simp [f, hz])))
    have hg : HasCompactSupport g := hj.2.1.of_isClosed_subset (isClosed_tsupport g)
      (closure_mono (fun x hx hz => hx (by simp [g, hz])))
    have hsum : (fun x : M => (eta + xi) x (fun j => Fin.elim0 j)) = f + g := by
      funext x; rfl
    refine ⟨hi.1, hk, ?_, ?_⟩
    · rw [hsum]
      exact D04.ManifoldIntegral.zero_support_finite hi.1 (f+g) (hf.add hg)
    · rw [hsum, D04.ManifoldIntegralIndependence.zero_add hi.1 o f g hf hg]
      exact congrArg₂ (· + ·) hi.2.2.2 hj.2.2.2

/-- Finite linearity is valid for bulk and boundary integrals alike. -/
theorem manifold_integral_sum {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} {ι : Type*}
    (hM : IsEmbeddedManifold r k M) (o : ManifoldOrientation r k M)
    (eta : ι → TangentTopField r k M) (I : ι → ℝ) (s : Finset ι)
    (hi : ∀ i ∈ s, HasManifoldIntegral r k o (eta i) (I i)) :
    HasManifoldIntegral r k o (∑ i ∈ s, eta i) (∑ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using manifold_integral_zero hM o
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using manifold_integral_add o (eta a)
      (∑ i ∈ s, eta i) (hi a (Finset.mem_insert_self a s))
      (ih (fun i h => hi i (Finset.mem_insert_of_mem h)))

/-- The outward-first sign converts a half-space coefficient identity into
an identity of actual manifold integral values, in every positive bulk dimension. -/
theorem halfspace_integral_eq_of_coefficients {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M)
    (bO : ManifoldOrientation r d (intrinsicBoundary r (d+1) M))
    (hout : OutwardFirst d o bO) (c : EmbeddedChart r (d+1) n M)
    (hh : c.half = true) (s : PointSign)
    (hsgn : ∀ u : c.source, chartSign o.atPoint c u u.property = s.val)
    (A : TangentTopField r (d+1) M)
    (B : TangentTopField r d (intrinsicBoundary r (d+1) M))
    (hAs : topSupport A ⊆ Subtype.val ⁻¹' c.ambient)
    (hBs : topSupport B ⊆ Subtype.val ⁻¹' c.ambient)
    (hv : s.val * coefficientIntegral (topCoefficient A c) =
      (s.val * (-1 : ℝ)^(d+1)) * coefficientIntegral (topCoefficient B
        (D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh)))
    {I J : ℝ} (hI : HasPositiveIntegral o A I) (hJ : HasManifoldIntegral r d bO B J) : I = J := by
  obtain ⟨P⟩ := hI.2.2.1
  have hi : I = s.val * coefficientIntegral (topCoefficient A c) :=
    ((hI.2.2.2 P).2).symm.trans
      (D04.ManifoldIntegralIndependence.oriented_single_chart o A hI.1 hI.2.1 P c hAs s hsgn).2
  cases d with
  | zero =>
    obtain ⟨nu, _, hnu, hsign⟩ := hout
    let b := D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh
    have hbt : ∀ v : b.source, (bO (chartPoint b v)).val = -s.val := by
      intro v
      exact (boundary_point_chart_sign o nu hnu bO hsign c hh v v.property).trans
        (congrArg Neg.neg (hsgn ⟨D04.flatInclusion 0 v, v.property⟩))
    have hj := zero_integral_single_chart bO B b hBs (-s.val) hbt
    rw [pow_one, mul_neg_one] at hv
    exact hi.trans (hv.trans (hj.symm.trans hJ.2.2.2))
  | succ d =>
    obtain ⟨nu, _, hnu, hpos⟩ := hout
    obtain ⟨q, _, huniq⟩ := D04BoundaryOrientation.boundary_orientation o nu hnu
    have hbO : bO = D04BoundaryOrientation.inducedBoundaryOrientation o nu hnu :=
      (huniq bO hpos).trans (huniq _ (D04BoundaryOrientation.boundaryOrientationField_positive o nu hnu)).symm
    let b := D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hh
    let t : PointSign := ⟨s.val * (-1 : ℝ)^(d+2), by
      rcases s.property with h | h <;> rcases neg_one_pow_eq_or ℝ (d+2) with hp | hp <;>
        simp [h, hp]⟩
    have hbt : ∀ v : b.source, chartSign bO.atPoint b v v.property = t.val := by
      intro v
      have hb : bO.atPoint = D04BoundaryOrientation.boundaryOrientationField o nu hnu :=
        congrArg (fun q => q.atPoint) hbO
      rw [hb, D04BoundaryOrientation.boundary_chart_sign o nu hnu c hh v v.property,
        hsgn ⟨D04.flatInclusion (d+1) v, v.property⟩]
    obtain ⟨Q⟩ := hJ.2.2.1
    have hj : J = (s.val * (-1 : ℝ)^(d+2)) * coefficientIntegral (topCoefficient B b) :=
      ((hJ.2.2.2 Q).2).symm.trans
        (D04.ManifoldIntegralIndependence.oriented_single_chart bO B hJ.1 hJ.2.1 Q b hBs t hbt).2
    exact hi.trans (hv.trans hj.symm)

/-- The local ambient equality on an actual refined chart, including
signed point boundaries and interior charts. -/
theorem ambient_weighted_local_integrals {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M)
    (bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M))
    (hout : OutwardFirst d o bO) (R : AmbientStokesChart o)
    (O : Set (E n)) (alpha : FormField n d) (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w)
    (hc : IsCompact (tsupport (fun x : M => w x)))
    (hs : tsupport (fun x : M => w x) ⊆ R.neighborhood)
    {I J : ℝ}
    (hI : HasPositiveIntegral o
      (tangentRestriction 1 (d+1) M (exteriorDerivative (fun y => w y • alpha y))) I)
    (hJ : HasManifoldIntegral 1 d bO
      (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) (fun y => w y • alpha y)) J) : I = J := by
  let beta : FormField n d := fun y => w y • alpha y
  let A := tangentRestriction 1 (d+1) M beta
  let D := tangentRestriction 1 (d+1) M (exteriorDerivative beta)
  let B := tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) beta
  have hAs : formSupport A ⊆ Subtype.val ⁻¹' R.chart.ambient :=
    (tangentRestriction_weight_support alpha w).trans (hs.trans R.in_chart)
  have hDs : topSupport D ⊆ Subtype.val ⁻¹' R.chart.ambient :=
    (tangentRestriction_weighted_derivative_support o.manifold O alpha hMO ha w hw).trans
      (hs.trans R.in_chart)
  have hBs : topSupport B ⊆ Subtype.val ⁻¹' R.chart.ambient := by
    dsimp only [B]
    rw [← boundaryRestriction_ambient o.manifold beta]
    exact (boundaryRestriction_support A).trans (preimage_mono hAs)
  cases hh : R.chart.half with
  | true =>
    exact halfspace_integral_eq_of_coefficients o bO hout R.chart hh R.sign R.agrees D B hDs hBs
      (ambient_weighted_chart_halfspace o R hh O alpha hMO ha w hw hc hs) hI hJ
  | false =>
    obtain ⟨P⟩ := hI.2.2.1
    have hi : I = R.sign.val * coefficientIntegral (topCoefficient D R.chart) :=
      ((hI.2.2.2 P).2).symm.trans
        (D04.ManifoldIntegralIndependence.oriented_single_chart o D hI.1 hI.2.1 P
          R.chart hDs R.sign R.agrees).2
    rw [ambient_weighted_chart_interior o R hh O alpha hMO ha w hw hc hs, mul_zero] at hi
    have hBzero : B = 0 := by
      dsimp only [B]
      rw [← boundaryRestriction_ambient o.manifold beta]
      exact boundaryRestriction_eq_zero_of_interior_support o.manifold R.chart hh A hAs
    have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
    change HasManifoldIntegral 1 d bO B J at hJ
    rw [hBzero] at hJ
    exact hi.trans (manifold_integral_unique bO 0 (manifold_integral_zero hbM bO) hJ)

/-- Localized integrals can be taken in any fixed boundary orientation.
The compactness hypothesis is relative support of the scalar weight. -/
theorem ambient_weighted_integrals_fixed_orientation {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M)
    (bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M))
    (O : Set (E n)) (alpha : FormField n d) (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w)
    (hc : IsCompact (tsupport (fun x : M => w x))) :
    ∃ I J : ℝ,
      HasPositiveIntegral o
        (tangentRestriction 1 (d+1) M (exteriorDerivative (fun y => w y • alpha y))) I ∧
      HasManifoldIntegral 1 d bO
        (boundaryRestriction (tangentRestriction 1 (d+1) M (fun y => w y • alpha y))) J := by
  obtain ⟨_, _, I, _, hi, _⟩ := ambient_weighted_integrals_exist o O alpha hMO ha w hw hc
  let beta : FormField n d := fun y => w y • alpha y
  have hb : IsCrForm (some 1) O beta := D04.isCrForm_function_smul 1 O w alpha ha.1
    ((D04.crOn_iff_contDiffOn 1 O w ha.1).mpr hw.contDiffOn) ha
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  have hbc := tangentRestriction_top_continuous hbM O beta (fun x hx => hMO hx.1)
    (D04.LocalStokes.form_C0 O beta hb)
  rw [← boundaryRestriction_ambient o.manifold beta] at hbc
  obtain ⟨J, hj⟩ := manifold_integral_exists hbM bO _ hbc
    (boundaryRestriction_support_compact o.manifold _
      (hc.of_isClosed_subset isClosed_closure (tangentRestriction_weight_support alpha w)))
  exact ⟨I, J, hi, hj⟩

/-- Full C¹ ambient Stokes. Localization uses finite ambient smooth weights
in preselected rectangles and the proved C¹ cell formula, without differentiating
a merely continuous chart pullback. -/
theorem ambient_stokes : ambient_stokesType := by
  intro d n M o O alpha hMO ha hc
  let K : Set M := Subtype.val ⁻¹' tsupport alpha
  have hK : IsCompact K := by
    have hpre : IsCompact (Subtype.val ⁻¹' (M ∩ tsupport alpha) : Set M) :=
      IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc
        (by simpa only [Subtype.range_coe] using (inter_subset_left : M ∩ tsupport alpha ⊆ M))
    convert hpre using 1
    ext x; exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩
  obtain ⟨m, R, w, hw⟩ := finite_ambient_stokes_partition o K hK
  obtain ⟨bO, hout⟩ := outwardFirst_exists o
  let A : Fin m → TangentForm 1 (d+1) M d :=
    fun i => tangentRestriction 1 (d+1) M (fun y => w i y • alpha y)
  let D : Fin m → TangentTopField 1 (d+1) M :=
    fun i => tangentRestriction 1 (d+1) M (exteriorDerivative (fun y => w i y • alpha y))
  let B : Fin m → TangentTopField 1 d (intrinsicBoundary 1 (d+1) M) :=
    fun i => boundaryRestriction (A i)
  have hex (i : Fin m) : ∃ I J : ℝ, HasPositiveIntegral o (D i) I ∧
      HasManifoldIntegral 1 d bO (B i) J :=
    ambient_weighted_integrals_fixed_orientation o bO O alpha hMO ha (w i)
      ((hw.1 i).of_le (by norm_num)) (hw.2.2.1 i).1
  choose I J hI hJ using hex
  have hij (i : Fin m) : I i = J i := by
    have hj : HasManifoldIntegral 1 d bO
        (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) (fun y => w i y • alpha y)) (J i) := by
      rw [← boundaryRestriction_ambient o.manifold]
      exact hJ i
    exact ambient_weighted_local_integrals o bO hout (R i) O alpha hMO ha (w i)
      ((hw.1 i).of_le (by norm_num)) (hw.2.2.1 i).1 (hw.2.2.1 i).2 (hI i) hj
  have hbulk := positive_integral_sum o D I Finset.univ (fun i _ => hI i)
  have hboundary := manifold_integral_sum
    (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
    bO B J Finset.univ (fun i _ => hJ i)
  have hbfield : (∑ i, D i) = (fun x : M => ∑ i, D i x) := by
    funext x; exact Finset.sum_apply x _ _
  rw [hbfield, show (fun x : M => ∑ i, D i x) =
      tangentRestriction 1 (d+1) M (exteriorDerivative alpha) from
        ambient_partition_derivative o.manifold O alpha hMO ha _ w hw] at hbulk
  have hrecon : (fun x : M => ∑ i, A i x) = tangentRestriction 1 (d+1) M alpha := by
    funext x
    have he (i : Fin m) : A i x = w i x • tangentRestriction 1 (d+1) M alpha x := by
      ext v; rfl
    simp_rw [he]
    rw [← Finset.sum_smul]
    by_cases hz : alpha x = 0
    · have hzero : tangentRestriction 1 (d+1) M alpha x = 0 := by simp [tangentRestriction, hz]
      simp [hzero]
    · obtain ⟨V, _, hKV, hone⟩ := hw.2.2.2.1
      rw [hone x (hKV (subset_tsupport alpha hz)), one_smul]
  have htrace : (fun x => ∑ i, B i x) =
      tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) alpha :=
    (boundaryRestriction_sum A).symm.trans
      ((congrArg (fun a => boundaryRestriction a) hrecon).trans
        (boundaryRestriction_ambient o.manifold alpha))
  have htfield : (∑ i, B i) = (fun x => ∑ i, B i x) := by
    funext x; exact Finset.sum_apply x _ _
  rw [htfield, htrace] at hboundary
  refine ⟨bO, hout, ∑ i, I i, hbulk, ?_⟩
  rw [Finset.sum_congr rfl (fun i _ => hij i)]
  exact hboundary

/-- Every ambient C¹ form on a neighborhood is admissible on compact M. -/
theorem ambient_stokes_compact : ambient_stokes_compactType := by
  intro d n M o hc O alpha hMO ha
  exact ambient_stokes o O alpha hMO ha (hc.inter_right (isClosed_tsupport alpha))

/-- The ambient derivative integrates to zero on an empty-boundary manifold. -/
theorem ambient_stokes_boundaryless : ambient_stokes_boundarylessType := by
  intro d n M o O alpha hMO ha hc he
  obtain ⟨bO, _, I, hI, hB⟩ := ambient_stokes o O alpha hMO ha hc
  have hz := manifold_integral_eq_zero_of_empty bO _ he hB
  rwa [hz] at hI

end D04Stokes
