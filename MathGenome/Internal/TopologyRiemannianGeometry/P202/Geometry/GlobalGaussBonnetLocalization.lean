import Mathlib.Tactic.Choose
import Mathlib.Data.Finset.Max
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LocalGaussBonnet
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RegionalBoundaryCycles
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PiecewiseCurves
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Connected.Clopen
import Mathlib.LinearAlgebra.BilinearForm.Hom
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.QuotientBundles
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RiemannianVolume
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LocalGaussBonnet
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.ClassicalBoundaryGeometry
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.MetricVolume
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleMetrics
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.EmbeddedComparison
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Tactic.FunProp
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceRegionConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurveCovariantDerivative
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceRegionsEuler
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.DoubleCover
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ChartRegionStokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceBoundaryGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ArrangementGraphGeometry
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Analytic and geometric localization for paper.tex 5093–5137. The canonical
objects live in the independent GlobalGaussBonnetLocalization Spec. This module
constructs genuine boundary presentations and ambient regional geometry,
proves curvature/area naturality and all regional local formulas, and localizes
the intrinsic area integral away from the null graph. Reusable metric,
connection, curve-germ, normal and presentation-comparison helpers retain
their canonical names for the subsequent finite gluing proofs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData (ModelChart)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
universe u

namespace P202.GlobalGaussBonnet
open P202.MetricData P202.ConnectionData P202.CurvatureData
  P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction

section Boundary
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- A surface with empty intrinsic boundary has the empty arc presentation. -/
def emptyBoundaryPresentation (g : RiemannianMetric S)
    (hBoundary : SmoothManifolds.BoundaryData.intrinsicBoundary S = ∅) :
    BoundaryPresentation g where
  count := 0
  arc := Fin.elim0
  injective := fun i => Fin.elim0 i
  disjoint := fun i => Fin.elim0 i
  covers := by simpa only [iUnion_of_empty] using hBoundary
  side := fun i => Fin.elim0 i

theorem boundaryPresentation_count_zero (g : RiemannianMetric S)
    (B : BoundaryPresentation g)
    (hBoundary : SmoothManifolds.BoundaryData.intrinsicBoundary S = ∅) : B.count = 0 := by
  by_contra hn
  let i : Fin B.count := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hx : (B.arc i).curve (B.arc i).left ∈
      SmoothManifolds.BoundaryData.intrinsicBoundary S := by
    rw [B.covers]
    exact mem_iUnion.mpr ⟨i, (B.arc i).left,
      ⟨le_rfl, (B.arc i).ordered.le⟩, rfl⟩
  rw [hBoundary] at hx
  exact hx

/-- The boundary term vanishes for every allowed presentation of a closed
surface, rather than just for the empty presentation chosen above. -/
theorem boundaryCurvatureIntegral_eq_zero (g : RiemannianMetric S)
    (B : BoundaryPresentation g) (C : Connection (tangentBundle S))
    (hBoundary : SmoothManifolds.BoundaryData.intrinsicBoundary S = ∅) :
    B.curvatureIntegral C = 0 := by
  have hc := boundaryPresentation_count_zero g B hBoundary
  haveI : IsEmpty (Fin B.count) := by rw [hc]; infer_instance
  simp [BoundaryPresentation.curvatureIntegral]

/-- Negating the defining conormal negates the actual normalized metric dual. -/
theorem normalVector_neg (g : RiemannianMetric S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) :
    normalVector g p (-ℓ) = -normalVector g p ℓ := by
  simp only [normalVector, map_neg, P202.Geometry.SmoothMetrics.tangentNorm_neg, smul_neg]

/-- The curvature pairing changes sign with the normal, without any
orientation of the surface or any choice of tangent direction. -/
theorem inwardCurvature_neg_normal (g : RiemannianMetric S) (p : M)
    (A N : TangentSpace S p) :
    inwardCurvature g p A (-N) = -inwardCurvature g p A N := by
  exact LinearMap.BilinForm.neg_right _ _

theorem inwardCurveCurvature_neg_normal
    (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (c : ℝ → M) (T N : (t : ℝ) → TangentSpace S (c t))
    (speed : ℝ → ℝ) (t : ℝ) :
    inwardCurveCurvature C g c T (fun s => -N s) speed t =
      -inwardCurveCurvature C g c T N speed t :=
  inwardCurvature_neg_normal g _ _ _

/-- The two edge contributions cancel when the region normals are opposite,
even though the positively traversed parametrizations run in opposite
directions. Reversal of the actual velocity uses the proved covariant chain
rule, rather than an assumed invariance of D_T T. -/
theorem reversed_opposite_normal_cancel
    (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t))
    (s : ℝ) (hs : -s ∈ Ioo c.left c.right) :
    inwardCurveCurvature C g (c.curve ∘ Neg.neg)
      (unitTangent g (c.curve ∘ Neg.neg) (fun t => -c.velocity (-t)))
      (fun t => -N (-t))
      (fun t => tangentNorm g (c.curve (-t)) (-c.velocity (-t))) s +
      boundaryGeodesicCurvature C g hC c N (-s) = 0 := by
  rw [inwardCurveCurvature_neg_normal]
  rw [(P202.Geometry.SurfaceBoundaryGeometry.regularArc_curvature_reversal
    C g hC c N s hs).2]
  exact neg_add_cancel _

/-- Multiplying by unsigned speed preserves the pointwise cancellation. -/
theorem reversed_opposite_normal_integrand_cancel
    (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t))
    (s : ℝ) (hs : -s ∈ Ioo c.left c.right) :
    inwardCurveCurvature C g (c.curve ∘ Neg.neg)
      (unitTangent g (c.curve ∘ Neg.neg) (fun t => -c.velocity (-t)))
      (fun t => -N (-t))
      (fun t => tangentNorm g (c.curve (-t)) (-c.velocity (-t))) s *
        tangentNorm g (c.curve (-s)) (-c.velocity (-s)) +
      boundaryGeodesicCurvature C g hC c N (-s) * c.speed (-s) = 0 := by
  rw [P202.Geometry.SmoothMetrics.tangentNorm_neg]
  change _ * c.speed (-s) + _ * c.speed (-s) = 0
  rw [← add_mul, reversed_opposite_normal_cancel C g hC c N s hs, zero_mul]

end Boundary

section Area
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The original area measure exists uniquely without orientability. -/
theorem exists_unique_areaMeasure (g : RiemannianMetric S) :
    ∃! μ : @Measure M (borel M), IsAreaMeasure g μ :=
  P202.Geometry.RiemannianVolume.measure_representation_exists g

/-- The generic-model curvature agrees literally with the frozen local
curvature when the surface has Euclidean model. -/
theorem gaussianCurvature_eq_local {X : Type u} [TopologicalSpace X]
    {W : SmoothManifold 2 .euclidean X}
    (g : RiemannianMetric W) (T : CurvatureTensor W) :
    gaussianCurvature g T = P202Specs.LocalGaussBonnet.gaussianCurvature g T := rfl

/-- Every differentiable planar arc has zero planar area, with no global
injectivity assumption. This is the local measure-theoretic input to graph
nullity, and applies to arbitrary parameter subsets. -/
theorem plane_curve_image_null {f : ℝ → P202Specs.PlanarRegionTopology.Plane}
    {A : Set ℝ} (hf : DifferentiableOn ℝ f A) : volume (f '' A) = 0 := by
  have hA : (Measure.hausdorffMeasure 2 : Measure ℝ) A = 0 := by
    rw [Real.hausdorffMeasure_of_finrank_lt (by norm_num :
      (Module.finrank ℝ ℝ : ℝ) < 2)]
    simp
  have hIm := hf.hausdorffMeasure_image_eq_zero (by norm_num : (0 : ℝ) ≤ 2) hA
  have hAC : (volume : Measure P202Specs.PlanarRegionTopology.Plane) ≪
      Measure.hausdorffMeasure 2 := by
    have h := Measure.absolutelyContinuous_isAddHaarMeasure
      (volume : Measure P202Specs.PlanarRegionTopology.Plane)
      (Measure.hausdorffMeasure (Module.finrank ℝ P202Specs.PlanarRegionTopology.Plane))
    simpa [P202Specs.PlanarRegionTopology.Plane] using h
  exact hAC hIm

/-- The same null-image result in the ambient coordinate space used by the
canonical density measure, including for half-space-model charts. -/
theorem coordinate_curve_image_null
    {f : ℝ → SmoothManifolds.ModelData.Euclidean 2} {A : Set ℝ}
    (hf : DifferentiableOn ℝ f A) : volume (f '' A) = 0 := by
  have hA : (Measure.hausdorffMeasure 2 : Measure ℝ) A = 0 := by
    rw [Real.hausdorffMeasure_of_finrank_lt (by norm_num :
      (Module.finrank ℝ ℝ : ℝ) < 2)]
    simp
  have hIm := hf.hausdorffMeasure_image_eq_zero (by norm_num : (0 : ℝ) ≤ 2) hA
  have hAC : (volume : Measure (SmoothManifolds.ModelData.Euclidean 2)) ≪
      Measure.hausdorffMeasure 2 := by
    have h := Measure.absolutelyContinuous_isAddHaarMeasure
      (volume : Measure (SmoothManifolds.ModelData.Euclidean 2))
      (Measure.hausdorffMeasure
        (Module.finrank ℝ (SmoothManifolds.ModelData.Euclidean 2)))
    simpa [SmoothManifolds.ModelData.Euclidean] using h
  exact hAC hIm

/-- Every area measure characterized by the intrinsic density integral has
the upstream measurable chart formula. Uniqueness identifies the actual
measure; choosing a different measure cannot change the localization. -/
theorem areaMeasure_lintegral_chart
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (c : ModelChart 2 kind M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ≥0∞) (hf : @Measurable M ℝ≥0∞ (borel M) _ f)
    (hs : Function.support f ⊆ c.source) :
    (letI : MeasurableSpace M := borel M; ∫⁻ p, f p ∂μ) =
      ∫⁻ x, P202.VolumeData.chartLIntegrand g f
        (tangentStructure S).fiberCoordinates c hc x := by
  letI : MeasurableSpace M := borel M
  obtain ⟨ν, hνr, hνc, hνi, hν⟩ :=
    P202.Geometry.RiemannianVolume.measure_chart_exists g
  have heq : ν = μ := (exists_unique_areaMeasure g).unique
    ⟨hνr, hνc, hνi⟩ hμ
  subst ν
  exact (hν (tangentStructure S).fiberCoordinates c hc).1 f hf hs

/-- Real-valued chart localization for the same, uniquely characterized
intrinsic area measure. -/
theorem areaMeasure_integral_chart
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (c : ModelChart 2 kind M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) (hf : letI : MeasurableSpace M := borel M; Integrable f μ)
    (hs : Function.support f ⊆ c.source) :
    (letI : MeasurableSpace M := borel M; ∫ p, f p ∂μ) =
      ∫ x, P202.VolumeData.chartIntegrand g f
        (tangentStructure S).fiberCoordinates c hc x := by
  letI : MeasurableSpace M := borel M
  obtain ⟨ν, hνr, hνc, hνi, hν⟩ :=
    P202.Geometry.RiemannianVolume.measure_chart_exists g
  have heq : ν = μ := (exists_unique_areaMeasure g).unique
    ⟨hνr, hνc, hνi⟩ hμ
  subst ν
  exact (hν (tangentStructure S).fiberCoordinates c hc).2 f hf hs

/-- A measurable set in a chart whose ambient coordinate image is Lebesgue
null is null for the canonical area measure. No orientability is required. -/
theorem areaMeasure_null_of_chart_image_null
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (c : ModelChart 2 kind M) (hc : c ∈ S.smoothStructure.val)
    (A : Set M) (hA : @MeasurableSet M (borel M) A) (hAc : A ⊆ c.source)
    (hnull : (volume : Measure (SmoothManifolds.ModelData.Euclidean 2))
      ((fun p => (c p).val) '' A) = 0) : μ A = 0 := by
  letI : MeasurableSpace M := borel M
  let f : M → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hs : Function.support f ⊆ c.source :=
    support_indicator_subset.trans hAc
  have hchart := areaMeasure_lintegral_chart g μ hμ c hc f hf hs
  have hzero : ∀ᵐ x : SmoothManifolds.ModelData.Euclidean 2,
      x ∉ ((fun p => (c p).val) '' A) := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hnull
  have hz : (∫⁻ x, P202.VolumeData.chartLIntegrand g f
      (tangentStructure S).fiberCoordinates c hc x) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hzero] with x hx
    unfold P202.VolumeData.chartLIntegrand
    split
    · rename_i hm
      split
      · rename_i ht
        have hnot : c.symm ⟨x, hm⟩ ∉ A := by
          intro hp
          apply hx
          exact ⟨c.symm ⟨x, hm⟩, hp, congrArg Subtype.val (c.right_inv ht)⟩
        simp [f, hnot]
      · rfl
    · rfl
  have hl : (∫⁻ p, f p ∂μ) = μ A := lintegral_indicator_one hA
  exact hl.symm.trans (hchart.trans hz)

end Area

section GraphArea
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The coordinate image of the graph in a local star is contained in the
center and finitely many affine lines. This includes boundary half-stars and
stars with no rays. -/
theorem graphStar_coordinate_image_null {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) :
    (volume : Measure (SmoothManifolds.ModelData.Euclidean 2))
      ((fun q => (s.chart q).val) '' (G.carrier ∩ s.neighborhood)) = 0 := by
  let L : Fin s.rayCount → ℝ → SmoothManifolds.ModelData.Euclidean 2 :=
    fun i t => toPlane.symm (coordinates s.chart p + t • s.direction i)
  have hL (i : Fin s.rayCount) : volume (range (L i)) = 0 := by
    have hd : Differentiable ℝ (L i) := by
      dsimp [L]
      fun_prop
    simpa only [image_univ] using coordinate_curve_image_null (A := univ) hd.differentiableOn
  apply measure_mono_null (t := {(s.chart p).val} ∪ ⋃ i, range (L i))
  · rintro _ ⟨q, ⟨hqG, hqS, hqB⟩, rfl⟩
    obtain hqp | ⟨i, t, _, _, hqt⟩ := (s.graph_eq q hqS hqB).mp hqG
    · exact Or.inl (by simpa only [hqp, mem_singleton_iff])
    · apply Or.inr
      refine mem_iUnion.mpr ⟨i, t, ?_⟩
      apply toPlane.injective
      simpa only [L, ContinuousLinearEquiv.apply_symm_apply, coordinates] using hqt.symm
  · exact measure_union_null (measure_singleton _) (measure_iUnion_null hL)

/-- The actual intrinsic area of a local star's graph is zero. -/
theorem graphStar_area_null
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p) :
    μ (G.carrier ∩ s.neighborhood) = 0 := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact areaMeasure_null_of_chart_image_null g μ hμ s.chart s.chart_mem
    (G.carrier ∩ s.neighborhood)
    ((P202.SurfaceRegionConstruction.EmbeddedGraph.isClosed_carrier G).measurableSet.inter
      (P202.SurfaceRegionConstruction.GraphStar.isOpen_neighborhood s).measurableSet)
    (fun _ h => h.2.1) (graphStar_coordinate_image_null s)

/-- A finite graph with local graph stars has zero Riemannian area. Compactness
of the actual interval-edge carrier supplies a finite star cover; no
orientability, connectedness, or ambient compactness is needed. -/
theorem graph_area_null
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (G : EmbeddedGraph S) (hs : ∀ p ∈ G.carrier, Nonempty (GraphStar G p)) :
    μ G.carrier = 0 := by
  letI : MeasurableSpace M := borel M
  let s (p : G.carrier) : GraphStar G p.val := (hs p.val p.property).some
  obtain ⟨F, hF⟩ := (P202.SurfaceRegionConstruction.EmbeddedGraph.isCompact_carrier G).elim_finite_subcover
    (fun p : G.carrier => (s p).neighborhood)
    (fun p => P202.SurfaceRegionConstruction.GraphStar.isOpen_neighborhood (s p)) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩,
        P202.SurfaceRegionConstruction.GraphStar.mem_neighborhood (s ⟨p, hp⟩)⟩)
  apply measure_mono_null (t := ⋃ p ∈ F, G.carrier ∩ (s p).neighborhood)
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hF hp)
    exact mem_iUnion₂.mpr ⟨q, hq, hp, hpq⟩
  · exact (measure_biUnion_null_iff F.countable_toSet).mpr
      (fun p _ => graphStar_area_null g μ hμ (s p))

/-- The regional construction supplies the required stars at every graph
point, so its actual graph is area-null for the canonical measure. -/
theorem regionDecomposition_graph_area_null
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : RegionDecomposition S) : μ R.graph.carrier = 0 := by
  apply graph_area_null g μ hμ R.graph
  intro p hp
  obtain ⟨s, _⟩ := R.sectors p hp univ isOpen_univ (mem_univ p)
  exact ⟨s⟩

end GraphArea

/-- Finite measure localization away from a null graph. This lemma does not
assume integrability on the whole space: regional integrability suffices.
Geometry must supply the disjoint regions, cover, and graph-nullity premises. -/
theorem integral_eq_sum_off_null_set {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ι : Type*} [Fintype ι]
    (G : Set X) (D : ι → Set X) (f : X → ℝ)
    (hG : μ G = 0) (hcover : (⋃ i, D i) = Gᶜ)
    (hD : ∀ i, MeasurableSet (D i)) (hdisjoint : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hf : ∀ i, IntegrableOn f (D i) μ) :
    (∫ x, f x ∂μ) = ∑ i, ∫ x in D i, f x ∂μ := by
  have hmem : ∀ᵐ x ∂μ, x ∈ Gᶜ := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using hG
  rw [integral_eq_setIntegral hmem f, ← hcover]
  exact integral_iUnion_fintype hD hdisjoint hf

/-- Integrability, as well as the integral, can be recovered from finitely
many regions covering the complement of a null set. -/
theorem integrable_off_null_set {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ι : Type*} [Fintype ι]
    (G : Set X) (D : ι → Set X) (f : X → ℝ)
    (hG : μ G = 0) (hcover : (⋃ i, D i) = Gᶜ)
    (hf : ∀ i, IntegrableOn f (D i) μ) : Integrable f μ := by
  have hU : IntegrableOn f (⋃ i, D i) μ := integrableOn_finite_iUnion.mpr hf
  have hmem : ∀ᵐ x ∂μ, x ∈ Gᶜ := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using hG
  have heq : univ =ᵐ[μ] ⋃ i, D i := by
    rw [hcover]
    filter_upwards [hmem] with x hx
    exact propext ⟨fun _ => hx, fun _ => mem_univ _⟩
  exact integrableOn_univ.mp (hU.congr_set_ae heq)

section RegionalArea
open P202Specs.SurfaceRegionsEuler
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- In particular the genuine intrinsic boundary has zero area, since the
constructed graph contains it. -/
theorem intrinsicBoundary_area_null
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : RegionDecomposition S) :
    μ (SmoothManifolds.BoundaryData.intrinsicBoundary S) = 0 :=
  measure_mono_null R.contains_boundary (regionDecomposition_graph_area_null g μ hμ R)

/-- Each region and its actual closure agree almost everywhere. The only
added points lie on the null graph, including at the genuine boundary. -/
theorem regionInterior_ae_regionClosure
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : RegionDecomposition S) (j : Fin R.regionCount) :
    letI : MeasurableSpace M := borel M
    regionInterior R j =ᵐ[μ] regionClosure R j := by
  letI : MeasurableSpace M := borel M
  have hmem : ∀ᵐ x ∂μ, x ∉ R.graph.carrier := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using regionDecomposition_graph_area_null g μ hμ R
  filter_upwards [hmem] with x hx
  apply propext
  constructor
  · exact fun h => subset_closure h
  · intro h
    have hC := P202.SurfaceRegionConstruction.Components.closure_inter
      R.graph.carrierᶜ (R.component j)
    change x ∈ componentSet R.graph.carrierᶜ (R.component j)
    rw [← hC]
    exact ⟨h, hx⟩

/-- Intrinsic area localization for the actual region closures. Integrability
on those closures suffices; their overlapping boundaries carry zero area.
No Euler or Gauss–Bonnet identity is used in this analytic statement. -/
theorem regionDecomposition_integral
    (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : RegionDecomposition S) (f : M → ℝ)
    (hf : letI : MeasurableSpace M := borel M
      ∀ j, IntegrableOn f (regionClosure R j) μ) :
    letI : MeasurableSpace M := borel M
    Integrable f μ ∧ (∫ p, f p ∂μ) = ∑ j, ∫ p in regionClosure R j, f p ∂μ := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have hcover : (⋃ j, regionInterior R j) = R.graph.carrierᶜ := by
    exact (iUnion_congr_of_surjective R.component R.component.surjective (fun _ => rfl)).trans
      (P202.SurfaceRegionConstruction.Components.union_eq _)
  have hdisjoint : Pairwise (fun i j => Disjoint (regionInterior R i) (regionInterior R j)) := by
    intro i j hij
    exact P202.SurfaceRegionConstruction.Components.disjoint _ _ _
      (fun h => hij (R.component.injective h))
  have hf' : ∀ j, IntegrableOn f (regionInterior R j) μ :=
    fun j => (hf j).mono_set subset_closure
  have hnull := regionDecomposition_graph_area_null g μ hμ R
  refine ⟨integrable_off_null_set R.graph.carrier (regionInterior R) f hnull hcover hf', ?_⟩
  rw [integral_eq_sum_off_null_set R.graph.carrier (regionInterior R) f
    hnull hcover (fun j => (R.open_components j).measurableSet) hdisjoint hf']
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.restrict_congr_set (regionInterior_ae_regionClosure g μ hμ R j)]

end RegionalArea

section LocalAreaBridge
open P202Specs.PlanarRegionTopology
variable {X : Type u} [TopologicalSpace X] {W : SmoothManifold 2 .euclidean X}

/-- The inverse coordinate point lies in a chart subset exactly when its
plane coordinate belongs to that subset's actual coordinate image. -/
theorem chartPoint_mem_iff (c : ModelChart 2 .euclidean X)
    (A : Set X) (hAc : A ⊆ c.source) (x : Plane)
    (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    P202Specs.LocalGaussBonnet.chartPoint c x ∈ A ↔ x ∈ coordinates c '' A := by
  have hpoint : coordinates c (P202Specs.LocalGaussBonnet.chartPoint c x) = x := by
    unfold coordinates P202Specs.LocalGaussBonnet.chartPoint
    rw [c.right_inv hx]
    simp [P202Specs.ChartRegionStokes.modelPoint, toPlane]
  constructor
  · intro hp
    exact ⟨_, hp, hpoint⟩
  · rintro ⟨p, hp, hpx⟩
    have heq : c p = P202Specs.ChartRegionStokes.modelPoint x := by
      apply Subtype.ext
      apply toPlane.injective
      simpa [coordinates, P202Specs.ChartRegionStokes.modelPoint, toPlane] using hpx
    simpa only [P202Specs.LocalGaussBonnet.chartPoint, ← heq, c.left_inv (hAc hp)] using hp

/-- The zero extension of the intrinsic curvature over a chart subset is
literally the local curvature density restricted to its coordinate image.
The L2-plane conversion does not change coordinates or volume. -/
theorem chart_curvatureIntegrand_indicator
    (g : RiemannianMetric W) (T : CurvatureTensor W)
    (c : ModelChart 2 .euclidean X) (hc : c ∈ W.smoothStructure.val)
    (A : Set X) (hAc : A ⊆ c.source) (x : Plane) :
    P202.VolumeData.chartIntegrand g (A.indicator (gaussianCurvature g T))
      (tangentStructure W).fiberCoordinates c hc (EuclideanSpace.equiv (Fin 2) ℝ x) =
    (coordinates c '' A).indicator
      (P202Specs.LocalGaussBonnet.curvatureIntegrand g T c hc) x := by
  classical
  by_cases hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target
  · have hm := chartPoint_mem_iff c A hAc x hx
    by_cases hp : P202Specs.LocalGaussBonnet.chartPoint c x ∈ A
    · have hi := hm.mp hp
      simp [P202.VolumeData.chartIntegrand, SmoothManifolds.LocalIntegrationData.extendModel,
        SmoothManifolds.ModelData.modelSet, P202Specs.LocalGaussBonnet.curvatureIntegrand,
        P202Specs.LocalGaussBonnet.areaWeight, P202Specs.LocalGaussBonnet.chartPoint,
        P202Specs.ChartRegionStokes.modelPoint, gaussianCurvature_eq_local,
        P202Specs.LocalGaussBonnet.chartPoint] at hx hp ⊢
      simp_all [P202Specs.LocalGaussBonnet.curvatureIntegrand,
        P202Specs.LocalGaussBonnet.areaWeight, P202Specs.LocalGaussBonnet.chartPoint,
        P202Specs.ChartRegionStokes.modelPoint]
    · have hi : x ∉ coordinates c '' A := fun h => hp (hm.mpr h)
      simp [P202.VolumeData.chartIntegrand, SmoothManifolds.LocalIntegrationData.extendModel,
        SmoothManifolds.ModelData.modelSet, P202Specs.LocalGaussBonnet.curvatureIntegrand,
        P202Specs.LocalGaussBonnet.areaWeight, P202Specs.LocalGaussBonnet.chartPoint,
        P202Specs.ChartRegionStokes.modelPoint] at hx hp ⊢
      simp_all
  · have hi : x ∉ coordinates c '' A := by
      rintro ⟨p, hp, hpx⟩
      apply hx
      have heq : c p = P202Specs.ChartRegionStokes.modelPoint x := by
        apply Subtype.ext
        apply toPlane.injective
        simpa [coordinates, P202Specs.ChartRegionStokes.modelPoint, toPlane] using hpx
      exact heq ▸ c.map_source (hAc hp)
    simp [P202.VolumeData.chartIntegrand, SmoothManifolds.LocalIntegrationData.extendModel,
      SmoothManifolds.ModelData.modelSet, P202Specs.ChartRegionStokes.modelPoint] at hx ⊢
    simp_all

/-- The local theorem's chart curvature integral equals the intrinsic
curvature integral on the actual chart region. This is a measure and density
identity and requires no chosen orientation. -/
theorem local_curvatureIntegral_eq_intrinsic
    (g : RiemannianMetric W) (T : CurvatureTensor W)
    (μ : @Measure X (borel X)) (hμ : IsAreaMeasure g μ)
    (c : ModelChart 2 .euclidean X) (hc : c ∈ W.smoothStructure.val)
    (R : PlanarRegion) (A : Set X) (hA : @MeasurableSet X (borel X) A)
    (hAc : A ⊆ c.source) (hAR : coordinates c '' A = R.carrier)
    (hf : letI : MeasurableSpace X := borel X; IntegrableOn (gaussianCurvature g T) A μ) :
    (letI : MeasurableSpace X := borel X; ∫ p in A, gaussianCurvature g T p ∂μ) =
      P202Specs.LocalGaussBonnet.curvatureIntegral g T c hc R := by
  letI : MeasurableSpace X := borel X
  have hfi : Integrable (A.indicator (gaussianCurvature g T)) μ :=
    (integrable_indicator_iff hA).mpr hf
  rw [← integral_indicator hA, areaMeasure_integral_chart g μ hμ c hc _ hfi
    (support_indicator_subset.trans hAc)]
  rw [← (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.measurableEmbedding]
  have hfun : (fun x : Plane =>
      P202.VolumeData.chartIntegrand g (A.indicator (gaussianCurvature g T))
        (tangentStructure W).fiberCoordinates c hc (EuclideanSpace.equiv (Fin 2) ℝ x)) =
      R.carrier.indicator (P202Specs.LocalGaussBonnet.curvatureIntegrand g T c hc) := by
    funext x
    rw [chart_curvatureIntegrand_indicator g T c hc A hAc x, hAR]
  change (∫ x : Plane, P202.VolumeData.chartIntegrand g (A.indicator (gaussianCurvature g T))
    (tangentStructure W).fiberCoordinates c hc (EuclideanSpace.equiv (Fin 2) ℝ x)) = _
  rw [hfun]
  exact integral_indicator isClosed_closure.measurableSet

end LocalAreaBridge

/-- Integrating a reversed parametrization with opposite scalar curvature
cancels its original contribution. Equality is only needed on the open arc,
so values assigned to vertices and corners are irrelevant. -/
theorem reversed_interval_integral_cancel (l r : ℝ) (hlr : l ≤ r)
    (f g : ℝ → ℝ)
    (h : ∀ s ∈ Ioo (-r) (-l), f s + g (-s) = 0) :
    (∫ s in -r..-l, f s) + (∫ t in l..r, g t) = 0 := by
  have heq : (∫ s in -r..-l, f s) = ∫ s in -r..-l, -g (-s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro s hs
    exact eq_neg_of_add_eq_zero_left (h s hs)
  rw [heq, intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg]
  simp

section Incidence
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Each edge has an initial and a terminal half-edge, even when both
endpoints are the same vertex. -/
def halfEdgeVertex (G : EmbeddedGraph S) (h : Fin G.edgeCount × Bool) :
    Fin G.vertexCount :=
  if h.2 then G.terminal h.1 else G.initial h.1

def valence (G : EmbeddedGraph S) (v : Fin G.vertexCount) : ℕ :=
  ∑ h : Fin G.edgeCount × Bool, if halfEdgeVertex G h = v then 1 else 0

/-- The endpoint-incidence handshake identity. No prohibition on loops or
multiple edges is used. -/
theorem sum_valence (G : EmbeddedGraph S) :
    ∑ v : Fin G.vertexCount, valence G v = 2 * G.edgeCount := by
  simp only [valence]
  rw [Finset.sum_comm]
  simp [Nat.mul_comm]

theorem sum_valence_real (G : EmbeddedGraph S) :
    ∑ v : Fin G.vertexCount, (valence G v : ℝ) = 2 * (G.edgeCount : ℝ) := by
  exact_mod_cast sum_valence G

/-- Once the sectors at each vertex have exterior-angle sum π(d_v−2),
the global exterior-angle sum is exactly 2π(E−V). -/
theorem sum_vertex_exterior (G : EmbeddedGraph S)
    (ε : Fin G.vertexCount → ℝ)
    (hε : ∀ v, ε v = Real.pi * ((valence G v : ℝ) - 2)) :
    ∑ v, ε v = 2 * Real.pi * ((G.edgeCount : ℝ) - (G.vertexCount : ℝ)) := by
  simp_rw [hε, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_valence_real]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Incidence

/-- A full-plane vertex has one sector per incident half-edge. This is the
arithmetic consequence of its sector angles filling the full tangent plane. -/
theorem interior_sector_exterior_sum {d : ℕ} (α : Fin d → ℝ)
    (hα : ∑ i, α i = 2 * Real.pi) :
    ∑ i, (Real.pi - α i) = Real.pi * ((d : ℝ) - 2) := by
  rw [Finset.sum_sub_distrib, hα]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A smooth-boundary vertex has d−1 sectors filling a tangent half-plane.
The positivity premise only licenses subtraction in ℕ; it does not assert
anything about the angles. -/
theorem boundary_sector_exterior_sum {d : ℕ} (hd : 1 ≤ d)
    (α : Fin (d - 1) → ℝ) (hα : ∑ i, α i = Real.pi) :
    ∑ i, (Real.pi - α i) = Real.pi * ((d : ℝ) - 2) := by
  rw [Finset.sum_sub_distrib, hα]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub hd]
  push_cast
  ring

section LocalFormulas
open P202Specs.PlanarRegionTopology

/-- Summation of the actual proved local formulas for every finite family
of positively charted regions and every allowed boundary presentation. -/
theorem sum_local_chart_formulas
    {X : Type u} [TopologicalSpace X] (W : SmoothManifold 2 .euclidean X)
    (g : RiemannianMetric W) (C : Connection (tangentBundle W))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor W) (hT : RepresentsCurvature C T)
    (o : SmoothManifolds.OrientationData.Orientation W)
    {n : ℕ} (c : Fin n → ModelChart 2 .euclidean X)
    (hc : ∀ j, c j ∈ W.smoothStructure.val)
    (hp : ∀ j, P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle W) o (c j) (hc j))
    (R : Fin n → PlanarRegion)
    (hR : ∀ j, (R j).carrier ⊆ P202Specs.ChartRegionStokes.chartTarget (c j))
    (A : ∀ j i, P202Specs.PlaneTurning.ArcPresentation ((R j).curve i))
    (s : ∀ j, Fin (R j).boundaryCount → ℝ)
    (hs : ∀ j, IsInducedBoundaryOrientation (R j) (s j)) :
    ∃ h : ∀ j, P202Specs.EulerPoincare.HomologyFiniteType ℚ (R j).carrier,
      (∑ j, P202Specs.LocalGaussBonnet.curvatureIntegral g T (c j) (hc j) (R j)) +
      (∑ j, P202Specs.LocalGaussBonnet.geodesicIntegral g C o (c j) (hc j)
        (R j) (A j) (s j)) +
      (∑ j, P202Specs.LocalGaussBonnet.exteriorAngleSum g o (c j) (hc j)
        (R j) (A j) (s j)) =
      2 * Real.pi * ∑ j,
        (P202Specs.EulerPoincare.topologicalEuler (R j).carrier (h j) : ℝ) := by
  have hj (j : Fin n) :=
    ((P202.LocalGaussBonnet.localGaussBonnet W g C hC T hT o (c j) (hc j) (hp j) (R j) (hR j)).2
      (A j) (s j) (hs j)).2.2.2.2.1
  choose h hh using hj
  refine ⟨h, ?_⟩
  have hsum := congrArg (fun f : Fin n → ℝ => ∑ j, f j) (funext hh)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum

end LocalFormulas

/-- The last step of the regional argument. All three analytic/geometric
identities are explicit premises here, not assumed certificates attached to
the surface or a replacement for the original theorem. -/
theorem assemble_region_identities {n : ℕ}
    (area boundary : ℝ) (a b ε : Fin n → ℝ)
    (χ : Fin n → ℤ) (V E : ℕ) (χS : ℤ)
    (hlocal : ∀ j, a j + b j + ε j = 2 * Real.pi * (χ j : ℝ))
    (harea : ∑ j, a j = area) (hboundary : ∑ j, b j = boundary)
    (hcorners : ∑ j, ε j = 2 * Real.pi * ((E : ℝ) - (V : ℝ)))
    (heuler : χS = (V : ℤ) - (E : ℤ) + ∑ j, χ j) :
    area + boundary = 2 * Real.pi * (χS : ℝ) := by
  have hsum := congrArg (fun f : Fin n → ℝ => ∑ j, f j) (funext hlocal)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [harea, hboundary, hcorners] at hsum
  have heuler' : (χS : ℝ) = (V : ℝ) - (E : ℝ) + ∑ j, (χ j : ℝ) := by
    exact_mod_cast heuler
  rw [heuler']
  linarith

end P202.GlobalGaussBonnet

/-! Curvature continuity and intrinsic integrability. -/

open Set Filter Module MeasureTheory
open scoped _root_.Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurvatureData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Every actual basis expresses the same Gaussian curvature scalar. -/
theorem gaussianCurvature_eq_basis
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    gaussianCurvature g T p =
      curvatureForm g T p (b 0) (b 1) (b 1) (b 0) /
        (pairing g p (b 0) (b 0) * pairing g p (b 1) (b 1) -
          pairing g p (b 0) (b 1) ^ 2) := by
  have hb (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
      LinearIndependent ℝ ![b 0, b 1] := by
    convert b.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  have hs (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
      Submodule.span ℝ ({b 0, b 1} : Set (TangentSpace S p)) = ⊤ := by
    convert b.span_eq using 2
    ext x
    simp only [mem_insert_iff, mem_singleton_iff, mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  exact P202.Geometry.CurvatureAlgebra.sectional_basis_independent g C hC T hT p
    _ _ _ _ (hb (referenceBasis g p)) (hb b) ((hs _).trans (hs _).symm)

/-- A metric Gram denominator cannot vanish on a basis. -/
theorem basis_gram_ne_zero (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    pairing g p (b 0) (b 0) * pairing g p (b 1) (b 1) -
      pairing g p (b 0) (b 1) ^ 2 ≠ 0 := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  have h := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ) (v := b)).mpr
    b.linearIndependent
  simp only [Matrix.det_fin_two, Matrix.gram, Matrix.of_apply] at h
  change pairing g p (b 0) (b 0) * pairing g p (b 1) (b 1) -
    pairing g p (b 0) (b 1) * pairing g p (b 1) (b 0) ≠ 0 at h
  simp only [pairing] at h ⊢
  rw [g.symmetric p (b 1) (b 0)] at h
  simpa only [pow_two] using h

/-- Continuity follows from smooth local frames and basis independence;
the arbitrary reference orthonormal bases need not vary continuously. -/
theorem continuous_gaussianCurvature
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) :
    Continuous (gaussianCurvature g T) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := tangentBundle S
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B p
  obtain ⟨e, he⟩ := P202.Geometry.ConnectionForms.local_frame_representative B b ⟨p, hp⟩
  have he' : ∀ᶠ q in 𝓝 p, ∀ j, (e j).val q =
      SmoothManifolds.SectionExtension.totalSection (b.section_ j) q :=
    Filter.eventually_all.mpr he
  let R : Field S := ⟨fun q => T.val q ((e 0).val q) ((e 1).val q) ((e 1).val q),
    T.smooth (e 0) (e 1) (e 1)⟩
  let n : M → ℝ := fun q => pairing g q (R.val q) ((e 0).val q)
  let d : M → ℝ := fun q =>
    pairing g q ((e 0).val q) ((e 0).val q) *
    pairing g q ((e 1).val q) ((e 1).val q) -
    pairing g q ((e 0).val q) ((e 1).val q) ^ 2
  have hc (s t : Field S) : ContinuousAt (fun q => pairing g q (s.val q) (t.val q)) p :=
    (P202.Geometry.TorsionAndMetric.metricPairing_smooth B g s t p).1
  have hn : ContinuousAt n p := hc R (e 0)
  have hd : ContinuousAt d p := ((hc (e 0) (e 0)).mul (hc (e 1) (e 1))).sub
    ((hc (e 0) (e 1)).pow 2)
  have heq : (fun q => n q / d q) =ᶠ[𝓝 p] gaussianCurvature g T := by
    filter_upwards [hU.mem_nhds hp, he'] with q hq hqe
    have hv (j : Fin 2) : (e j).val q = b.basis ⟨q, hq⟩ j := by
      rw [hqe j, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
      exact (b.basis_eq ⟨q, hq⟩ j).symm
    dsimp [n, d, R]
    rw [hv 0, hv 1]
    exact (gaussianCurvature_eq_basis g C hC T hT q (b.basis ⟨q, hq⟩)).symm
  have hd0 : d p ≠ 0 := by
    have hv (j : Fin 2) : (e j).val p = b.basis ⟨p, hp⟩ j := by
      rw [(he j).self_of_nhds, SmoothManifolds.SectionExtension.totalSection_of_mem _ p hp]
      exact (b.basis_eq ⟨p, hp⟩ j).symm
    dsimp [d]
    rw [hv 0, hv 1]
    exact basis_gram_ne_zero g p (b.basis ⟨p, hp⟩)
  exact (hn.div hd hd0).congr_of_eventuallyEq heq.symm

/-- Canonical area integrability on every compact measurable subset. -/
theorem integrableOn_gaussianCurvature_of_isCompact
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (A : Set M) (hA : IsCompact A) (hAm : @MeasurableSet M (borel M) A) :
    letI : MeasurableSpace M := borel M
    MeasureTheory.IntegrableOn (gaussianCurvature g T) A μ := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact (continuous_gaussianCurvature g C hC T hT).continuousOn.integrableOn_of_subset_isCompact
    hA hAm (subset_refl A) (ne_of_lt (hμ.2.1 A hA))

/-- The actual Gaussian curvature is integrable on a compact surface with
its canonical area measure, including nonorientable and empty surfaces. -/
theorem integrable_gaussianCurvature [CompactSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ) :
    letI : MeasurableSpace M := borel M
    MeasureTheory.Integrable (gaussianCurvature g T) μ := by
  letI : MeasurableSpace M := borel M
  exact MeasureTheory.integrableOn_univ.mp
    (integrableOn_gaussianCurvature_of_isCompact g C hC T hT μ hμ univ
      isCompact_univ MeasurableSet.univ)

/-- Localization of the actual total Gaussian curvature needs no supplied
integrability certificate: smooth Levi–Civita geometry provides it. -/
theorem regionDecomposition_totalCurvature [CompactSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : P202Specs.SurfaceRegionConstruction.RegionDecomposition S) :
    totalCurvature g T μ =
      (letI : MeasurableSpace M := borel M
       ∑ j, ∫ p in P202Specs.SurfaceRegionsEuler.regionClosure R j,
         gaussianCurvature g T p ∂μ) := by
  letI : MeasurableSpace M := borel M
  have hf := integrable_gaussianCurvature g C hC T hT μ hμ
  exact (regionDecomposition_integral g μ hμ R _ (fun _ => hf.integrableOn)).2

/-- Compact chart regions have the local curvature integral appearing in the
local theorem, with integrability proved from the genuine smooth geometry. -/
theorem local_curvatureIntegral_eq_intrinsic_of_isCompact
    {X : Type u} [TopologicalSpace X] {W : SmoothManifold 2 .euclidean X}
    (g : RiemannianMetric W) (C : Connection (tangentBundle W))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor W) (hT : RepresentsCurvature C T)
    (μ : @Measure X (borel X)) (hμ : IsAreaMeasure g μ)
    (c : SmoothManifolds.ModelData.ModelChart 2 .euclidean X)
    (hc : c ∈ W.smoothStructure.val)
    (R : P202Specs.PlanarRegionTopology.PlanarRegion)
    (A : Set X) (hA : @MeasurableSet X (borel X) A) (hAK : IsCompact A)
    (hAc : A ⊆ c.source)
    (hAR : P202Specs.SurfaceRegionConstruction.coordinates c '' A = R.carrier) :
    (letI : MeasurableSpace X := borel X; ∫ p in A, gaussianCurvature g T p ∂μ) =
      P202Specs.LocalGaussBonnet.curvatureIntegral g T c hc R := by
  exact local_curvatureIntegral_eq_intrinsic g T μ hμ c hc R A hA hAc hAR
    (integrableOn_gaussianCurvature_of_isCompact g C hC T hT μ hμ A hAK hA)

end P202.GlobalGaussBonnet

/-! Intrinsic inward normal uniqueness and normalization. -/
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.SurfaceBoundaryData
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem inwardUnitNormal_unique (g : RiemannianMetric S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) (N₁ N₂ : TangentSpace S p)
    (h₁ : IsInwardUnitNormal g p ℓ N₁) (h₂ : IsInwardUnitNormal g p ℓ N₂) :
    N₁ = N₂ := by
  let a : ℝ := ℓ N₁ / ℓ N₂
  have ha : 0 < a := div_pos h₁.2.2 h₂.2.2
  have hk : ℓ (N₁ - a • N₂) = 0 := by
    rw [show ℓ (N₁ - a • N₂) = ℓ N₁ - ℓ (a • N₂) from
      map_sub ℓ N₁ (a • N₂), map_smul, smul_eq_mul]
    dsimp [a]
    field_simp [ne_of_gt h₂.2.2]
    ring
  have hq : N₁ - a • N₂ = 0 := by
    by_contra hn
    have hp : 0 < pairing g p (N₁ - a • N₂) (N₁ - a • N₂) :=
      g.positive p (N₁ - a • N₂) hn
    have hzero : pairing g p (N₁ - a • N₂) (N₁ - a • N₂) = 0 := by
      rw [show pairing g p (N₁ - a • N₂) (N₁ - a • N₂) =
        pairing g p N₁ (N₁ - a • N₂) - pairing g p (a • N₂) (N₁ - a • N₂) from
        LinearMap.BilinForm.sub_left (B₁ := pairing g p) N₁ (a • N₂) (N₁ - a • N₂),
        LinearMap.BilinForm.smul_left,
        h₁.2.1 _ hk, h₂.2.1 _ hk]
      ring
    linarith
  have hEq : N₁ = a • N₂ := sub_eq_zero.mp hq
  have hasq : a ^ 2 = 1 := by
    have hu := h₁.1
    rw [hEq, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h₂.1] at hu
    nlinarith
  have hone : a = 1 := by nlinarith
  simpa [hone] using hEq
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem inwardUnitNormal_pos_smul_iff (g : RiemannianMetric S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) (N : TangentSpace S p)
    (r : ℝ) (hr : 0 < r) :
    IsInwardUnitNormal g p (r • ℓ) N ↔ IsInwardUnitNormal g p ℓ N := by
  constructor
  · rintro ⟨hu, ho, hp⟩
    refine ⟨hu, ?_, ?_⟩
    · intro V hV
      apply ho V
      simp [hV]
    · change 0 < r * ℓ N at hp
      exact (mul_pos_iff_of_pos_left hr).mp hp
  · rintro ⟨hu, ho, hp⟩
    refine ⟨hu, ?_, ?_⟩
    · intro V hV
      apply ho V
      change r * ℓ V = 0 at hV
      exact (mul_eq_zero.mp hV).resolve_left (ne_of_gt hr)
    · change 0 < r * ℓ N
      exact mul_pos hr hp
 theorem curvatureVector_speed_pairing (C : P202.ConnectionData.Connection
      (P202.ConnectionData.tangentBundle S)) (g : RiemannianMetric S)
    (c : ℝ → M) (T : (t : ℝ) → TangentSpace S (c t)) (speed : ℝ → ℝ)
    (t : ℝ) (N : TangentSpace S (c t)) (hs : speed t ≠ 0) :
    inwardCurvature g (c t) (curvatureVector C g c T speed t) N * speed t =
      pairing g (c t) (P202.CurveConnectionData.covariantDerivative C c T t) N := by
  change pairing g (c t)
    ((speed t)⁻¹ • P202.CurveConnectionData.covariantDerivative C c T t) N * speed t = _
  rw [LinearMap.BilinForm.smul_left]
  field_simp
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem boundary_curvatureIntegrand_eq (g : RiemannianMetric S)
    (B : P202Specs.GlobalGaussBonnet.BoundaryPresentation g)
    (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S))
    (i : Fin B.count) (t : ℝ)
    (ht : t ∈ Set.Ioo (B.arc i).left (B.arc i).right) :
    B.curvatureIntegrand C i t = pairing g ((B.arc i).curve t)
      (P202.CurveConnectionData.covariantDerivative C
        (B.arc i).curve (B.arc i).tangent t)
      (boundaryNormal g (B.side i t ht)) := by
  unfold P202Specs.GlobalGaussBonnet.BoundaryPresentation.curvatureIntegrand
  rw [dif_pos ht]
  apply curvatureVector_speed_pairing
  have hv := (B.arc i).regular t (Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩)
  exact ne_of_gt (Real.sqrt_pos.mpr (g.positive _ _ hv))
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem normalVector_pos_smul (g : RiemannianMetric S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) (r : ℝ) (hr : 0 < r) :
    normalVector g p (r • ℓ) = normalVector g p ℓ := by
  simp only [normalVector, map_smul, P202.Geometry.SmoothMetrics.tangentNorm_smul,
    abs_of_pos hr, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), mul_one]
 theorem boundaryNormal_eq_of_pos_smul (g : RiemannianMetric S)
    {D₁ D₂ : Set M} {p : M} (b₁ : BoundarySideAt (S := S) D₁ p)
    (b₂ : BoundarySideAt (S := S) D₂ p) (r : ℝ) (hr : 0 < r)
    (hderiv : P202.ConnectionData.scalarDerivative S b₂.definingFunction p =
      r • P202.ConnectionData.scalarDerivative S b₁.definingFunction p) :
    boundaryNormal g b₂ = boundaryNormal g b₁ := by
  unfold boundaryNormal
  rw [hderiv]
  exact normalVector_pos_smul g p _ r hr
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem conormal_eq_pos_smul_of_same_kernel (p : M)
    (ℓ₁ ℓ₂ : Module.Dual ℝ (TangentSpace S p))
    (hker : ∀ V, ℓ₁ V = 0 ↔ ℓ₂ V = 0)
    (V : TangentSpace S p) (h₁ : 0 < ℓ₁ V) (h₂ : 0 < ℓ₂ V) :
    ∃ r : ℝ, 0 < r ∧ ℓ₂ = r • ℓ₁ := by
  refine ⟨ℓ₂ V / ℓ₁ V, div_pos h₂ h₁, ?_⟩
  ext W
  have hk : ℓ₁ (W - (ℓ₁ W / ℓ₁ V) • V) = 0 := by
    rw [map_sub ℓ₁ W ((ℓ₁ W / ℓ₁ V) • V), map_smul, smul_eq_mul]
    field_simp [ne_of_gt h₁]
    ring
  have hz := (hker _).mp hk
  rw [map_sub ℓ₂ W ((ℓ₁ W / ℓ₁ V) • V), map_smul, smul_eq_mul] at hz
  change ℓ₂ W = (ℓ₂ V / ℓ₁ V) * ℓ₁ W
  calc
    ℓ₂ W = (ℓ₁ W / ℓ₁ V) * ℓ₂ V := sub_eq_zero.mp hz
    _ = (ℓ₂ V / ℓ₁ V) * ℓ₁ W := by ring
 theorem normalVector_eq_of_same_kernel (g : RiemannianMetric S) (p : M)
    (ℓ₁ ℓ₂ : Module.Dual ℝ (TangentSpace S p))
    (hker : ∀ V, ℓ₁ V = 0 ↔ ℓ₂ V = 0)
    (V : TangentSpace S p) (h₁ : 0 < ℓ₁ V) (h₂ : 0 < ℓ₂ V) :
    normalVector g p ℓ₂ = normalVector g p ℓ₁ := by
  obtain ⟨r, hr, heq⟩ := conormal_eq_pos_smul_of_same_kernel p ℓ₁ ℓ₂ hker V h₁ h₂
  rw [heq]
  exact normalVector_pos_smul g p ℓ₁ r hr
end P202.GlobalGaussBonnet
open Set Filter
open scoped _root_.Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.SurfaceBoundaryData P202.ConnectionData
open private right_derivative_nonneg from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem side_derivative_nonneg_on_forward_curve {p : M}
    (b : BoundarySideAt (S := S) univ p) (V : TangentSpace S p)
    (c : ℝ → M) (hc : CurveRepresentsDerivation S p .forward c V) :
    0 ≤ scalarDerivative S b.definingFunction p V := by
  have hsm := b.smooth p b.contains
  have hrep : Germ.ofFun b.definingFunction = (scalarGerm S b.definingFunction p).val := by
    simp only [scalarGerm, dite_eq_left hsm]
  have hd := hc.2 (scalarGerm S b.definingFunction p) b.definingFunction hrep
  change HasDerivWithinAt (b.definingFunction ∘ c)
    (scalarDerivative S b.definingFunction p V) (Ici 0) 0 at hd
  have hev : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ), 0 ≤ b.definingFunction (c t) := by
    have hct : Tendsto c (𝓝[Ici 0] 0) (𝓝 p) := by
      simpa only [ContinuousWithinAt, hc.1.1, curveParameterSet] using hc.1.2.1
    filter_upwards [hct.eventually (b.isOpen.mem_nhds b.contains)] with t ht
    exact (b.region (c t) ht).mp (mem_univ _)
  have heq : (b.definingFunction ∘ c) =ᶠ[𝓝[Ici 0] (0 : ℝ)]
      (fun t => max (b.definingFunction (c t)) 0) := by
    filter_upwards [hev] with t ht
    exact (max_eq_left ht).symm
  have hzero : b.definingFunction (c 0) = 0 := hc.1.1 ▸ b.vanishes
  apply right_derivative_nonneg (f := fun t => max (b.definingFunction (c t)) 0)
    (fun t => le_max_right _ _) (by simp [hzero])
  exact hd.congr_of_eventuallyEq heq.symm (by simp [hzero])
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 .halfSpace M}
 theorem side_derivative_nonneg_on_forward_coordinate {p : M}
    (bp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) univ p)
    (e : ModelChart 2 .halfSpace M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
    (hE : SmoothManifolds.DifferentialData.IsChartCoordinates S p e E)
    (V : TangentSpace S p) (hV : 0 ≤ E V (Fin.last 1)) :
    0 ≤ scalarDerivative S b.definingFunction p V := by
  obtain ⟨c, hc⟩ := (SmoothManifolds.boundary_curve_cones S ⟨p, bp⟩ e he hp
    E hE .forward V).mpr hV
  exact side_derivative_nonneg_on_forward_curve b V c hc
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 .halfSpace M}
 theorem side_conormal_positive_coordinate {p : M}
    (bp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) univ p)
    (e : ModelChart 2 .halfSpace M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
    (hE : SmoothManifolds.DifferentialData.IsChartCoordinates S p e E) :
    ∃ r : ℝ, 0 < r ∧ ∀ V, scalarDerivative S b.definingFunction p V =
      r * E V (Fin.last 1) := by
  let ℓ := scalarDerivative S b.definingFunction p
  let N := E.symm (Pi.single (Fin.last 1) 1)
  have hN : E N (Fin.last 1) = 1 := by simp [N]
  have hz (V : TangentSpace S p) (hV : E V (Fin.last 1) = 0) : ℓ V = 0 := by
    have hpos := side_derivative_nonneg_on_forward_coordinate bp b e he hp E hE V (by rw [hV])
    have hneg := side_derivative_nonneg_on_forward_coordinate bp b e he hp E hE (-V) (by
      rw [map_neg E V, Pi.neg_apply, hV, neg_zero])
    change 0 ≤ ℓ V at hpos
    change 0 ≤ ℓ (-V) at hneg
    rw [map_neg ℓ V] at hneg
    linarith
  have hformula (V : TangentSpace S p) : ℓ V = ℓ N * E V (Fin.last 1) := by
    have hzero : E (V - E V (Fin.last 1) • N) (Fin.last 1) = 0 := by
      rw [map_sub E V (E V (Fin.last 1) • N),
        map_smul E (E V (Fin.last 1)) N, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hN]
      ring
    have hzeroℓ := hz _ hzero
    rw [map_sub ℓ V (E V (Fin.last 1) • N), map_smul, smul_eq_mul] at hzeroℓ
    exact (sub_eq_zero.mp hzeroℓ).trans (mul_comm _ _)
  have hn : 0 ≤ ℓ N := side_derivative_nonneg_on_forward_coordinate bp b e he hp E hE N (by
    rw [hN]; norm_num)
  have hn0 : ℓ N ≠ 0 := by
    intro hzero
    apply b.regular
    ext V
    change ℓ V = 0
    rw [hformula, hzero, zero_mul]
  exact ⟨ℓ N, lt_of_le_of_ne' hn hn0, hformula⟩
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem boundary_conormals_pos_smul {p : M}
    (bp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b₁ b₂ : BoundarySideAt (S := S) univ p) :
    ∃ r : ℝ, 0 < r ∧ scalarDerivative S b₂.definingFunction p =
      r • scalarDerivative S b₁.definingFunction p := by
  cases kind with
  | euclidean =>
    have hb := SmoothManifolds.intrinsicBoundary_euclidean S
    change p ∈ SmoothManifolds.intrinsicBoundary S at bp
    rw [hb] at bp
    exact False.elim bp
  | halfSpace =>
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    let E := SmoothManifolds.coordinateDerivationEquiv S p e he hp
    have hE := SmoothManifolds.coordinateDerivationEquiv_isChartCoordinates S p e he hp
    obtain ⟨r₁, hr₁, h₁⟩ := side_conormal_positive_coordinate bp b₁ e he hp E hE
    obtain ⟨r₂, hr₂, h₂⟩ := side_conormal_positive_coordinate bp b₂ e he hp E hE
    refine ⟨r₂ / r₁, div_pos hr₂ hr₁, ?_⟩
    ext V
    change scalarDerivative S b₂.definingFunction p V =
      (r₂ / r₁) * scalarDerivative S b₁.definingFunction p V
    rw [h₁, h₂]
    field_simp
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem boundaryNormal_eq {p : M} (g : RiemannianMetric S)
    (bp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b₁ b₂ : BoundarySideAt (S := S) univ p) :
    boundaryNormal g b₂ = boundaryNormal g b₁ := by
  obtain ⟨r, hr, heq⟩ := boundary_conormals_pos_smul bp b₁ b₂
  exact P202.GlobalGaussBonnet.boundaryNormal_eq_of_pos_smul g b₁ b₂ r hr heq
end P202.GlobalGaussBonnet

/-! Actual boundary defining functions and smooth metric normals. -/
open Set Filter
open scoped _root_.Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.SurfaceBoundaryData P202.ConnectionData
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem chart_coordinate_smooth (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (i : Fin 2) (p : M) (hp : p ∈ e.source) :
    SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val (fun q => (e q).val i) p := by
  apply SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
  exact ⟨univ, isOpen_univ, mem_univ _, fun z => z i,
    (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) i).contDiffOn,
    Eventually.of_forall (fun _ => rfl)⟩
 theorem scalarDerivative_chart_coordinate (e : ModelChart 2 kind M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (i : Fin 2) (V : TangentSpace S p) :
    scalarDerivative S (fun q => (e q).val i) p V =
      SmoothManifolds.coordinateDerivationEquiv S p e he hp V i := by
  have hsm := chart_coordinate_smooth e he i p hp
  have hg : scalarGerm S (fun q => (e q).val i) p =
      SmoothManifolds.coordinateGerm S p e he hp i := by
    apply Subtype.ext
    simp only [scalarGerm, dite_eq_left hsm]
    rfl
  change V.val (scalarGerm S (fun q => (e q).val i) p) = _
  rw [hg]
  rfl
 theorem scalarDerivative_chart_coordinate_ne_zero (e : ModelChart 2 kind M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) (i : Fin 2) :
    scalarDerivative S (fun q => (e q).val i) p ≠ 0 := by
  intro hz
  let E := SmoothManifolds.coordinateDerivationEquiv S p e he hp
  let V := E.symm (Pi.single i 1)
  have hv : scalarDerivative S (fun q => (e q).val i) p V = 1 := by
    rw [scalarDerivative_chart_coordinate]
    change E V i = 1
    simp [V]
  rw [hz, LinearMap.zero_apply] at hv
  exact zero_ne_one hv
 def chartBoundarySideAt {S : SmoothManifold 2 .halfSpace M}
    (e : ModelChart 2 .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source)
    (bp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S) :
    BoundarySideAt (S := S) univ p where
  neighborhood := e.source
  isOpen := e.open_source
  contains := hp
  definingFunction := fun q => (e q).val (Fin.last 1)
  smooth := chart_coordinate_smooth e he (Fin.last 1)
  vanishes := (SmoothManifolds.intrinsicBoundary_iff_chart S e he p hp).mp bp
  region := fun q _ => ⟨fun _ => (e q).property, fun _ => mem_univ _⟩
  regular := scalarDerivative_chart_coordinate_ne_zero e he p hp (Fin.last 1)
 theorem existsBoundarySideAt {p : M}
    (bp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S) :
    Nonempty (BoundarySideAt (S := S) univ p) := by
  cases kind with
  | euclidean =>
    change p ∈ SmoothManifolds.intrinsicBoundary S at bp
    rw [SmoothManifolds.intrinsicBoundary_euclidean S] at bp
    exact False.elim bp
  | halfSpace =>
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    exact ⟨chartBoundarySideAt e he p hp bp⟩
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.BundleOperationsData SmoothManifolds.FrameData
  SmoothManifolds.MapData SmoothManifolds.BundleData
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem coordinate_covector_smoothAt (e : ModelChart 2 kind M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) (j : Fin 2) :
    ManifoldSmoothAt S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, scalarDerivative S (fun y => (e y).val j) q⟩ :
        Bundle.TotalSpace (Euclidean 2) (fun q => Module.Dual ℝ (TangentSpace S q)))) p := by
  let B := tangentBundle S
  let i : TangentIndex S := ⟨e, he⟩
  have hpi : p ∈ B.baseSet i := by
    change p ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hp
  apply SmoothManifolds.SectionExtension.smoothAt_of_coordinates (cotangentBundle S) i
    (by rw [(cotangentDual S).baseSet]; exact hpi)
  apply (VectorSmoothAt.const S.smoothStructure.val (Pi.single j (1 : ℝ)) p).congr
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  ext k
  have hqi : q ∈ B.baseSet i := by
    change q ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hq
  rw [(cotangentDual S).coordinates i q hqi]
  rw [scalarDerivative_chart_coordinate e he q hq]
  let V := (B.trivialization i).symm q (Pi.single k 1)
  have hK := SmoothManifolds.chartCoordinates_eq S q e he hq
    ((tangentStructure S).fiberCoordinates.equiv e he q hq)
    ((tangentStructure S).fiberCoordinates.isCoordinates e he q hq) V
  rw [← hK, ← (tangentRealization S).coordinates i q hq V]
  have hv : ((B.trivialization i) ⟨q, V⟩).2 = Pi.single k 1 := by
    rw [← SmoothVectorBundle.fiberCoordinates_apply B i q hqi]
    change (B.fiberCoordinates i q hqi) ((B.trivialization i).symm q (Pi.single k 1)) = _
    rw [← SmoothVectorBundle.fiberCoordinates_symm_apply B i q hqi]
    exact LinearEquiv.apply_symm_apply _ _
  rw [hv]
  simp [Pi.single_apply, eq_comm]
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
open SmoothManifolds.FrameData SmoothManifolds.MapData
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem coordinate_metricDual_smoothAt (g : RiemannianMetric S)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (j : Fin 2) :
    ManifoldSmoothAt S.smoothStructure.val (tangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g q).symm
        (scalarDerivative S (fun y => (e y).val j) q)⟩ :
        Bundle.TotalSpace (Euclidean 2) (TangentSpace S))) p := by
  let iso := SmoothManifolds.MetricSplittings.metricIso (tangentBundle S) g (cotangentDual S)
  exact SmoothManifolds.manifoldContDiffAt_comp
    (cotangentBundle S).totalManifold.smoothStructure.property.1.1
    (coordinate_covector_smoothAt e he p hp j) (iso.inverse_smooth _)
 theorem coordinate_normalVector_smoothAt (g : RiemannianMetric S)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (j : Fin 2) :
    ManifoldSmoothAt S.smoothStructure.val (tangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, normalVector g q
        (scalarDerivative S (fun y => (e y).val j) q)⟩ :
        Bundle.TotalSpace (Euclidean 2) (TangentSpace S))) p := by
  let V : (q : M) → TangentSpace S q := fun q =>
    (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g q).symm
      (scalarDerivative S (fun y => (e y).val j) q)
  have hV : ManifoldSmoothAt S.smoothStructure.val (tangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, V q⟩ : Bundle.TotalSpace (Euclidean 2) (TangentSpace S))) p :=
    coordinate_metricDual_smoothAt g e he p hp j
  have hvne : V p ≠ 0 := by
    intro hz
    apply scalarDerivative_chart_coordinate_ne_zero e he p hp j
    have h := congrArg (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p) hz
    simpa only [V, LinearEquiv.apply_symm_apply, map_zero] using h
  have hid := SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p
  have hQ : VectorSmoothAt S.smoothStructure.val (fun q => pairing g q (V q) (V q)) p :=
    P202.Geometry.SmoothMetrics.metric_pairing_smoothAt S (tangentBundle S) g id V V p hid hV hV
  have hnorm : VectorSmoothAt S.smoothStructure.val (fun q => tangentNorm g q (V q)) p := by
    apply hQ.postcompOn isOpen_Ioi (g.positive p (V p) hvne)
    intro x hx
    exact (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt
  have hnormne : tangentNorm g p (V p) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (g.positive p (V p) hvne))
  have hinv := ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hnorm).inv hnormne
  exact SmoothManifolds.SectionExtension.section_smul_smoothAt (tangentBundle S) hinv hV
end P202.GlobalGaussBonnet

/-! Oriented chart restrictions and actual curvature naturality. -/
set_option maxHeartbeats 300000
open Set
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentBundleData SmoothManifolds.OrientationData
  SmoothManifolds.OrientationCoverData
namespace P202.GlobalGaussBonnet
variable {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}
def globalRay (L : LocalOrientation S) (hsource : L.domain = univ) : RayField S :=
  fun p => L.ray ⟨p, by rw [hsource]; trivial⟩

theorem globalRay_continuous (L : LocalOrientation S) (hsource : L.domain = univ) :
    IsContinuousRayField (globalRay L hsource) := by
  intro K' d hd
  have hmem (p : M) : p ∈ L.domain := by rw [hsource]; trivial
  let incl : d.source → ↥(L.domain ∩ d.source) :=
    fun p => ⟨p.val, hmem p.val, p.property⟩
  have h := (L.continuous K' d hd).comp_continuous
    (continuous_subtype_val.subtype_mk _ : Continuous incl)
  exact h
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}
def LocalOrientation.toGlobal (L : LocalOrientation S) (hsource : L.domain = univ) :
    Orientation S := ⟨globalRay L hsource, globalRay_continuous L hsource⟩

def globalChartOrientation (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hsource : c.source = univ) : Orientation S :=
  LocalOrientation.toGlobal (SmoothManifolds.OrientationCover.coordinateLocal K c hc) hsource
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.BundleOperationsData
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
theorem globalChartOrientation_positive (K : FiberCoordinates S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hsource : c.source = univ) (B : CotangentBundle S) :
    P202Specs.ChartRegionStokes.PositiveChart B
      (globalChartOrientation K c hc hsource) c hc := by
  intro p
  change IsPositive
    (rayOfNeZero ℝ (coordinateVector K c hc p)
      (SmoothManifolds.OrientationResults.coordinateVector_ne_zero K c hc p))
    (coordinateVector B.tangent.fiberCoordinates c hc p)
  rw [SmoothManifolds.OrientationResults.coordinateVector_independent
    B.tangent.fiberCoordinates K]
  exact ⟨SmoothManifolds.OrientationResults.coordinateVector_ne_zero K c hc p, rfl⟩
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
variable {M : Type u} [TopologicalSpace M]
theorem exists_orientedChartRestriction (S : SmoothManifold 2 .euclidean M)
    (e : ModelChart 2 .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hne : e.source.Nonempty) :
    ∃ Q : SmoothManifold 2 .euclidean e.source,
      IsSmoothMap Q S Subtype.val ∧
      ∃ d : ModelChart 2 .euclidean e.source,
        ∃ hd : d ∈ Q.smoothStructure.val,
          d.source = univ ∧ (∀ p, d p = e p.val) ∧
          ∃ o : Orientation Q,
            ∀ B : CotangentBundle Q,
              P202Specs.ChartRegionStokes.PositiveChart B o d hd := by
  obtain ⟨Q, _, hQA, hQ⟩ := SmoothManifolds.exists_openSubset_smoothManifold S
    e.source e.open_source
  let hp : Nonempty e.source := hne.to_subtype
  let d := e.subtypeRestr (s := ⟨e.source, e.open_source⟩) hp
  have hd : d ∈ Q.smoothStructure.val := by
    rw [hQA]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _
        S.smoothStructure.property.1 e.source e.open_source) ⟨hp, e, he, rfl⟩
  have hds : d.source = univ := by
    ext p
    simp only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
      mem_univ, iff_true]
    exact p.property
  let K := Classical.choice (SmoothManifolds.TangentBundle.fiberCoordinates_exists Q)
  exact ⟨Q, hQ, d, hd, hds, (fun _ => rfl), globalChartOrientation K d hd hds,
    fun B => globalChartOrientation_positive K d hd hds B⟩
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
open P202.MetricData
variable {M : Type u} [TopologicalSpace M]
theorem exists_orientedChartMetricRestriction (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S)
    (e : ModelChart 2 .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hne : e.source.Nonempty) :
    ∃ Q : SmoothManifold 2 .euclidean e.source,
      ∃ i : SmoothImmersion Q S Subtype.val,
        ∃ h : RiemannianMetric Q,
          IsMetricPreserving h g Subtype.val i.differential ∧
          ∃ d : ModelChart 2 .euclidean e.source,
            ∃ hd : d ∈ Q.smoothStructure.val,
              d.source = univ ∧ (∀ p, d p = e p.val) ∧
              ∃ o : Orientation Q,
                ∀ B : CotangentBundle Q,
                  P202Specs.ChartRegionStokes.PositiveChart B o d hd := by
  obtain ⟨Q, _, hQA, _⟩ := SmoothManifolds.exists_openSubset_smoothManifold S
    e.source e.open_source
  have hQE := (SmoothManifolds.TransversePreimage.open_subset_embedded_of_atlas_eq
    S e.source e.open_source Q hQA).1
  obtain ⟨i⟩ := (P202.Geometry.SmoothMetrics.smoothImmersion_iff Q S Subtype.val).mpr
    ⟨hQE.1, hQE.2.2.1⟩
  let h := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i
  let hp : Nonempty e.source := hne.to_subtype
  let d := e.subtypeRestr (s := ⟨e.source, e.open_source⟩) hp
  have hd : d ∈ Q.smoothStructure.val := by
    rw [hQA]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _
        S.smoothStructure.property.1 e.source e.open_source) ⟨hp, e, he, rfl⟩
  have hds : d.source = univ := by
    ext p
    simp only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
      mem_univ, iff_true]
    exact p.property
  let K := Classical.choice (SmoothManifolds.TangentBundle.fiberCoordinates_exists Q)
  exact ⟨Q, i, h, (fun _ _ _ => rfl), d, hd, hds, (fun _ => rfl),
    globalChartOrientation K d hd hds,
    fun B => globalChartOrientation_positive K d hd hds B⟩
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.MapData SmoothManifolds.TensorData
open Filter
open scoped _root_.Topology
variable {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
theorem openSubset_localDiffeomorphism (S : SmoothManifold n kind M)
    (U : Set M) (hU : IsOpen U) (Q : SmoothManifold n kind U)
    (hQA : Q.smoothStructure.val = maximalExtension ⊤
      (openSubsetAtlas S.smoothStructure.val U hU)) :
    IsLocalDiffeomorphism Q S Subtype.val := by
  classical
  have hQE := (SmoothManifolds.TransversePreimage.open_subset_embedded_of_atlas_eq
    S U hU Q hQA).1
  refine ⟨hQE.1, ?_⟩
  intro p
  let inv : M → U := fun q => if hq : q ∈ U then ⟨q, hq⟩ else p
  have hval : (fun q => (inv q).val) =ᶠ[𝓝 p.val] id := by
    filter_upwards [hU.mem_nhds p.property] with q hq
    simp only [inv, dite_eq_left hq, id_eq]
  have hcont : ContinuousAt inv p.val := by
    apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    exact continuousAt_id.congr hval.symm
  have hinvp : inv p.val = p := by simp only [inv, dite_eq_left p.property]
  have hsmooth : ManifoldSmoothAt S.smoothStructure.val Q.smoothStructure.val inv p.val := by
    obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p.val
    let d := e.subtypeRestr (s := ⟨U, hU⟩) ⟨p⟩
    have hd : d ∈ Q.smoothStructure.val := by
      rw [hQA]
      exact SmoothManifolds.subset_maximalExtension
        (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _
          S.smoothStructure.property.1 U hU) ⟨⟨p⟩, e, he, rfl⟩
    apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart ⊤ _ _
      S.smoothStructure.property.1 Q.smoothStructure.property.1 inv p.val).mpr
    refine ⟨hcont, e, he, d, hd, hpe, ?_, ?_⟩
    · rw [hinvp]
      simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hpe
    · refine ⟨univ, isOpen_univ, mem_univ _, id, contDiff_id.contDiffOn, ?_⟩
      filter_upwards [hU.mem_nhds p.property] with q hq
      simp only [inv, dite_eq_left hq, id_eq]
      rfl
  refine ⟨inv, hsmooth, hinvp, ?_, hval⟩
  exact Filter.Eventually.of_forall (fun q => by simp only [Function.comp_apply, inv,
    dite_eq_left q.property, id_eq])
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.MapData SmoothManifolds.TensorData SmoothManifolds.DifferentialData
  SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
open Filter
open scoped _root_.Topology
variable {n m : ℕ} {a b : SmoothManifolds.ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold m b N}

theorem localIsometry_curvature_related_at (f : M → N)
    (hf : IsLocalDiffeomorphism S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (X Y Z : Field S) (X' Y' Z' : Field W) (p : M)
    (hX : ∀ᶠ q in 𝓝 p, L q (X.val q) = X'.val (f q))
    (hY : ∀ᶠ q in 𝓝 p, L q (Y.val q) = Y'.val (f q))
    (hZ : ∀ᶠ q in 𝓝 p, L q (Z.val q) = Z'.val (f q)) :
    L p ((curvature C X Y Z).val p) = (curvature K X' Y' Z').val (f p) := by
  have conn (A B : Field S) (A' B' : Field W) (q : M)
      (hA : ∀ᶠ r in 𝓝 q, L r (A.val r) = A'.val (f r))
      (hB : ∀ᶠ r in 𝓝 q, L r (B.val r) = B'.val (f r)) :=
    P202.Geometry.LeviCivita.connection_related_at
      P202.Geometry.TorsionAndMetric.torsion_apply f hf L hL g h hm C K hC hK
      A B A' B' q hA hB
  have hYZ : ∀ᶠ q in 𝓝 p,
      L q ((C.cov Y Z).val q) = (K.cov Y' Z').val (f q) := by
    filter_upwards [hY.eventually_nhds, hZ.eventually_nhds] with q hYq hZq
    exact conn Y Z Y' Z' q hYq hZq
  have hXZ : ∀ᶠ q in 𝓝 p,
      L q ((C.cov X Z).val q) = (K.cov X' Z').val (f q) := by
    filter_upwards [hX.eventually_nhds, hZ.eventually_nhds] with q hXq hZq
    exact conn X Z X' Z' q hXq hZq
  have hXY : ∀ᶠ q in 𝓝 p,
      L q ((P202.TorsionMetricData.bracket X Y).val q) =
        (P202.TorsionMetricData.bracket X' Y').val (f q) := by
    filter_upwards [hX.eventually_nhds, hY.eventually_nhds] with q hXq hYq
    exact P202.Geometry.LeviCivita.bracket_related_at f hf.1 L hL X Y X' Y' q hXq hYq
  rw [P202.Geometry.CurvatureAlgebra.curvature_apply,
    P202.Geometry.CurvatureAlgebra.curvature_apply]
  have hmapp (v w : TangentSpace S p) : L p (v - w) = L p v - L p w :=
    by
      rw [P202.Geometry.LeviCivita.tangent_sub_as_add,
        P202.Geometry.LeviCivita.tangent_sub_as_add]
      simp only [map_add, map_smul]
  rw [hmapp, hmapp,
    conn X (C.cov Y Z) X' (K.cov Y' Z') p hX hYZ,
    conn Y (C.cov X Z) Y' (K.cov X' Z') p hY hXZ,
    conn (P202.TorsionMetricData.bracket X Y) Z
      (P202.TorsionMetricData.bracket X' Y') Z' p hXY hZ]

theorem localIsometry_curvatureTensor (f : M → N)
    (hf : IsLocalDiffeomorphism S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (p : M) (v w z : TangentSpace S p) :
    L p (R.val p v w z) = R'.val (f p) (L p v) (L p w) (L p z) := by
  obtain ⟨X, hXp⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective
    (tangentBundle S) p v
  obtain ⟨Y, hYp⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective
    (tangentBundle S) p w
  obtain ⟨Z, hZp⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective
    (tangentBundle S) p z
  obtain ⟨X', hX⟩ := P202.Geometry.LeviCivita.exists_related_germ f hf L hL X p
  obtain ⟨Y', hY⟩ := P202.Geometry.LeviCivita.exists_related_germ f hf L hL Y p
  obtain ⟨Z', hZ⟩ := P202.Geometry.LeviCivita.exists_related_germ f hf L hL Z p
  rw [← hXp, ← hYp, ← hZp, hR X Y Z p,
    localIsometry_curvature_related_at f hf L hL g h hm C K hC hK
      X Y Z X' Y' Z' p hX hY hZ, ← hR' X' Y' Z' (f p),
    hX.self_of_nhds, hY.self_of_nhds, hZ.self_of_nhds]
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.MapData SmoothManifolds.TensorData SmoothManifolds.DifferentialData
  SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
variable {n m : ℕ} {a b : SmoothManifolds.ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold m b N}
theorem localIsometry_curvatureForm (f : M → N)
    (hf : IsLocalDiffeomorphism S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (p : M) (v w z t : TangentSpace S p) :
    curvatureForm g R p v w z t =
      curvatureForm h R' (f p) (L p v) (L p w) (L p z) (L p t) := by
  unfold curvatureForm
  rw [← localIsometry_curvatureTensor f hf L hL g h hm C K hC hK R R' hR hR' p v w z]
  exact (hm p (R.val p v w z) t).symm

theorem localIsometry_sectionalCurvature (f : M → N)
    (hf : IsLocalDiffeomorphism S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (p : M) (v w : TangentSpace S p)
    (hvw : LinearIndependent ℝ ![v, w])
    (hvw' : LinearIndependent ℝ ![L p v, L p w]) :
    sectionalCurvature g R p v w hvw =
      sectionalCurvature h R' (f p) (L p v) (L p w) hvw' := by
  unfold sectionalCurvature
  rw [localIsometry_curvatureForm f hf L hL g h hm C K hC hK R R' hR hR' p v w w v,
    hm p v v, hm p w w, hm p v w]

open SmoothManifolds.BundleOperationsData

theorem openSubset_pullback_localIsometry (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (Q : SmoothManifold n a U)
    (hQA : Q.smoothStructure.val = maximalExtension ⊤
      (openSubsetAtlas S.smoothStructure.val U hU))
    (g : RiemannianMetric S) (i : SmoothImmersion Q S Subtype.val) :
    IsLocalIsometry (P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i)
      g Subtype.val :=
  ⟨openSubset_localDiffeomorphism S U hU Q hQA,
    i.differential, i.isDifferential, (fun _ _ _ => rfl)⟩
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
open P202.MetricData
variable {M : Type u} [TopologicalSpace M]
theorem exists_orientedChartLocalIsometry (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S)
    (e : ModelChart 2 .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hne : e.source.Nonempty) :
    ∃ Q : SmoothManifold 2 .euclidean e.source,
      ∃ i : SmoothImmersion Q S Subtype.val,
        ∃ h : RiemannianMetric Q,
          IsLocalIsometry h g Subtype.val ∧
          IsMetricPreserving h g Subtype.val i.differential ∧
          ∃ d : ModelChart 2 .euclidean e.source,
            ∃ hd : d ∈ Q.smoothStructure.val,
              d.source = univ ∧ d.target = e.target ∧
              (∀ p, d p = e p.val) ∧
              ∃ o : Orientation Q,
                ∀ B : CotangentBundle Q,
                  P202Specs.ChartRegionStokes.PositiveChart B o d hd := by
  obtain ⟨Q, _, hQA, _⟩ := SmoothManifolds.exists_openSubset_smoothManifold S
    e.source e.open_source
  have hQE := (SmoothManifolds.TransversePreimage.open_subset_embedded_of_atlas_eq
    S e.source e.open_source Q hQA).1
  obtain ⟨i⟩ := (P202.Geometry.SmoothMetrics.smoothImmersion_iff Q S Subtype.val).mpr
    ⟨hQE.1, hQE.2.2.1⟩
  let h := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i
  let hp : Nonempty e.source := hne.to_subtype
  let d := e.subtypeRestr (s := ⟨e.source, e.open_source⟩) hp
  have hd : d ∈ Q.smoothStructure.val := by
    rw [hQA]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _
        S.smoothStructure.property.1 e.source e.open_source) ⟨hp, e, he, rfl⟩
  have hds : d.source = univ := by
    ext p
    simp only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
      mem_univ, iff_true]
    exact p.property
  have hdt : d.target = e.target := by
    apply Subset.antisymm (e.subtypeRestr_target_subset hp)
    intro z hz
    have hmem := e.map_subtype_source (s := ⟨e.source, e.open_source⟩) hp
      (x := ⟨e.symm z, e.map_target hz⟩) (e.map_target hz)
    simpa only [e.right_inv hz] using hmem
  let K := Classical.choice (SmoothManifolds.TangentBundle.fiberCoordinates_exists Q)
  exact ⟨Q, i, h, openSubset_pullback_localIsometry S e.source e.open_source Q hQA g i,
    (fun _ _ _ => rfl), d, hd, hds, hdt, (fun _ => rfl),
    globalChartOrientation K d hd hds,
    fun B => globalChartOrientation_positive K d hd hds B⟩
end P202.GlobalGaussBonnet

/-! Assembly for the actual region decomposition. -/

/-! Proposed helper for the g26 draft. The regional geometric identities are
proof-internal premises; Euler and intrinsic area localization are actual
proved upstream results for the same decomposition. -/
open Set MeasureTheory
open scoped Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData

namespace P202.GlobalGaussBonnet
open P202.MetricData P202.ConnectionData P202.CurvatureData
  P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.SurfaceRegionsEuler P202Specs.EulerPoincare

/-- Assemble local formulas on the actual planar models of one actual region
decomposition. The Euler characteristics of the planar carriers are transported
by the canonical coordinate homeomorphisms to the genuine component closures.
The area identity uses the canonical measure and nullity of this same graph. -/
theorem assemble_actual_region_formulas
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : RegionDecomposition S) (B : BoundaryPresentation g)
    (a b ε : Fin R.regionCount → ℝ)
    (hP : ∀ j, HomologyFiniteType ℚ (R.region j).carrier)
    (hlocal : ∀ j, a j + b j + ε j =
      2 * Real.pi * (topologicalEuler (R.region j).carrier (hP j) : ℝ))
    (hf : letI : MeasurableSpace M := borel M;
      ∀ j, IntegrableOn (gaussianCurvature g T) (regionClosure R j) μ)
    (harea : letI : MeasurableSpace M := borel M;
      ∀ j, a j = ∫ p in regionClosure R j, gaussianCurvature g T p ∂μ)
    (hboundary : ∑ j, b j = B.curvatureIntegral C)
    (hcorners : ∑ j, ε j = 2 * Real.pi *
      ((R.graph.edgeCount : ℝ) - (R.graph.vertexCount : ℝ))) :
    (letI : MeasurableSpace M := borel M;
      Integrable (gaussianCurvature g T) μ) ∧
      ∃ hS : HomologyFiniteType ℚ M,
        totalCurvature g T μ + B.curvatureIntegral C =
          2 * Real.pi * (topologicalEuler M hS : ℝ) := by
  letI : MeasurableSpace M := borel M;
  obtain ⟨hS, hD, heuler⟩ := P202.SurfaceRegionsEuler.eulerConclusionFromRegions R
  obtain ⟨hint, htotal⟩ := regionDecomposition_integral g μ hμ R
    (gaussianCurvature g T) hf
  refine ⟨hint, hS, ?_⟩
  apply assemble_region_identities
    (a := a) (b := b) (ε := ε)
    (χ := fun j => topologicalEuler (regionClosure R j) (hD j))
    (V := R.graph.vertexCount) (E := R.graph.edgeCount)
    (χS := topologicalEuler M hS)
  · intro j
    rw [P202.SurfaceRegionsEuler.regionEuler_model R j (hD j) (hP j)]
    exact hlocal j
  · change (∑ j, a j) = ∫ p, gaussianCurvature g T p ∂μ
    simpa only [harea] using htotal.symm
  · exact hboundary
  · exact hcorners
  · exact heuler

end P202.GlobalGaussBonnet


open Set
open scoped BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
namespace P202.GlobalGaussBonnet
open P202Specs.SurfaceRegionConstruction

/-- The existing valence convention equals the genuine number of star rays,
with the two incidences of a loop retained. -/
theorem valence_eq_graphStar_rayCount
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (G : EmbeddedGraph S)
    (v : Fin G.vertexCount) (g : GraphStar G (G.vertex v)) :
    valence G v = g.rayCount := by
  classical
  have hcard : valence G v =
      {d : Fin G.edgeCount × Bool |
        (if d.2 then G.terminal d.1 else G.initial d.1) = v}.ncard := by
    simp [valence, halfEdgeVertex, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  exact hcard.trans
    (P202.SurfaceRegionConstruction.BoundaryCycles.graphStar_incidence_ncard G v g)
end P202.GlobalGaussBonnet

/-! The actual chart-restricted Levi–Civita geometry. -/

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.MapData SmoothManifolds.TensorData
open P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
open P202.SurfaceBoundaryData
open Set
namespace P202.GlobalGaussBonnet
variable {a b : SmoothManifolds.ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 a M} {W : SmoothManifold 2 b N}

theorem localIsometry_gaussianCurvature (f : M → N)
    (hf : IsLocalDiffeomorphism S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (p : M) :
    P202Specs.GlobalGaussBonnet.gaussianCurvature g R p =
      P202Specs.GlobalGaussBonnet.gaussianCurvature h R' (f p) := by
  obtain ⟨E, hE⟩ := SmoothManifolds.Tensors.local_diffeomorphism_differential S W f hf
  have hLE : L p = (E p).toLinearMap :=
    (SmoothManifolds.differential_exists S W f hf.1 p).unique (hL p) (hE p)
  let bs := referenceBasis g p
  let bt := bs.map (E p)
  have hbt (i : Fin 2) : bt i = L p (bs i) := by
    change (E p) (bs i) = L p (bs i)
    rw [hLE]
    rfl
  rw [gaussianCurvature_eq_basis g C hC R hR p bs,
    gaussianCurvature_eq_basis h K hK R' hR' (f p) bt]
  simp only [hbt]
  rw [localIsometry_curvatureForm f hf L hL g h hm C K hC hK R R' hR hR' p
    (bs 0) (bs 1) (bs 1) (bs 0), hm p (bs 0) (bs 0),
    hm p (bs 1) (bs 1), hm p (bs 0) (bs 1)]
end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.OrientationData SmoothManifolds.BundleOperationsData
/-- Every Euclidean-model chart has its own positively oriented Riemannian
geometry, without an orientation on the original surface. The local connection
and curvature tensor are constructed by their genuine existence theorems. -/
theorem exists_orientedChartGeometry
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (e : ModelChart 2 .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hne : e.source.Nonempty) :
    ∃ Q : SmoothManifold 2 .euclidean e.source,
      ∃ i : SmoothImmersion Q S Subtype.val,
        ∃ h : RiemannianMetric Q,
          ∃ CQ : Connection (tangentBundle Q), IsLeviCivita h CQ ∧
            ∃ RQ : CurvatureTensor Q, RepresentsCurvature CQ RQ ∧
              IsLocalIsometry h g Subtype.val ∧
              IsMetricPreserving h g Subtype.val i.differential ∧
              (∀ p, P202Specs.GlobalGaussBonnet.gaussianCurvature h RQ p =
                P202Specs.GlobalGaussBonnet.gaussianCurvature g R p.val) ∧
              ∃ d : ModelChart 2 .euclidean e.source,
                ∃ hd : d ∈ Q.smoothStructure.val,
                  d.source = univ ∧ d.target = e.target ∧ (∀ p, d p = e p.val) ∧
                  ∃ o : Orientation Q, ∀ B : CotangentBundle Q,
                    P202Specs.ChartRegionStokes.PositiveChart B o d hd := by
  obtain ⟨Q, i, h, hi, hm, d, hd, hs, ht, hv, o, ho⟩ :=
    exists_orientedChartLocalIsometry S g e he hne
  obtain ⟨CQ, hCQ, _⟩ := P202.Geometry.LeviCivita.exists_unique h
  obtain ⟨RQ, hRQ, _⟩ := P202.Geometry.CurvatureAlgebra.tensor_exists_unique CQ
  refine ⟨Q, i, h, CQ, hCQ, RQ, hRQ, hi, hm, ?_, d, hd, hs, ht, hv, o, ho⟩
  intro p
  exact localIsometry_gaussianCurvature Subtype.val hi.1 i.differential i.isDifferential
    h g hm CQ C hCQ hC RQ R hRQ hR p
end P202.GlobalGaussBonnet

/-! The complete empty-surface conclusion. -/
open Set MeasureTheory
open scoped Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurvatureData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet P202Specs.EulerPoincare
namespace P202.GlobalGaussBonnet
/-- The complete empty-surface instance of the original conclusion. -/
theorem globalGaussBonnet_empty
    {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M] [IsEmpty M]
    (S : SmoothManifold 2 kind M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) :
    Nonempty (BoundaryPresentation g) ∧
      ∃ μ : @Measure M (borel M), IsAreaMeasure g μ ∧
        (letI : MeasurableSpace M := borel M; Integrable (gaussianCurvature g T) μ) ∧
        ∀ B : BoundaryPresentation g,
          (∀ i, IntervalIntegrable (B.curvatureIntegrand C i) volume
            (B.arc i).left (B.arc i).right) ∧
          ∃ h : HomologyFiniteType ℚ M,
            totalCurvature g T μ + B.curvatureIntegral C =
              2 * Real.pi * (topologicalEuler M h : ℝ) := by
  have hBoundary : SmoothManifolds.BoundaryData.intrinsicBoundary S = ∅ :=
    Set.eq_empty_of_isEmpty _
  obtain ⟨R, hS, hD, heuler⟩ := P202.SurfaceRegionsEuler.surfaceRegionsEuler S
  obtain ⟨hV, hE, hR⟩ := R.empty_case inferInstance
  haveI : IsEmpty (Fin R.regionCount) := by rw [hR]; infer_instance
  have hχ : topologicalEuler M hS = 0 := by simpa [hV, hE] using heuler
  obtain ⟨μ, hμ, _⟩ := exists_unique_areaMeasure g
  refine ⟨⟨emptyBoundaryPresentation g hBoundary⟩, μ, hμ,
    integrable_gaussianCurvature g C hC T hT μ hμ, ?_⟩
  intro B
  have hc := boundaryPresentation_count_zero g B hBoundary
  haveI : IsEmpty (Fin B.count) := by rw [hc]; infer_instance
  refine ⟨fun i => isEmptyElim i, hS, ?_⟩
  rw [boundaryCurvatureIntegral_eq_zero g B C hBoundary, hχ]
  letI : MeasurableSpace M := borel M
  simp [totalCurvature, MeasureTheory.Measure.eq_zero_of_isEmpty μ]
end P202.GlobalGaussBonnet

/-! Boundary curvature integrability for every permitted presentation. -/
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open Set Filter
open scoped _root_.Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.BundleOperationsData SmoothManifolds.MapData SmoothManifolds.FrameData
open P202.MetricData P202.SurfaceBoundaryData P202.ConnectionData
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem covector_eval_coordinates (i : TangentIndex S) (p : M)
    (hp : p ∈ (tangentBundle S).baseSet i)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) (V : TangentSpace S p) :
    ℓ V = ∑ j : Fin 2, ((cotangentBundle S).trivialization i ⟨p, ℓ⟩).2 j *
      ((tangentBundle S).trivialization i ⟨p, V⟩).2 j := by
  let B := tangentBundle S
  let E := B.fiberCoordinates i p hp
  have hvec : V = ∑ j : Fin 2, (E V) j • E.symm (Pi.single j 1) := by
    simpa using
      (congrArg E.symm ((Pi.basisFun ℝ (Fin 2)).sum_equivFun (E V))).symm
  conv_lhs => rw [hvec, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, (cotangentDual S).coordinates i p hp]
  rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
  exact mul_comm _ _
 theorem covector_withinVelocity_continuousWithinAt {c : ℝ → M} {J : Set ℝ}
    (hc : P202.CurveData.CoordinateC1On S c J) (hc' : ContinuousOn c J)
    (hJ : UniqueDiffOn ℝ J) {t : ℝ} (ht : t ∈ J)
    (ω : (p : M) → Module.Dual ℝ (TangentSpace S p))
    (hω : ManifoldSmoothAt S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
      (fun p => (⟨p, ω p⟩ : Bundle.TotalSpace (Euclidean 2)
        (fun p => Module.Dual ℝ (TangentSpace S p)))) (c t)) :
    ContinuousWithinAt (fun s => ω (c s)
      (P202.Geometry.PiecewiseCurves.withinVelocity S c J s)) J t := by
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hc t ht
  let B := tangentBundle S
  let i : TangentIndex S := ⟨e, he⟩
  have hi : c t ∈ B.baseSet i := by
    change c t ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hp
  let D := derivWithin (fun s => (e (c s)).val) J
  have hD : ContinuousWithinAt D J t :=
    P202.Geometry.PiecewiseCurves.coordinate_derivWithin_continuousWithinAt hJ ht hx heq
  let W : M → Euclidean 2 := fun p => ((cotangentBundle S).trivialization i ⟨p, ω p⟩).2
  have hW : ContinuousWithinAt (fun s => W (c s)) J t :=
    (SmoothManifolds.SectionExtension.coordinates_smoothAt (cotangentBundle S) i
      (by rw [(cotangentDual S).baseSet]; exact hi) hω).1.comp_continuousWithinAt (hc' t ht)
  have hsum : ContinuousWithinAt (fun s => ∑ j : Fin 2, W (c s) j * D s j) J t := by
    apply tendsto_finsetSum
    intro j _
    exact ((continuous_apply j).continuousAt.comp_continuousWithinAt hW).mul
      ((continuous_apply j).continuousAt.comp_continuousWithinAt hD)
  apply hsum.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [(hc' t ht).eventually (e.open_source.mem_nhds hp), self_mem_nhdsWithin]
    with s hse hsJ
  have hsB : c s ∈ B.baseSet i := by
    change c s ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hse
  have hcoord : ((B.trivialization i) ⟨c s,
      P202.Geometry.PiecewiseCurves.withinVelocity S c J s⟩).2 = D s := by
    rw [(tangentRealization S).coordinates i (c s) hse]
    exact P202.Geometry.PiecewiseCurves.withinVelocity_coordinates hc hc' hJ hsJ e he hse
  rw [covector_eval_coordinates i (c s) hsB, hcoord]
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem covector_eval_smoothAt (g : RiemannianMetric S)
    (ω : (p : M) → Module.Dual ℝ (TangentSpace S p))
    (F : (p : M) → TangentSpace S p) (p : M)
    (hω : ManifoldSmoothAt S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
      (fun p => (⟨p, ω p⟩ : Bundle.TotalSpace (Euclidean 2)
        (fun p => Module.Dual ℝ (TangentSpace S p)))) p)
    (hF : ManifoldSmoothAt S.smoothStructure.val (tangentBundle S).totalManifold.smoothStructure.val
      (fun p => (⟨p, F p⟩ : Bundle.TotalSpace (Euclidean 2) (TangentSpace S))) p) :
    VectorSmoothAt S.smoothStructure.val (fun q => ω q (F q)) p := by
  let V : (q : M) → TangentSpace S q := fun q =>
    (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g q).symm (ω q)
  have hV : ManifoldSmoothAt S.smoothStructure.val (tangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, V q⟩ : Bundle.TotalSpace (Euclidean 2) (TangentSpace S))) p :=
    SmoothManifolds.manifoldContDiffAt_comp
      (cotangentBundle S).totalManifold.smoothStructure.property.1.1
      hω ((SmoothManifolds.MetricSplittings.metricIso (tangentBundle S) g (cotangentDual S)).inverse_smooth _)
  have hid := SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p
  have hQ := P202.Geometry.SmoothMetrics.metric_pairing_smoothAt S
    (tangentBundle S) g id V F p hid hV hF
  apply hQ.congr
  exact Eventually.of_forall (fun q =>
    congrArg (fun ℓ : Module.Dual ℝ (TangentSpace S q) => ℓ (F q))
      ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g q).apply_symm_apply (ω q)))
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
open P202.CurveConnectionData SmoothManifolds.BundleData
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem c1_derivWithin_continuousWithinAt {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    {t : ℝ} (ht : t ∈ J) {f v : ℝ → Euclidean 2}
    (hv : ContDiffAt ℝ 1 v t) (heq : f =ᶠ[𝓝[J] t] v) :
    ContinuousWithinAt (derivWithin f J) J t := by
  have hvd : ContDiffAt ℝ 0 (deriv v) t := hv.derivWithin (by norm_num)
  refine hvd.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [heq.derivWithin, (hv.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hvs hsJ
  exact hs.trans ((hvs.differentiableAt (by simp)).derivWithin (hJ s hsJ))
 theorem covector_covariantDerivativeWithin_continuousWithinAt
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    {c : ℝ → M} {J : Set ℝ}
    (hc : P202.CurveData.CoordinateC1On S c J) (hc' : ContinuousOn c J)
    (hJ : UniqueDiffOn ℝ J) (f : (t : ℝ) → TangentSpace S (c t))
    (hf : C1FieldOn (B := tangentBundle S) c f J)
    {t : ℝ} (ht : t ∈ J) (ω : (p : M) → Module.Dual ℝ (TangentSpace S p))
    (hω : ManifoldSmoothAt S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
      (fun p => (⟨p, ω p⟩ : Bundle.TotalSpace (Euclidean 2)
        (fun p => Module.Dual ℝ (TangentSpace S p)))) (c t)) :
    ContinuousWithinAt (fun s => ω (c s) (covariantDerivativeWithin C c f J s)) J t := by
  obtain ⟨U, hU, b, hp, v, hv, hval, heq⟩ := hf t ht
  let cf := coefficientsAlong b c f
  let df := derivWithin cf J
  let V := P202.Geometry.PiecewiseCurves.withinVelocity S c J
  let Γ (i j : Fin 2) : (p : M) → Module.Dual ℝ (TangentSpace S p) :=
    SmoothManifolds.SectionExtension.totalSection (fun p : U => connectionForm C b p i j)
  let A (i : Fin 2) : M → ℝ := fun q => ω q
    (SmoothManifolds.SectionExtension.totalSection (b.section_ i) q)
  have hcf : ContinuousWithinAt cf J t :=
    hv.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem heq ht
  have hdf : ContinuousWithinAt df J t := c1_derivWithin_continuousWithinAt hJ ht hv heq
  have hΓ (i j : Fin 2) : ContinuousWithinAt (fun s => Γ i j (c s) (V s)) J t :=
    covector_withinVelocity_continuousWithinAt hc hc' hJ ht (Γ i j)
      (P202.Geometry.ConnectionForms.connectionForm_smooth (tangentBundle S) C hU b i j (c t) hp)
  have hA (i : Fin 2) : ContinuousWithinAt (fun s => A i (c s)) J t :=
    (covector_eval_smoothAt g ω _ (c t) hω
      (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU
        (b.section_ i) (b.smooth i) (c t) hp)).1.comp_continuousWithinAt (hc' t ht)
  have hsum : ContinuousWithinAt
      (fun s => ∑ i : Fin 2, A i (c s) *
        (df s i + ∑ j : Fin 2, Γ i j (c s) (V s) * cf s j)) J t := by
    apply tendsto_finsetSum
    intro i _
    apply (hA i).mul
    apply ((continuous_apply i).continuousAt.comp_continuousWithinAt hdf).add
    apply tendsto_finsetSum
    intro j _
    exact (hΓ i j).mul ((continuous_apply j).continuousAt.comp_continuousWithinAt hcf)
  apply hsum.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [(hc' t ht).eventually (hU.mem_nhds hp), self_mem_nhdsWithin]
    with s hsU hsJ
  have hDs := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_spec C
    (P202.Geometry.CurveCovariantDerivative.exists_covariantDerivative C hsJ hc hc' hf)
  obtain ⟨v', hv'⟩ := P202.Geometry.CurveCovariantDerivative.exists_coefficients_deriv C hsJ hDs b hsU
  have hvd : df s = v' := hv'.derivWithin (hJ s hsJ)
  have hVs := P202.Geometry.PiecewiseCurves.withinVelocity_spec hc hc' hsJ
  have hformula := P202.Geometry.CurveCovariantDerivative.local_formula C hsJ (hJ s hsJ)
    hDs b hsU hVs hv'
  rw [hformula]
  unfold frameDerivative
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  rw [← hvd]
  simp only [A, Γ, SmoothManifolds.SectionExtension.totalSection_of_mem _ (c s) hsU,
    b.basis_eq, cf, df, V, mul_comm, connectionMatrix]
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
open P202Specs.GlobalGaussBonnet P202.CurveConnectionData
open SmoothManifolds.MapData
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 def intrinsicNormal (g : RiemannianMetric S) (p : M) : TangentSpace S p := by
  classical
  exact if hp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S then
    boundaryNormal g (P202.GlobalGaussBonnet.existsBoundarySideAt hp).some else 0
 theorem intrinsicNormal_eq (g : RiemannianMetric S) {p : M}
    (hp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) univ p) : intrinsicNormal g p = boundaryNormal g b := by
  rw [intrinsicNormal, dite_eq_left hp]
  exact P202.GlobalGaussBonnet.boundaryNormal_eq g hp b _
 theorem arc_points_in_boundary (g : RiemannianMetric S) (B : BoundaryPresentation g)
    (i : Fin B.count) {t : ℝ} (ht : t ∈ Icc (B.arc i).left (B.arc i).right) :
    (B.arc i).curve t ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S := by
  rw [B.covers]
  exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
 theorem regularArc_covariantDerivativeWithin_eq (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (c : RegularArc g) {t : ℝ}
    (ht : t ∈ Ioo c.left c.right) :
    covariantDerivativeWithin C c.curve c.tangent (Icc c.left c.right) t =
      covariantDerivative C c.curve c.tangent t := by
  have hI := Icc_mem_nhds ht.1 ht.2
  have htcc : t ∈ Icc c.left c.right := ⟨ht.1.le, ht.2.le⟩
  have hd := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_spec C
    (P202.Geometry.CurveCovariantDerivative.exists_covariantDerivative C htcc
      c.coordinateC1 c.continuous c.unitC1)
  have hfull : HasCovariantDerivativeAt C c.curve c.tangent t
      (covariantDerivativeWithin C c.curve c.tangent (Icc c.left c.right) t) := by
    obtain ⟨V, hV, U, hU, b, hp, v', hv, he⟩ := hd
    refine ⟨V, ?_, U, hU, b, hp, v', (hv.hasDerivAt hI).hasDerivWithinAt, he⟩
    obtain ⟨hc, e, he, hp, hd⟩ := hV
    exact ⟨(hc.continuousAt hI).continuousWithinAt,
      e, he, hp, (hd.hasDerivAt hI).hasDerivWithinAt⟩
  exact (P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (mem_univ _) uniqueDiffWithinAt_univ hfull).symm
 theorem boundary_curvatureIntegrand_integrable (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (B : BoundaryPresentation g) (i : Fin B.count) :
    IntervalIntegrable (B.curvatureIntegrand C i) MeasureTheory.volume
      (B.arc i).left (B.arc i).right := by
  let c := B.arc i
  let J := Icc c.left c.right
  let F : ℝ → ℝ := fun t => pairing g (c.curve t)
    (covariantDerivativeWithin C c.curve c.tangent J t)
    (intrinsicNormal g (c.curve t))
  have hF : ContinuousOn F J := by
    intro t ht
    have hbt := arc_points_in_boundary g B i ht
    cases kind with
    | euclidean =>
      change c.curve t ∈ SmoothManifolds.intrinsicBoundary S at hbt
      rw [SmoothManifolds.intrinsicBoundary_euclidean S] at hbt
      exact False.elim hbt
    | halfSpace =>
      obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c.curve t)
      let N : (q : M) → TangentSpace S q := fun q => normalVector g q
        (scalarDerivative S (fun y => (e y).val (Fin.last 1)) q)
      let ω : (q : M) → Module.Dual ℝ (TangentSpace S q) := fun q =>
        SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g q (N q)
      have hN := P202.GlobalGaussBonnet.coordinate_normalVector_smoothAt g e he (c.curve t) hp (Fin.last 1)
      have hω : ManifoldSmoothAt S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
          (fun q => (⟨q, ω q⟩ : Bundle.TotalSpace (Euclidean 2)
            (fun q => Module.Dual ℝ (TangentSpace S q)))) (c.curve t) :=
        SmoothManifolds.manifoldContDiffAt_comp
          (tangentBundle S).totalManifold.smoothStructure.property.1.1 hN
          ((SmoothManifolds.MetricSplittings.metricIso (tangentBundle S) g (cotangentDual S)).smooth _)
      have hcont := P202.GlobalGaussBonnet.covector_covariantDerivativeWithin_continuousWithinAt
        g C c.coordinateC1 c.continuous (uniqueDiffOn_Icc c.ordered) c.tangent c.unitC1 ht ω hω
      apply hcont.congr_of_eventuallyEq_of_mem _ ht
      filter_upwards [(c.continuous t ht).eventually (e.open_source.mem_nhds hp), self_mem_nhdsWithin]
        with s hsE hsJ
      have hbs := arc_points_in_boundary g B i hsJ
      have hnormal := intrinsicNormal_eq g hbs
        (P202.GlobalGaussBonnet.chartBoundarySideAt e he (c.curve s) hsE hbs)
      change pairing g (c.curve s) _ _ = ω (c.curve s) _
      rw [hnormal]
      exact g.symmetric _ _ _
  apply (hF.intervalIntegrable_of_Icc c.ordered.le).congr_uIoo
  rw [uIoo_of_le c.ordered.le]
  intro t ht
  rw [P202.GlobalGaussBonnet.boundary_curvatureIntegrand_eq g B C i t ht]
  dsimp only [F]
  rw [regularArc_covariantDerivativeWithin_eq g C c ht,
    intrinsicNormal_eq g (arc_points_in_boundary g B i (Ioo_subset_Icc_self ht)) (B.side i t ht)]
end P202.GlobalGaussBonnet

/-! Finite genuine boundary intervals. -/

open Set Filter Topology
open scoped BigOperators ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BoundaryData SmoothManifolds.TangentData
  SmoothManifolds.MapData SmoothManifolds.MapClassData

namespace P202.GlobalGaussBonnet
open P202Specs.SurfaceRegionConstruction P202.SurfaceRegionConstruction

/-- The genuine intrinsic boundary has a finite embedded interval graph;
all edge parameters, including endpoints, admit smooth regular coordinate
germs in every original surface chart. -/
theorem exists_regular_boundary_graph
    {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) :
    ∃ G : EmbeddedGraph S, G.carrier = intrinsicBoundary S ∧
      ∀ i, RegularCoordinateGerms S (G.edge i) := by
  classical
  haveI : T2Space M := S.topologicalManifold.hausdorff
  obtain ⟨B, hBS, hB⟩ := SmoothManifolds.exists_boundary_smoothManifold S
  have hEmb := SmoothManifolds.TransversePreimage.natural_boundary_embedding S B ⟨hBS,hB⟩
  letI : CompactSpace (intrinsicBoundary S) :=
    isCompact_iff_compactSpace.mp (SmoothManifolds.isClosed_intrinsicBoundary S).isCompact
  let K : Unit → Set M := fun _ => intrinsicBoundary S
  let curves : ∀ i, SmoothManifold 1 .euclidean (K i) := fun _ => B
  letI : ∀ i, CompactSpace (K i) := fun _ => inferInstance
  obtain ⟨G, hG, _, _, _, hgerms⟩ := embeddedGraph_of_finite_smooth_curves
    S K curves (fun _ => hBS) (fun _ => hEmb.2.2.1) (by
      intro i j hij
      exact False.elim (hij (Subsingleton.elim i j)))
  refine ⟨G, ?_, hgerms⟩
  simpa only [K, iUnion_const] using hG

/-- Genuine smooth regular coordinate jets of a closed graph interval,
expressed in the actual Euclidean coordinates used by intrinsic velocities.
The curve is clamped outside [0,1], but jets are compared only within [0,1]. -/
theorem regularCoordinateGerms_smoothJet
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {c : C(unitInterval, M)}
    (h : RegularCoordinateGerms S c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ e, ∃ he : e ∈ S.smoothStructure.val,
      IccExtend zero_le_one c t ∈ e.source ∧
      ∃ x : ℝ → Euclidean 2, ContDiffAt ℝ ∞ x t ∧ deriv x t ≠ 0 ∧
        x t = (e (IccExtend zero_le_one c t)).val ∧
        (fun s => (e (IccExtend zero_le_one c s)).val) =ᶠ[𝓝[Icc (0 : ℝ) 1] t] x := by
  let q : unitInterval := ⟨t, ht⟩
  have hct : IccExtend zero_le_one c t = c q := IccExtend_of_mem zero_le_one c ht
  obtain ⟨e, he, hqe⟩ := S.smoothStructure.property.1.1 (c q)
  obtain ⟨δ, F, hδ, hF, hFn, hrep⟩ := h q e he hqe
  have hFt : ContDiffAt ℝ ∞ F t := hF.contDiffAt
    (isOpen_Ioo.mem_nhds (by change t - δ < t ∧ t < t + δ; constructor <;> linarith))
  let x : ℝ → Euclidean 2 := fun s => toPlane.symm (F s)
  have hxd : HasDerivAt x (toPlane.symm (deriv F t)) t :=
    toPlane.symm.hasFDerivAt.comp_hasDerivAt t (hFt.differentiableAt (by simp)).hasDerivAt
  refine ⟨e, he, hct ▸ hqe, x,
    toPlane.symm.contDiff.contDiffAt.comp t hFt, ?_, ?_, ?_⟩
  · rw [hxd.deriv]
    intro hz
    apply hFn
    exact toPlane.symm.injective (by simpa using hz)
  · rw [hct]
    exact congrArg toPlane.symm (hrep q (by simpa [q] using hδ)).2
  · have hball : Metric.ball t δ ∈ 𝓝[Icc (0 : ℝ) 1] t :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)
    filter_upwards [hball, self_mem_nhdsWithin] with s hst hs
    rw [IccExtend_of_mem zero_le_one c hs]
    exact (congrArg toPlane.symm (hrep ⟨s, hs⟩ (by
      simpa only [Metric.mem_ball, Real.dist_eq] using hst)).2).symm

/-- Closed graph intervals with smooth coordinate germs are C¹ in the
original curve-calculus interface, including both endpoints. -/
theorem regularCoordinateGerms_coordinateC1
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {c : C(unitInterval, M)}
    (h : RegularCoordinateGerms S c) :
    P202.CurveData.CoordinateC1On S (IccExtend zero_le_one c) (Icc (0 : ℝ) 1) := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, _, hxt, heq⟩ := regularCoordinateGerms_smoothJet h ht
  exact ⟨e, he, hp, x, hx.of_le (by simp), hxt, heq⟩

/-- The canonical within velocity of a regular graph interval never vanishes,
including at its two endpoints. It gives the actual intrinsic velocity on
(0,1), rather than differentiating the clamping at the endpoints. -/
theorem regularCoordinateGerms_intrinsicVelocity
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {c : C(unitInterval, M)}
    (h : RegularCoordinateGerms S c) :
    (∀ t ∈ Icc (0 : ℝ) 1,
      P202.Geometry.PiecewiseCurves.withinVelocity S (IccExtend zero_le_one c)
        (Icc (0 : ℝ) 1) t ≠ 0) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1,
      P202.CurveData.HasVelocityAt S (IccExtend zero_le_one c) t
        (P202.Geometry.PiecewiseCurves.withinVelocity S (IccExtend zero_le_one c)
          (Icc (0 : ℝ) 1) t) := by
  let γ := IccExtend zero_le_one c
  have hc : Continuous γ := c.continuous.Icc_extend'
  have hC1 := regularCoordinateGerms_coordinateC1 h
  have hUD : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  constructor
  · intro t ht hz
    obtain ⟨e, he, hp, x, hx, hxn, hxt, heq⟩ := regularCoordinateGerms_smoothJet h ht
    have hv := P202.Geometry.PiecewiseCurves.withinVelocity_spec hC1 hc.continuousOn ht
    have hvd := P202.Geometry.PiecewiseCurves.hasVelocityWithinAt_coordinates hv ht e he hp
    have hxd := (hx.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem heq ht
    have hvx := (hvd.derivWithin (hUD t ht)).symm.trans (hxd.derivWithin (hUD t ht))
    rw [hz, map_zero] at hvx
    exact hxn hvx.symm
  · intro t ht
    have hvw := P202.Geometry.PiecewiseCurves.withinVelocity_spec hC1 hc.continuousOn
      ⟨ht.1.le, ht.2.le⟩
    obtain ⟨hvwcont, e, he, hp, hvwd⟩ := hvw
    refine ⟨hc.continuousAt, e, he, hp, ?_⟩
    exact hvwd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Removing finitely many marks from a smooth curve leaves a dense set.
This includes the empty curve and uses real chart neighborhoods directly. -/
theorem smoothCurve_finite_compl_dense
    {X : Type u} [TopologicalSpace X] (B : SmoothManifold 1 .euclidean X)
    (P : Set X) (hP : P.Finite) : Dense Pᶜ := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨b, hb, hxb⟩ := B.smoothStructure.property.1.1 x
  let e := CurveCuts.realChart b
  have hxe : x ∈ e.source := hxb
  have hV : IsOpen (e '' (U ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hU.inter e.open_source) inter_subset_right
  have hxV : e x ∈ e '' (U ∩ e.source) := ⟨x, ⟨hx,hxe⟩, rfl⟩
  have hVi := infinite_of_mem_nhds (e x) (hV.mem_nhds hxV)
  obtain ⟨y, hyV, hyP⟩ := (hVi.diff (hP.image e)).nonempty
  obtain ⟨z, ⟨hzU,hze⟩, rfl⟩ := hyV
  exact ⟨z, hzU, fun hzP => hyP ⟨z,hzP,rfl⟩⟩

/-- A finite interval graph whose carrier is the intrinsic boundary is covered
by its closed edge images alone. There are no isolated boundary vertices. -/
theorem boundaryGraph_edges_cover
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (G : EmbeddedGraph S)
    (hG : G.carrier = intrinsicBoundary S) :
    (⋃ i, range (G.edge i)) = intrinsicBoundary S := by
  haveI : T2Space M := S.topologicalManifold.hausdorff
  obtain ⟨B, _, _⟩ := SmoothManifolds.exists_boundary_smoothManifold S
  let P : Set (intrinsicBoundary S) := Subtype.val ⁻¹' range G.vertex
  have hP : P.Finite := (Set.finite_range G.vertex).preimage Subtype.val_injective.injOn
  have hD := smoothCurve_finite_compl_dense B P hP
  have hclosed : IsClosed (⋃ i, range (G.edge i)) :=
    (isCompact_iUnion (fun i => isCompact_range (G.edge i).continuous)).isClosed
  have hsub : ∀ x : intrinsicBoundary S, x ∈ Pᶜ → x.val ∈ ⋃ i, range (G.edge i) := by
    intro x hx
    have hxG : x.val ∈ G.carrier := by
      rw [hG]
      exact x.property
    exact hxG.resolve_left hx
  apply Set.Subset.antisymm
  · intro x hx
    rw [← hG]
    exact Or.inr hx
  · intro x hx
    exact hD.induction (P := fun y : intrinsicBoundary S =>
      y.val ∈ ⋃ i, range (G.edge i)) hsub
      (hclosed.preimage continuous_subtype_val) ⟨x,hx⟩

/-- The same interval germs give a continuous, strictly positive intrinsic
metric speed all the way to the endpoints. -/
theorem regularCoordinateGerms_speed
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {c : C(unitInterval, M)}
    (g : P202.MetricData.RiemannianMetric S) (h : RegularCoordinateGerms S c) :
    ContinuousOn (fun t => P202.MetricData.tangentNorm g (IccExtend zero_le_one c t)
      (P202.Geometry.PiecewiseCurves.withinVelocity S (IccExtend zero_le_one c)
        (Icc (0 : ℝ) 1) t)) (Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      0 < P202.MetricData.tangentNorm g (IccExtend zero_le_one c t)
        (P202.Geometry.PiecewiseCurves.withinVelocity S (IccExtend zero_le_one c)
          (Icc (0 : ℝ) 1) t) := by
  refine ⟨P202.Geometry.PiecewiseCurves.withinNorm_continuousOn g
    (regularCoordinateGerms_coordinateC1 h) c.continuous.Icc_extend'.continuousOn
    (uniqueDiffOn_Icc zero_lt_one), ?_⟩
  intro t ht
  have hn := (regularCoordinateGerms_intrinsicVelocity h).1 t ht
  exact lt_of_le_of_ne (P202.Geometry.SmoothMetrics.tangentNorm_nonneg _ _ _)
    (Ne.symm ((P202.Geometry.SmoothMetrics.tangentNorm_eq_zero_iff _ _ _).not.mpr hn))

end P202.GlobalGaussBonnet

/-! Normalized tangent regularity. -/
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open Set Filter
open scoped _root_.Topology BigOperators ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData P202.CurveConnectionData
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
 theorem smooth_scalar_pullback_of_coordinate_jet {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hc : ContinuousWithinAt c J t)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val) (hp : c t ∈ e.source)
    (x : ℝ → Euclidean 2) (hx : ContDiffAt ℝ ∞ x t)
    (hxt : x t = (e (c t)).val)
    (heq : (fun s => (e (c s)).val) =ᶠ[𝓝[J] t] x)
    (f : M → ℝ) (hf : VectorSmoothAt S.smoothStructure.val f (c t)) :
    ∃ F : ℝ → ℝ, ContDiffAt ℝ ∞ F t ∧ F t = f (c t) ∧
      (fun s => f (c s)) =ᶠ[𝓝[J] t] F := by
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := hf.2 e he hp
  refine ⟨G ∘ x, (hG.contDiffAt (hU.mem_nhds (hxt ▸ hpU))).comp t hx, ?_, ?_⟩
  · change G (x t) = f (c t)
    rw [hxt]
    exact heG.eq_of_nhds
  · filter_upwards [heq, heG.comp_tendsto hc] with s hs hGs
    exact hGs.symm.trans (congrArg G hs)
 theorem regularCoordinateGerms_unitC1
    {c : C(unitInterval, M)} (g : RiemannianMetric S)
    (h : P202.SurfaceRegionConstruction.RegularCoordinateGerms S c) :
    C1FieldOn (B := tangentBundle S) (IccExtend zero_le_one c)
      (unitTangent g (IccExtend zero_le_one c)
        (P202.Geometry.PiecewiseCurves.withinVelocity S (IccExtend zero_le_one c)
          (Icc (0 : ℝ) 1))) (Icc (0 : ℝ) 1) := by
  let γ := IccExtend zero_le_one c
  let J := Icc (0 : ℝ) 1
  let W := P202.Geometry.PiecewiseCurves.withinVelocity S γ J
  let B := tangentBundle S
  have hc : Continuous γ := c.continuous.Icc_extend'
  have hC1 := regularCoordinateGerms_coordinateC1 h
  have hUD : UniqueDiffOn ℝ J := uniqueDiffOn_Icc zero_lt_one
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxn, hxt, heq⟩ := regularCoordinateGerms_smoothJet h ht
  let i : TangentIndex S := ⟨e, he⟩
  have hi : γ t ∈ B.baseSet i := by
    change γ t ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hp
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  have hxd : ContDiffAt ℝ ∞ (deriv x) t := hx.derivWithin (by simp)
  have hx1 : ContDiffAt ℝ 1 x t := hx.of_le (by simp)
  let gram (j k : Fin 2) : M → ℝ := fun q =>
    g.form q ((B.trivialization i).symm q (Pi.single j 1))
      ((B.trivialization i).symm q (Pi.single k 1))
  have hGrams (j k : Fin 2) : ∃ F : ℝ → ℝ,
      ContDiffAt ℝ ∞ F t ∧ F t = gram j k (γ t) ∧
        (fun s => gram j k (γ s)) =ᶠ[𝓝[J] t] F :=
    smooth_scalar_pullback_of_coordinate_jet (S := S) hc.continuousAt.continuousWithinAt
      e he hp x hx hxt heq (gram j k) (g.smooth i j k (γ t) hi)
  choose G hG hGt hGrep using hGrams
  let Q : ℝ → ℝ := fun s => ∑ j : Fin 2, ∑ k : Fin 2,
    deriv x s j * (deriv x s k * G j k s)
  have hQ : ContDiffAt ℝ ∞ Q t := by
    apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.sum
    intro k _
    exact ((contDiffAt_pi.mp hxd j).mul ((contDiffAt_pi.mp hxd k).mul (hG j k)))
  have hcoordt : B.fiberCoordinates i (γ t) hi (W t) = deriv x t := by
    have hw := P202.Geometry.PiecewiseCurves.withinVelocity_spec hC1 hc.continuousOn ht
    have hwd := P202.Geometry.PiecewiseCurves.hasVelocityWithinAt_coordinates hw ht e he hp
    have hxd' := (hx.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem heq ht
    rw [SmoothVectorBundle.fiberCoordinates_apply, (tangentRealization S).coordinates i (γ t) hp]
    exact (hwd.derivWithin (hUD t ht)).symm.trans (hxd'.derivWithin (hUD t ht))
  have hQt : Q t = pairing g (γ t) (W t) (W t) := by
    have hbil := P202.Geometry.SmoothMetrics.bilinear_coordinates
      (B.fiberCoordinates i (γ t) hi) (g.form (γ t)) (W t) (W t)
    simp only [SmoothVectorBundle.fiberCoordinates_symm_apply, hcoordt] at hbil
    simpa only [Q, hGt, gram, P202.MetricData.pairing] using hbil.symm
  have hwne : W t ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hcoordt
    exact hxn hcoordt.symm
  have hQpos : 0 < Q t := hQt ▸ g.positive (γ t) (W t) hwne
  let v : ℝ → Euclidean 2 := fun s => (Real.sqrt (Q s))⁻¹ • deriv x s
  have hv : ContDiffAt ℝ 1 v t :=
    (((hQ.sqrt (ne_of_gt hQpos)).inv (ne_of_gt (Real.sqrt_pos.mpr hQpos))).smul hxd).of_le (by simp)
  refine ⟨B.baseSet i, _, b, hi, v, hv, ?_, ?_⟩
  · have hb : (b.basis ⟨γ t, hi⟩).equivFun = B.fiberCoordinates i (γ t) hi := by
      change ((Pi.basisFun ℝ (Fin 2)).map (B.fiberCoordinates i (γ t) hi).symm).equivFun = _
      simp
    rw [P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem b _ _ t hi, hb]
    change (B.fiberCoordinates i (γ t) hi) ((tangentNorm g (γ t) (W t))⁻¹ • W t) = _
    rw [map_smul, hcoordt]
    change _ = (Real.sqrt (Q t))⁻¹ • deriv x t
    rw [hQt]
    rfl
  · have hDrep : derivWithin (fun s => (e (γ s)).val) J =ᶠ[𝓝[J] t] deriv x := by
      filter_upwards [heq.derivWithin, (hx1.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs hxs hsJ
      exact hs.trans ((hxs.differentiableAt (by simp)).derivWithin (hUD s hsJ))
    have hGs : ∀ᶠ s in 𝓝[J] t, ∀ j k, gram j k (γ s) = G j k s := by
      exact Filter.eventually_all.mpr (fun j => Filter.eventually_all.mpr (fun k => hGrep j k))
    filter_upwards [hDrep, hGs, (hc.continuousAt.continuousWithinAt).eventually
      (e.open_source.mem_nhds hp), self_mem_nhdsWithin] with s hsD hsG hsE hsJ
    have hsB : γ s ∈ B.baseSet i := by
      change γ s ∈ (tangentRealization S).space.bundle.baseSet i
      rw [(tangentRealization S).baseSet]
      exact hsE
    have hcoords : B.fiberCoordinates i (γ s) hsB (W s) = deriv x s := by
      rw [SmoothVectorBundle.fiberCoordinates_apply, (tangentRealization S).coordinates i (γ s) hsE]
      exact (P202.Geometry.PiecewiseCurves.withinVelocity_coordinates hC1 hc.continuousOn hUD hsJ e he hsE).trans hsD
    have hQs : Q s = pairing g (γ s) (W s) (W s) := by
      have hbil := P202.Geometry.SmoothMetrics.bilinear_coordinates
        (B.fiberCoordinates i (γ s) hsB) (g.form (γ s)) (W s) (W s)
      simp only [SmoothVectorBundle.fiberCoordinates_symm_apply, hcoords] at hbil
      simpa only [Q, ← hsG, gram, P202.MetricData.pairing] using hbil.symm
    have hb : (b.basis ⟨γ s, hsB⟩).equivFun = B.fiberCoordinates i (γ s) hsB := by
      change ((Pi.basisFun ℝ (Fin 2)).map (B.fiberCoordinates i (γ s) hsB).symm).equivFun = _
      simp
    rw [P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem b _ _ s hsB, hb]
    change (B.fiberCoordinates i (γ s) hsB) ((tangentNorm g (γ s) (W s))⁻¹ • W s) = _
    rw [map_smul, hcoords]
    change _ = (Real.sqrt (Q s))⁻¹ • deriv x s
    rw [hQs]
    rfl
end P202.GlobalGaussBonnet

/-! Actual finite boundary presentations. -/

open Set Filter Topology
open scoped BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BoundaryData
namespace P202.GlobalGaussBonnet
open P202Specs.SurfaceRegionConstruction P202.SurfaceRegionConstruction
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData P202Specs.GlobalGaussBonnet
open P202.Geometry.PiecewiseCurves

variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Convert a genuinely regular closed graph interval to the original
metric arc object, using the proved normalized-velocity C¹ calculation. -/
def regularArcOfGerms (g : RiemannianMetric S) (c : C(unitInterval, M))
    (h : RegularCoordinateGerms S c) : RegularArc g where
  left := 0
  right := 1
  ordered := zero_lt_one
  curve := IccExtend zero_le_one c
  velocity := withinVelocity S (IccExtend zero_le_one c) (Icc (0 : ℝ) 1)
  hasVelocity := (regularCoordinateGerms_intrinsicVelocity h).2
  regular := (regularCoordinateGerms_intrinsicVelocity h).1
  coordinateC1 := regularCoordinateGerms_coordinateC1 h
  continuous := c.continuous.Icc_extend'.continuousOn
  unitC1 := regularCoordinateGerms_unitC1 g h

lemma clampedArc_image_Icc (c : C(unitInterval, M)) :
    IccExtend zero_le_one c '' Icc (0 : ℝ) 1 = range c := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [IccExtend_of_mem zero_le_one c ht]
    exact mem_range_self _
  · rintro ⟨q, rfl⟩
    exact ⟨q.val, q.property, IccExtend_of_mem zero_le_one c q.property⟩

lemma clampedArc_image_Ioo (c : C(unitInterval, M)) :
    IccExtend zero_le_one c '' Ioo (0 : ℝ) 1 =
      c '' {q : unitInterval | 0 < (q : ℝ) ∧ (q : ℝ) < 1} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t,ht.1.le,ht.2.le⟩, ht,
      (IccExtend_of_mem zero_le_one c ⟨ht.1.le,ht.2.le⟩).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.val, hq, IccExtend_of_mem zero_le_one c q.property⟩

/-- The graph's actual multiplicity-one edge intervals give a complete
boundary presentation. Coverage includes every graph vertex; the normals
come from the proved original-surface boundary-side construction. -/
def boundaryPresentationOfGraph (g : RiemannianMetric S)
    (G : EmbeddedGraph S) (hG : G.carrier = intrinsicBoundary S)
    (hgerms : ∀ i, RegularCoordinateGerms S (G.edge i)) : BoundaryPresentation g where
  count := G.edgeCount
  arc := fun i => regularArcOfGerms g (G.edge i) (hgerms i)
  injective := by
    intro i s hs t ht hst
    have hst' : G.edge i ⟨s,hs.1.le,hs.2.le⟩ = G.edge i ⟨t,ht.1.le,ht.2.le⟩ := by
      simpa only [regularArcOfGerms, IccExtend_of_mem zero_le_one (G.edge i)
        ⟨hs.1.le,hs.2.le⟩, IccExtend_of_mem zero_le_one (G.edge i)
        ⟨ht.1.le,ht.2.le⟩] using hst
    exact congrArg Subtype.val (G.open_injective i hs ht hst')
  disjoint := by
    intro i j hij
    change Disjoint
      (IccExtend zero_le_one (G.edge i) '' Ioo (0 : ℝ) 1)
      (IccExtend zero_le_one (G.edge j) '' Ioo (0 : ℝ) 1)
    rw [clampedArc_image_Ioo, clampedArc_image_Ioo]
    exact G.disjoint_open_edges hij
  covers := by
    change intrinsicBoundary S = ⋃ i,
      IccExtend zero_le_one (G.edge i) '' Icc (0 : ℝ) 1
    simp_rw [clampedArc_image_Icc]
    exact (boundaryGraph_edges_cover G hG).symm
  side := by
    intro i t ht
    apply Classical.choice
    apply existsBoundarySideAt
    rw [← hG]
    apply Or.inr
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change IccExtend zero_le_one (G.edge i) t ∈ range (G.edge i)
    exact (IccExtend_range zero_le_one (G.edge i)).subset (mem_range_self t)

/-- Every compact smooth surface admits a genuine finite boundary arc
presentation, with either model and no connectedness, orientation or
nonemptiness assumption. -/
theorem exists_boundaryPresentation [CompactSpace M]
    (g : RiemannianMetric S) : Nonempty (BoundaryPresentation g) := by
  obtain ⟨G, hG, hgerms⟩ := exists_regular_boundary_graph S
  exact ⟨boundaryPresentationOfGraph g G hG hgerms⟩

end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open P202Specs.GlobalGaussBonnet P202.MetricData P202.ConnectionData P202.CurvatureData
/-- The genuine global area and boundary integrals exist with the full
regularity asserted in the original conclusion. The Gauss–Bonnet equality
is not part of this analytic existence statement. -/
theorem exists_global_integrals
    {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) :
    Nonempty (BoundaryPresentation g) ∧
      ∃ μ : @Measure M (borel M), IsAreaMeasure g μ ∧
        (letI : MeasurableSpace M := borel M; Integrable (gaussianCurvature g T) μ) ∧
        ∀ B : BoundaryPresentation g, ∀ i,
          IntervalIntegrable (B.curvatureIntegrand C i) volume
            (B.arc i).left (B.arc i).right := by
  obtain ⟨μ, hμ, _⟩ := exists_unique_areaMeasure g
  exact ⟨exists_boundaryPresentation g, μ, hμ,
    integrable_gaussianCurvature g C hC T hT μ hμ,
    fun B i => boundary_curvatureIntegrand_integrable g C B i⟩
end P202.GlobalGaussBonnet


/-! Continuation: Round3ChartArea. -/
section Round3ChartArea
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.TangentBundleData
open P202.MetricData P202.VolumeData
namespace P202.GlobalGaussBonnet
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}
/-- In matching chart coordinates, the actual differential is the identity
on coordinate vectors, for either model kind. -/
theorem differential_matching_coordinates
    (f : M → N) (hf : IsSmoothMap S W f) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : IsDifferential S W f p L)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (hp : p ∈ c.source) (hfp : f p ∈ d.source)
    (hcoord : (fun q => (c q).val) =ᶠ[𝓝 p] (fun q => (d (f q)).val))
    (K : FiberCoordinates S) (J : FiberCoordinates W) (v : TangentSpace S p) :
    J.equiv d hd (f p) hfp (L v) = K.equiv c hc p hp v := by
  have hh := SmoothManifolds.differential_jacobian S W f hf p L hL c d hc hd hp hfp
    (K.equiv c hc p hp) (J.equiv d hd (f p) hfp)
    (K.isCoordinates c hc p hp) (J.isCoordinates d hd (f p) hfp)
    univ id isOpen_univ (mem_univ _) contDiff_id.contDiffOn hcoord v
  simpa only [fderiv_id, ContinuousLinearMap.id_apply] using hh

/-- Metric-preserving maps with matching chart coordinates identify the actual
Gram matrices, including at genuine boundary points. -/
theorem metricPreserving_gramMatrix
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (p : c.source) (hfp : f p.val ∈ d.source)
    (hcoord : (fun q => (c q).val) =ᶠ[𝓝 p.val] (fun q => (d (f q)).val))
    (K : FiberCoordinates S) (J : FiberCoordinates W) :
    gramMatrix g K c hc p = gramMatrix h J d hd ⟨f p.val, hfp⟩ := by
  have hv (v : Euclidean n) :
      L p.val ((K.equiv c hc p.val p.property).symm v) =
        (J.equiv d hd (f p.val) hfp).symm v := by
    apply (J.equiv d hd (f p.val) hfp).injective
    rw [differential_matching_coordinates f hf p.val (L p.val) (hL p.val)
      c d hc hd p.property hfp hcoord K J, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  ext i j
  change pairing g p.val _ _ = pairing h (f p.val) _ _
  rw [← hm, hv, hv]
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
open P202Specs.LocalGaussBonnet
variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 .euclidean M} {W : SmoothManifold 2 .euclidean N}
/-- Matching chart maps transport the actual inverse coordinate points. -/
theorem chartPoint_map_matching_coordinates
    (f : M → N)
    (c : ModelChart 2 .euclidean M) (d : ModelChart 2 .euclidean N)
    (hs : ∀ p ∈ c.source, f p ∈ d.source)
    (hcoord : ∀ p ∈ c.source, d (f p) = c p)
    (x : P202Specs.PlanarRegionTopology.Plane)
    (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    f (chartPoint c x) = chartPoint d x := by
  have hp : chartPoint c x ∈ c.source := c.map_target hx
  have hd : d (f (chartPoint c x)) = P202Specs.ChartRegionStokes.modelPoint x := by
    rw [hcoord _ hp]
    exact c.right_inv hx
  exact (d.left_inv (hs _ hp)).symm.trans (congrArg d.symm hd)

/-- Chart density agrees under a metric-preserving map whose coordinate map
is the identity. This uses the actual differential and actual Gram matrices. -/
theorem metricPreserving_areaWeight
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : ModelChart 2 .euclidean M) (d : ModelChart 2 .euclidean N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (hs : ∀ p ∈ c.source, f p ∈ d.source)
    (hcoord : ∀ p ∈ c.source, d (f p) = c p)
    (x : P202Specs.PlanarRegionTopology.Plane)
    (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    areaWeight g c hc x = areaWeight h d hd x := by
  have hp : chartPoint c x ∈ c.source := c.map_target hx
  have heq := chartPoint_map_matching_coordinates f c d hs hcoord x hx
  have hx' : P202Specs.ChartRegionStokes.modelPoint x ∈ d.target := by
    have h := d.map_source (hs _ hp)
    rwa [hcoord _ hp, show c (chartPoint c x) = _ from c.right_inv hx] at h
  have hm' := metricPreserving_gramMatrix f hf L hL g h hm c d hc hd
    ⟨chartPoint c x, hp⟩ (hs _ hp)
    (by filter_upwards [c.open_source.mem_nhds hp] with q hq
        exact congrArg Subtype.val (hcoord q hq).symm)
    (tangentStructure S).fiberCoordinates (tangentStructure W).fiberCoordinates
  simp only [areaWeight, dite_eq_left hx, dite_eq_left hx']
  congr 1
  rw [hm']
  congr 2
  exact Subtype.ext heq
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
open P202Specs.LocalGaussBonnet
variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 .euclidean M} {W : SmoothManifold 2 .euclidean N}
/-- Density transport of any scalar curvature field already identified by
an actual geometric map. -/
theorem metricPreserving_curvatureIntegrand
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (R : P202.CurvatureData.CurvatureTensor S) (Q : P202.CurvatureData.CurvatureTensor W)
    (hcurv : ∀ p, P202Specs.LocalGaussBonnet.gaussianCurvature g R p =
      P202Specs.LocalGaussBonnet.gaussianCurvature h Q (f p))
    (c : ModelChart 2 .euclidean M) (d : ModelChart 2 .euclidean N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (hs : ∀ p ∈ c.source, f p ∈ d.source)
    (hcoord : ∀ p ∈ c.source, d (f p) = c p)
    (x : P202Specs.PlanarRegionTopology.Plane)
    (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    curvatureIntegrand g R c hc x = curvatureIntegrand h Q d hd x := by
  unfold curvatureIntegrand
  rw [hcurv, chartPoint_map_matching_coordinates f c d hs hcoord x hx,
    metricPreserving_areaWeight f hf L hL g h hm c d hc hd hs hcoord x hx]

/-- Integration over the same actual planar carrier transports the local
curvature integral, with no chosen orientation or measure certificate. -/
theorem metricPreserving_curvatureIntegral
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (R : P202.CurvatureData.CurvatureTensor S) (Q : P202.CurvatureData.CurvatureTensor W)
    (hcurv : ∀ p, P202Specs.LocalGaussBonnet.gaussianCurvature g R p =
      P202Specs.LocalGaussBonnet.gaussianCurvature h Q (f p))
    (c : ModelChart 2 .euclidean M) (d : ModelChart 2 .euclidean N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (hs : ∀ p ∈ c.source, f p ∈ d.source)
    (hcoord : ∀ p ∈ c.source, d (f p) = c p)
    (D : P202Specs.PlanarRegionTopology.PlanarRegion)
    (hD : D.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c) :
    curvatureIntegral g R c hc D = curvatureIntegral h Q d hd D := by
  apply MeasureTheory.setIntegral_congr_fun isClosed_closure.measurableSet
  intro x hx
  exact metricPreserving_curvatureIntegrand f hf L hL g h hm R Q hcurv
    c d hc hd hs hcoord x (hD hx)
end P202.GlobalGaussBonnet
end Round3ChartArea


/-! Continuation: Round3ChartConnections. -/
section Round3ChartConnections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.TangentBundleData
open SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData
open P202.MetricData P202.ConnectionData P202.LeviCivitaData
namespace P202.GlobalGaussBonnet
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}

/-- The canonical bundle vector in a chart is the inverse of its actual
coordinate differential, including at a face. -/
theorem coordinateVector_eq_chartCoordinates
    (c : TangentIndex S) (p : M) (hp : p ∈ c.val.source) (j : Fin n) :
    coordinateVector c j p =
      ((tangentStructure S).fiberCoordinates.equiv c.val c.property p hp).symm
        (Pi.single j 1) := by
  have hpb : p ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have he : (tangentBundle S).fiberCoordinates c p hpb =
      (tangentStructure S).fiberCoordinates.equiv c.val c.property p hp := by
    ext v i
    exact congrFun ((tangentRealization S).coordinates c p hp v) i
  rw [← he, SmoothVectorBundle.fiberCoordinates_symm_apply]
  rfl

/-- Matching coordinate frames are related by the actual differential. No
local inverse across a boundary seam is required. -/
theorem differential_coordinateVector
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (p : M) (hp : p ∈ c.val.source) (j : Fin n) :
    L p (coordinateVector c j p) = coordinateVector d j (f p) := by
  rw [coordinateVector_eq_chartCoordinates c p hp,
    coordinateVector_eq_chartCoordinates d (f p) (hs p hp)]
  apply ((tangentStructure W).fiberCoordinates.equiv d.val d.property (f p) (hs p hp)).injective
  rw [differential_matching_coordinates f hf p (L p) (hL p)
    c.val d.val c.property d.property hp (hs p hp)
    (by filter_upwards [c.val.open_source.mem_nhds hp] with q hq
        exact hcoord q hq)
    (tangentStructure S).fiberCoordinates (tangentStructure W).fiberCoordinates,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Actual coordinate-frame germs on the two manifolds are related. -/
theorem exists_related_coordinate_frames
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (p : M) (hp : p ∈ c.val.source) :
    ∃ (X : Fin n → Field S) (Y : Fin n → Field W),
      (∀ j, ∀ᶠ q in 𝓝 p, L q ((X j).val q) = (Y j).val (f q)) ∧
      (∀ j, (X j).val p = coordinateVector c j p) ∧
      (∀ j, (Y j).val (f p) = coordinateVector d j (f p)) := by
  have hpc : p ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hpd : f p ∈ (tangentBundle W).baseSet d :=
    (tangentRealization W).baseSet d ▸ hs p hp
  let bc := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let bd := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle W) d
  obtain ⟨X, hX⟩ := P202.Geometry.ConnectionForms.local_frame_representative
    (tangentBundle S) bc ⟨p, hpc⟩
  obtain ⟨Y, hY⟩ := P202.Geometry.ConnectionForms.local_frame_representative
    (tangentBundle W) bd ⟨f p, hpd⟩
  have hcO : IsOpen ((tangentBundle S).baseSet c) :=
    (tangentBundle S).trivialization_baseSet c ▸ ((tangentBundle S).trivialization c).open_baseSet
  have hdO : IsOpen ((tangentBundle W).baseSet d) :=
    (tangentBundle W).trivialization_baseSet d ▸ ((tangentBundle W).trivialization d).open_baseSet
  have hX' (j : Fin n) : ∀ᶠ q in 𝓝 p, (X j).val q = coordinateVector c j q := by
    filter_upwards [hX j, hcO.mem_nhds hpc] with q hq hqc
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hqc]
    exact P202.Geometry.LeviCivita.trivializationFrame_section c j ⟨q, hqc⟩
  have hY' (j : Fin n) : ∀ᶠ q in 𝓝 (f p), (Y j).val q = coordinateVector d j q := by
    filter_upwards [hY j, hdO.mem_nhds hpd] with q hq hqd
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hqd]
    exact P202.Geometry.LeviCivita.trivializationFrame_section d j ⟨q, hqd⟩
  refine ⟨X, Y, ?_, fun j => (hX' j).self_of_nhds, fun j => (hY' j).self_of_nhds⟩
  intro j
  filter_upwards [hX' j, (hf p).1.eventually (hY' j), c.val.open_source.mem_nhds hp]
    with q hXq hYq hq
  rw [hXq, hYq]
  exact differential_coordinateVector f hf L hL c d hs hcoord q hq j
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}
/-- Levi–Civita connections are related under a metric-preserving map in
matching full-dimensional coordinates. This remains valid when the source
has a true boundary and the target is an ambient extension across its seam. -/
theorem matchingChart_connection_related_at
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (X Y : Field S) (X' Y' : Field W) (p : M) (hp : p ∈ c.val.source)
    (hX : ∀ᶠ q in 𝓝 p, L q (X.val q) = X'.val (f q))
    (hY : ∀ᶠ q in 𝓝 p, L q (Y.val q) = Y'.val (f q)) :
    L p ((C.cov X Y).val p) = (K.cov X' Y').val (f p) := by
  obtain ⟨Z, Z', hZ, _, hZ'p⟩ := exists_related_coordinate_frames f hf L hL c d hs hcoord p hp
  have he (j : Fin n) :
      pairing h (f p) (L p ((C.cov X Y).val p)) (coordinateVector d j (f p)) =
        pairing h (f p) ((K.cov X' Y').val (f p)) (coordinateVector d j (f p)) := by
    have hc := P202.Geometry.LeviCivita.koszul_of_leviCivita
      P202.Geometry.TorsionAndMetric.torsion_apply g C hC X Y (Z j) p
    have hk := P202.Geometry.LeviCivita.koszul_of_leviCivita
      P202.Geometry.TorsionAndMetric.torsion_apply h K hK X' Y' (Z' j) (f p)
    have hn := P202.Geometry.LeviCivita.koszulFunction_related_at
      f hf L hL g h hm X Y (Z j) X' Y' (Z' j) p hX hY (hZ j)
    rw [P202.Geometry.LeviCivita.koszulFunction_apply,
      P202.Geometry.LeviCivita.koszulFunction_apply] at hn
    rw [← hZ'p j, ← (hZ j).self_of_nhds, hm]
    have heval : (Z' j).val (f p) = L p ((Z j).val p) := (hZ j).self_of_nhds.symm
    rw [heval] at hk
    linarith
  apply P202.Geometry.LeviCivita.pairing_ext h (f p)
  intro V
  have hpd : f p ∈ (tangentBundle W).baseSet d :=
    (tangentRealization W).baseSet d ▸ hs p hp
  rw [← P202.Geometry.LeviCivita.coordinate_expansion d (f p) hpd (V.val (f p))]
  simp only [P202.MetricData.pairing, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun r : ℝ =>
    ((tangentBundle W).fiberCoordinates d (f p) hpd (V.val (f p))) j * r) (he j)
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}
/-- Every source tangent vector admits a smooth test field whose pushed
coordinate germ extends to the ambient target, even at a genuine seam. -/
theorem exists_matchingChart_related_fields
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (p : M) (hp : p ∈ c.val.source) (v : TangentSpace S p) :
    ∃ (X : Field S) (Y : Field W), X.val p = v ∧
      ∀ᶠ q in 𝓝 p, L q (X.val q) = Y.val (f q) := by
  obtain ⟨A, B, hAB, hAp, _⟩ := exists_related_coordinate_frames f hf L hL c d hs hcoord p hp
  have hpc : p ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  let coeff : Fin n → ℝ := (tangentBundle S).fiberCoordinates c p hpc v
  refine ⟨∑ j, coeff j • A j, ∑ j, coeff j • B j, ?_, ?_⟩
  · simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, hAp]
    exact P202.Geometry.LeviCivita.coordinate_expansion c p hpc v
  · filter_upwards [Filter.eventually_all.mpr hAB] with q hq
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, map_sum, map_smul, hq]
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
open P202.CurvatureData
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}
/-- Actual curvature fields transport in matching metric coordinates without
a local inverse across the source boundary. -/
theorem matchingChart_curvature_related_at
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (X Y Z : Field S) (X' Y' Z' : Field W) (p : M) (hp : p ∈ c.val.source)
    (hX : ∀ᶠ q in 𝓝 p, L q (X.val q) = X'.val (f q))
    (hY : ∀ᶠ q in 𝓝 p, L q (Y.val q) = Y'.val (f q))
    (hZ : ∀ᶠ q in 𝓝 p, L q (Z.val q) = Z'.val (f q)) :
    L p ((curvature C X Y Z).val p) = (curvature K X' Y' Z').val (f p) := by
  have conn (A B : Field S) (A' B' : Field W) (q : M) (hq : q ∈ c.val.source)
      (hA : ∀ᶠ r in 𝓝 q, L r (A.val r) = A'.val (f r))
      (hB : ∀ᶠ r in 𝓝 q, L r (B.val r) = B'.val (f r)) :=
    matchingChart_connection_related_at f hf L hL g h hm c d hs hcoord C K hC hK
      A B A' B' q hq hA hB
  have hYZ : ∀ᶠ q in 𝓝 p,
      L q ((C.cov Y Z).val q) = (K.cov Y' Z').val (f q) := by
    filter_upwards [hY.eventually_nhds, hZ.eventually_nhds, c.val.open_source.mem_nhds hp]
      with q hYq hZq hq
    exact conn Y Z Y' Z' q hq hYq hZq
  have hXZ : ∀ᶠ q in 𝓝 p,
      L q ((C.cov X Z).val q) = (K.cov X' Z').val (f q) := by
    filter_upwards [hX.eventually_nhds, hZ.eventually_nhds, c.val.open_source.mem_nhds hp]
      with q hXq hZq hq
    exact conn X Z X' Z' q hq hXq hZq
  have hXY : ∀ᶠ q in 𝓝 p,
      L q ((P202.TorsionMetricData.bracket X Y).val q) =
        (P202.TorsionMetricData.bracket X' Y').val (f q) := by
    filter_upwards [hX.eventually_nhds, hY.eventually_nhds] with q hXq hYq
    exact P202.Geometry.LeviCivita.bracket_related_at f hf L hL X Y X' Y' q hXq hYq
  rw [P202.Geometry.CurvatureAlgebra.curvature_apply,
    P202.Geometry.CurvatureAlgebra.curvature_apply]
  have hmapp (v w : TangentSpace S p) : L p (v - w) = L p v - L p w := by
    rw [P202.Geometry.LeviCivita.tangent_sub_as_add,
      P202.Geometry.LeviCivita.tangent_sub_as_add]
    simp only [map_add, map_smul]
  rw [hmapp, hmapp, conn X (C.cov Y Z) X' (K.cov Y' Z') p hp hX hYZ,
    conn Y (C.cov X Z) Y' (K.cov X' Z') p hp hY hXZ,
    conn (P202.TorsionMetricData.bracket X Y) Z
      (P202.TorsionMetricData.bracket X' Y') Z' p hp hXY hZ]

/-- Every representing curvature tensor obeys the same genuine seam
transport law; the fields used to test it are constructed above. -/
theorem matchingChart_curvatureTensor
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (p : M) (hp : p ∈ c.val.source) (v w z : TangentSpace S p) :
    L p (R.val p v w z) = R'.val (f p) (L p v) (L p w) (L p z) := by
  obtain ⟨X, X', hXp, hX⟩ := exists_matchingChart_related_fields f hf L hL c d hs hcoord p hp v
  obtain ⟨Y, Y', hYp, hY⟩ := exists_matchingChart_related_fields f hf L hL c d hs hcoord p hp w
  obtain ⟨Z, Z', hZp, hZ⟩ := exists_matchingChart_related_fields f hf L hL c d hs hcoord p hp z
  rw [← hXp, ← hYp, ← hZp, hR X Y Z p,
    matchingChart_curvature_related_at f hf L hL g h hm c d hs hcoord C K hC hK
      X Y Z X' Y' Z' p hp hX hY hZ, ← hR' X' Y' Z' (f p),
    hX.self_of_nhds, hY.self_of_nhds, hZ.self_of_nhds]
end P202.GlobalGaussBonnet
end Round3ChartConnections


/-! Continuation: Round3ChartGaussian. -/
section Round3ChartGaussian
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.TangentBundleData
open SmoothManifolds.BundleOperationsData
open P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData P202.SurfaceBoundaryData
namespace P202.GlobalGaussBonnet
variable {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 a M} {W : SmoothManifold 2 b N}
/-- Gaussian curvature agrees across a metric extension in matching chart
coordinates, including at genuine boundary points. -/
theorem matchingChart_gaussianCurvature
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (p : M) (hp : p ∈ c.val.source) :
    P202Specs.GlobalGaussBonnet.gaussianCurvature g R p =
      P202Specs.GlobalGaussBonnet.gaussianCurvature h R' (f p) := by
  let E := ((tangentStructure S).fiberCoordinates.equiv c.val c.property p hp).trans
    ((tangentStructure W).fiberCoordinates.equiv d.val d.property (f p) (hs p hp)).symm
  have hE (v : TangentSpace S p) : E v = L p v := by
    apply ((tangentStructure W).fiberCoordinates.equiv d.val d.property (f p) (hs p hp)).injective
    symm
    simpa only [E, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using
      differential_matching_coordinates f hf p (L p) (hL p)
        c.val d.val c.property d.property hp (hs p hp)
        (by filter_upwards [c.val.open_source.mem_nhds hp] with q hq
            exact hcoord q hq)
        (tangentStructure S).fiberCoordinates (tangentStructure W).fiberCoordinates v
  let bs := referenceBasis g p
  let bt := bs.map E
  have hbt (j : Fin 2) : bt j = L p (bs j) := hE (bs j)
  rw [gaussianCurvature_eq_basis g C hC R hR p bs,
    gaussianCurvature_eq_basis h K hK R' hR' (f p) bt]
  simp only [hbt]
  have hform (v w z t : TangentSpace S p) :
      curvatureForm g R p v w z t =
        curvatureForm h R' (f p) (L p v) (L p w) (L p z) (L p t) := by
    unfold curvatureForm
    rw [← matchingChart_curvatureTensor f hf L hL g h hm c d hs hcoord C K hC hK
      R R' hR hR' p hp v w z]
    exact (hm p (R.val p v w z) t).symm
  rw [hform, hm p (bs 0) (bs 0), hm p (bs 1) (bs 1), hm p (bs 0) (bs 1)]
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 .euclidean M} {W : SmoothManifold 2 .euclidean N}
/-- The actual local curvature integral is invariant under matching
full-source metric chart restrictions. Gaussian naturality is discharged by
the proved connection and curvature comparison. -/
theorem matchingChart_curvatureIntegral
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : ModelChart 2 .euclidean M) (d : ModelChart 2 .euclidean N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (hsource : c.source = univ)
    (hs : ∀ p ∈ c.source, f p ∈ d.source)
    (hcoord : ∀ p ∈ c.source, d (f p) = c p)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (D : P202Specs.PlanarRegionTopology.PlanarRegion)
    (hD : D.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c) :
    P202Specs.LocalGaussBonnet.curvatureIntegral g R c hc D =
      P202Specs.LocalGaussBonnet.curvatureIntegral h R' d hd D := by
  apply metricPreserving_curvatureIntegral f hf L hL g h hm R R' _ c d hc hd hs hcoord D hD
  intro p
  exact matchingChart_gaussianCurvature f hf L hL g h hm ⟨c, hc⟩ ⟨d, hd⟩ hs
    (fun q hq => congrArg Subtype.val (hcoord q hq).symm) C K hC hK R R' hR hR' p
    (by rw [hsource]; exact mem_univ p)
end P202.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 .euclidean M} {W : SmoothManifold 2 .euclidean N}
/-- The local theorem's curvature term on a matching chart restriction is
exactly the canonical intrinsic integral on the original compact chart region.
All curvature and density comparisons are discharged by the actual geometry. -/
theorem matchingChart_curvatureIntegral_eq_intrinsic
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace W (f q))
    (hL : ∀ q, IsDifferential S W f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : ModelChart 2 .euclidean M) (d : ModelChart 2 .euclidean N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (hsource : c.source = univ)
    (hs : ∀ p ∈ c.source, f p ∈ d.source)
    (hcoord : ∀ p ∈ c.source, d (f p) = c p)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (R' : CurvatureTensor W)
    (hR : RepresentsCurvature C R) (hR' : RepresentsCurvature K R')
    (μ : @MeasureTheory.Measure N (borel N)) (hμ : P202Specs.GlobalGaussBonnet.IsAreaMeasure h μ)
    (D : P202Specs.PlanarRegionTopology.PlanarRegion)
    (hD : D.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : Set N) (hA : @MeasurableSet N (borel N) A) (hAK : IsCompact A)
    (hAd : A ⊆ d.source)
    (hAD : P202Specs.SurfaceRegionConstruction.coordinates d '' A = D.carrier) :
    P202Specs.LocalGaussBonnet.curvatureIntegral g R c hc D =
      (letI : MeasurableSpace N := borel N;
        ∫ p in A, P202Specs.GlobalGaussBonnet.gaussianCurvature h R' p ∂μ) := by
  exact (matchingChart_curvatureIntegral f hf L hL g h hm c d hc hd hsource hs hcoord
    C K hC hK R R' hR hR' D hD).trans
      (local_curvatureIntegral_eq_intrinsic_of_isCompact h K hK R' hR' μ hμ
        d hd D A hA hAK hAd hAD).symm
end P202.GlobalGaussBonnet
end Round3ChartGaussian


/-! Continuation: Round3MetricExtension. -/
section Round3MetricExtension
set_option autoImplicit false

open Set Filter
open scoped Topology
open scoped Matrix Matrix.Norms.Elementwise
namespace P202.GlobalGaussBonnet

/-- Three scalar coefficients encode a symmetric two-dimensional Gram form. -/
def symmetricGram (c : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c 0, c 1; c 1, c 2]

lemma symmetricGram_posDef {c : Fin 3 → ℝ} (ha : 0 < c 0)
    (hdet : (c 1)^2 < c 0 * c 2) : (symmetricGram c).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [symmetricGram, Matrix.conjTranspose]
  · intro x hx
    have hxy : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp [h]
    simp [symmetricGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hsq := sq_nonneg (c 0 * x 0 + c 1 * x 1)
    have hid : c 0 * (x 0 * (c 0 * x 0 + c 1 * x 1) +
        x 1 * (c 1 * x 0 + c 2 * x 1)) =
        (c 0 * x 0 + c 1 * x 1)^2 + (c 0*c 2 - (c 1)^2)*(x 1)^2 := by ring
    have hpos : 0 < c 0 * (x 0 * (c 0 * x 0 + c 1 * x 1) +
        x 1 * (c 1 * x 0 + c 2 * x 1)) := by
      rcases eq_or_ne (x 1) 0 with hy | hy
      · have hx0 : x 0 ≠ 0 := hxy.resolve_right (not_ne_iff.mpr hy)
        rw [hy] at *
        nlinarith [sq_pos_of_ne_zero hx0, mul_pos ha ha]
      · rw [hid]
        exact add_pos_of_nonneg_of_pos hsq (mul_pos (sub_pos.mpr hdet) (sq_pos_of_ne_zero hy))
    exact pos_of_mul_pos_right hpos ha.le

/-- A compact set of embedded points admits an ambient smooth extension
whenever the actual smooth coefficient germs do. This applies directly to
chart embeddings of half-space chart domains. -/
theorem embedded_compact_smooth_extension
    {X E V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : X → E) (he : Topology.IsEmbedding e)
    (C : Set X) (hC : IsCompact C) (f : X → V)
    (hloc : ∀ p ∈ C, ∃ U : Set E, IsOpen U ∧ e p ∈ U ∧
      ∃ F : E → V, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        (fun q => F (e q)) =ᶠ[nhds p] f) :
    ∃ F : E → V, ContDiff ℝ (⊤ : ℕ∞) F ∧ ∀ p ∈ C, F (e p) = f p := by
  classical
  let K : Set E := e '' C
  let point (q : K) : X := Classical.choose q.property
  have point_mem (q : K) : point q ∈ C := (Classical.choose_spec q.property).1
  have point_eq (q : K) : e (point q) = q.val := (Classical.choose_spec q.property).2
  obtain ⟨F, hF, heq⟩ := CompactSmoothExtension.smooth_extension_of_local
    K (hC.image he.continuous) (fun q => f (point q)) (by
      intro p
      obtain ⟨U, hU, hpU, G, hG, hge⟩ := hloc (point p) (point_mem p)
      obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hge
      obtain ⟨A, hA, hpre, -⟩ := SmoothManifolds.SliceStructures.embedding_open_cut he hW
      refine ⟨U ∩ A, hU.inter hA, ⟨?_, ?_⟩, G, hG.mono inter_subset_left, ?_⟩
      · simpa only [← point_eq p] using hpU
      · have : point p ∈ e ⁻¹' A := by rw [hpre]; exact hpW
        simpa only [Set.mem_preimage, point_eq p] using this
      · intro q hq
        rw [← point_eq q]
        apply hWsub
        rw [← hpre]
        change e (point q) ∈ A
        rw [point_eq q]
        exact hq.2)
  refine ⟨F, hF, ?_⟩
  intro p hp
  let q : K := ⟨e p, ⟨p, hp, rfl⟩⟩
  have hpoint : point q = p := he.injective (point_eq q)
  simpa only [q, hpoint] using heq q

/-- Compact smooth coefficient data with positive definite symmetric Gram
forms extend to a genuine open Euclidean neighborhood with the same positivity.
Local extensions at a half-space seam are supplied by `VectorSmoothAt`. -/
theorem exists_positive_symmetricGram_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) (hK : IsCompact K) (c : K → Fin 3 → ℝ)
    (ha : ∀ p, 0 < c p 0) (hdet : ∀ p, (c p 1)^2 < c p 0 * c p 2)
    (hloc : ∀ p : K, ∃ U : Set E, IsOpen U ∧ p.val ∈ U ∧
      ∃ F : E → (Fin 3 → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        ∀ q : K, q.val ∈ U → F q.val = c q) :
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧
      ∃ F : E → (Fin 3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) F ∧
        (∀ p : K, F p.val = c p) ∧ ∀ x ∈ U, (symmetricGram (F x)).PosDef := by
  obtain ⟨F, hF, heq⟩ := CompactSmoothExtension.smooth_extension_of_local K hK c hloc
  let U : Set E := {x | 0 < F x 0 ∧ (F x 1)^2 < F x 0 * F x 2}
  have hcoord (i : Fin 3) : Continuous (fun x => F x i) :=
    (continuous_apply i).comp hF.continuous
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (hcoord 0)).inter
      (isOpen_lt ((hcoord 1).pow 2) ((hcoord 0).mul (hcoord 2)))
  refine ⟨U, hU, ?_, F, hF, heq, ?_⟩
  · intro x hx
    change 0 < F x 0 ∧ (F x 1)^2 < F x 0 * F x 2
    rw [heq ⟨x, hx⟩]
    exact ⟨ha ⟨x, hx⟩, hdet ⟨x, hx⟩⟩
  · intro x hx
    exact symmetricGram_posDef hx.1 hx.2

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FrameData SmoothManifolds.MetricVolumeData

/-- The chart embedding, including in the half-space model. -/
def metricChartEmbedding {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*}
    [TopologicalSpace M] (c : ModelChart n a M) : c.source → Euclidean n :=
  fun p => (c p.val).val

lemma metricChartEmbedding_isEmbedding {n : ℕ} {a : SmoothManifolds.ModelKind}
    {M : Type*} [TopologicalSpace M] (c : ModelChart n a M) :
    Topology.IsEmbedding (metricChartEmbedding c) := by
  exact Topology.IsEmbedding.subtypeVal.comp
    (Topology.IsEmbedding.subtypeVal.comp c.toHomeomorphSourceTarget.isEmbedding)

/-- Every compact portion of the actual coordinate metric has a smooth
symmetric positive-definite extension to an open ambient Euclidean neighborhood.
No local diffeomorphism from a half-space seam is assumed. -/
theorem exists_chartMetricMatrix_extension
    {a : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {C : CotangentBundle S} (g : Metric C)
    (K : FiberCoordinates S) (c : ModelChart 2 a M) (hc : c ∈ S.smoothStructure.val)
    (A : Set c.source) (hA : IsCompact A) :
    ∃ U : Set (Euclidean 2), IsOpen U ∧ metricChartEmbedding c '' A ⊆ U ∧
      ∃ F : Euclidean 2 → Matrix (Fin 2) (Fin 2) ℝ,
        ContDiff ℝ (⊤ : ℕ∞) F ∧
        (∀ p ∈ A, F (metricChartEmbedding c p) = metricMatrix g K c hc p) ∧
        ∀ x ∈ U, (F x).PosDef := by
  classical
  let _ := C.realization.space.topology
  let coeff : c.source → Fin 3 → ℝ := fun p =>
    ![metricMatrix g K c hc p 0 0, metricMatrix g K c hc p 0 1,
      metricMatrix g K c hc p 1 1]
  have hloc (p : c.source) (_ : p ∈ A) :
      ∃ U : Set (Euclidean 2), IsOpen U ∧ metricChartEmbedding c p ∈ U ∧
        ∃ F : Euclidean 2 → (Fin 3 → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
          (fun q => F (metricChartEmbedding c q)) =ᶠ[𝓝 p] coeff := by
    have hsm : VectorSmoothAt
        (openSubsetAtlas S.smoothStructure.val c.source c.open_source) coeff p := by
      apply SmoothManifolds.FrameData.VectorSmoothAt.pi
      intro i
      fin_cases i
      · exact SmoothManifolds.MetricVolumeResults.metricMatrix_smooth g K c hc 0 0 p
      · exact SmoothManifolds.MetricVolumeResults.metricMatrix_smooth g K c hc 0 1 p
      · exact SmoothManifolds.MetricVolumeResults.metricMatrix_smooth g K c hc 1 1 p
    let d := c.subtypeRestr (s := ⟨c.source, c.open_source⟩) ⟨p⟩
    have hd : d ∈ openSubsetAtlas S.smoothStructure.val c.source c.open_source :=
      ⟨⟨p⟩, c, hc, rfl⟩
    have hpd : p ∈ d.source := by
      simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using p.property
    obtain ⟨U, hU, hpU, G, hG, heG⟩ := hsm.2 d hd hpd
    exact ⟨U, hU, hpU, G, hG, heG⟩
  obtain ⟨F, hF, heF⟩ := embedded_compact_smooth_extension
    (metricChartEmbedding c) (metricChartEmbedding_isEmbedding c) A hA coeff hloc
  have ha (p : c.source) : 0 < coeff p 0 := by
    exact g.positive p.val
      ((SmoothManifolds.MetricVolumeResults.coordinateBasis K c hc p) 0)
      ((SmoothManifolds.MetricVolumeResults.coordinateBasis K c hc p).ne_zero 0)
  have hsym (p : c.source) : metricMatrix g K c hc p 1 0 = metricMatrix g K c hc p 0 1 := by
    exact g.symmetric p.val _ _
  have hdet (p : c.source) : (coeff p 1)^2 < coeff p 0 * coeff p 2 := by
    have hd := SmoothManifolds.MetricVolumeResults.metricMatrix_det_pos g K c hc p
    rw [Matrix.det_fin_two, hsym p] at hd
    change (metricMatrix g K c hc p 0 1)^2 <
      metricMatrix g K c hc p 0 0 * metricMatrix g K c hc p 1 1
    nlinarith
  let U : Set (Euclidean 2) := {x | 0 < F x 0 ∧ (F x 1)^2 < F x 0 * F x 2}
  have hcoord (i : Fin 3) : Continuous (fun x => F x i) :=
    (continuous_apply i).comp hF.continuous
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (hcoord 0)).inter
      (isOpen_lt ((hcoord 1).pow 2) ((hcoord 0).mul (hcoord 2)))
  refine ⟨U, hU, ?_, fun x => symmetricGram (F x), ?_, ?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩
    change 0 < F (metricChartEmbedding c p) 0 ∧
      (F (metricChartEmbedding c p) 1)^2 <
        F (metricChartEmbedding c p) 0 * F (metricChartEmbedding c p) 2
    rw [heF p hp]
    exact ⟨ha p, hdet p⟩
  · apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x => F x 0)
      exact (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3)).contDiff.comp hF
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x => F x 1)
      exact (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3)).contDiff.comp hF
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x => F x 1)
      exact (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3)).contDiff.comp hF
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x => F x 2)
      exact (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3)).contDiff.comp hF
  · intro p hp
    change symmetricGram (F (metricChartEmbedding c p)) = _
    rw [heF p hp]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symmetricGram, coeff, hsym p]
  · intro x hx
    exact symmetricGram_posDef hx.1 hx.2

end P202.GlobalGaussBonnet

open Set Filter
open scoped Topology Matrix.Norms.Elementwise
namespace P202.GlobalGaussBonnet
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleData SmoothManifolds.BundleMetricData
  SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
open SmoothManifolds.BundleMetrics

section MatrixMetric
variable {n r : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*}
  [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type*} {E : M → Type*}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

noncomputable def matrixMetricForm (i₀ : ι) (G : M → Matrix (Fin r) (Fin r) ℝ)
    (p : M) : LinearMap.BilinForm ℝ (E p) :=
  (Matrix.toBilin' (G p)).compl₁₂ (coordinateMap B i₀ p) (coordinateMap B i₀ p)

lemma matrixMetricForm_symmetric (i₀ : ι) (G : M → Matrix (Fin r) (Fin r) ℝ)
    (hG : ∀ p, (G p).PosDef) (p : M) (v w : E p) :
    matrixMetricForm B i₀ G p v w = matrixMetricForm B i₀ G p w v := by
  exact ((Matrix.isSymm_toBilin'_iff_isSymm).mpr (hG p).isHermitian.isSymm).eq _ _

lemma matrixMetricForm_positive (i₀ : ι) (hfull : ∀ p, p ∈ B.baseSet i₀)
    (G : M → Matrix (Fin r) (Fin r) ℝ) (hG : ∀ p, (G p).PosDef)
    (p : M) (v : E p) (hv : v ≠ 0) : 0 < matrixMetricForm B i₀ G p v v := by
  have hne : coordinateMap B i₀ p v ≠ 0 := by
    intro hz
    apply hv
    apply (B.fiberCoordinates i₀ p (hfull p)).injective
    rw [map_zero]
    simpa only [coordinateMap_of_mem B i₀ p (hfull p),
      SmoothVectorBundle.fiberCoordinates_apply] using hz
  change 0 < Matrix.toBilin' (G p) (coordinateMap B i₀ p v) (coordinateMap B i₀ p v)
  rw [Matrix.toBilin'_apply']
  simpa only [star_trivial] using (hG p).dotProduct_mulVec_pos hne

lemma matrixMetricForm_smooth (i₀ : ι) (hfull : ∀ p, p ∈ B.baseSet i₀)
    (G : M → Matrix (Fin r) (Fin r) ℝ)
    (hG : ∀ j k p, VectorSmoothAt S.smoothStructure.val (fun q => G q j k) p) :
    ∀ (i : ι) (j k : Fin r), SmoothOnBase S
      (fun p => matrixMetricForm B i₀ G p
        ((B.trivialization i).symm p (Pi.single j 1))
        ((B.trivialization i).symm p (Pi.single k 1))) (B.baseSet i) := by
  intro i j k p hp
  change VectorSmoothAt S.smoothStructure.val _ p
  simp only [matrixMetricForm, LinearMap.compl₁₂_apply, Matrix.toBilin'_apply]
  apply SmoothManifolds.FrameData.VectorSmoothAt.sum
  intro l
  apply SmoothManifolds.FrameData.VectorSmoothAt.sum
  intro m
  have hj := (transitionVector_smoothAt B i i₀ (Pi.single j 1) p hp (hfull p)).postcomp
    (ContinuousLinearMap.proj (R := ℝ) l).contDiff
  have hk := (transitionVector_smoothAt B i i₀ (Pi.single k 1) p hp (hfull p)).postcomp
    (ContinuousLinearMap.proj (R := ℝ) m).contDiff
  exact (((hj.prod (hG l m p)).postcomp (contDiff_fst.mul contDiff_snd)).prod hk).postcomp
    (contDiff_fst.mul contDiff_snd)

/-- A smooth positive matrix field in a genuine global bundle chart defines
an actual smooth fiber metric in every bundle chart. -/
noncomputable def matrixMetricOfGlobalChart (i₀ : ι) (hfull : ∀ p, p ∈ B.baseSet i₀)
    (G : M → Matrix (Fin r) (Fin r) ℝ) (hpos : ∀ p, (G p).PosDef)
    (hsmooth : ∀ j k p, VectorSmoothAt S.smoothStructure.val (fun q => G q j k) p) :
    SmoothFiberMetric B where
  form := matrixMetricForm B i₀ G
  symmetric := matrixMetricForm_symmetric B i₀ G hpos
  positive := matrixMetricForm_positive B i₀ hfull G hpos
  smooth := matrixMetricForm_smooth B i₀ hfull G hsmooth

end MatrixMetric
open P202.MetricData

/-- A positive smooth matrix field in a full-source surface chart gives a
metric on the ACTUAL canonical tangent fibers and realization. -/
noncomputable def metricOfGlobalChart
    {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold n a M) (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hsource : d.source = univ) (F : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hpos : ∀ p, (F (d p).val).PosDef) :
    RiemannianMetric S := by
  letI := (tangentRealization S).space.topology
  let B := (tangentRealization S).space.bundle
  let i₀ : TangentIndex S := ⟨d, hd⟩
  have hfull (p : M) : p ∈ B.baseSet i₀ := by
    rw [(tangentRealization S).baseSet i₀, hsource]
    trivial
  refine matrixMetricOfGlobalChart B i₀ hfull (fun p => F (d p).val) hpos ?_
  intro j k p
  have hFjk : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j k) :=
    contDiff_pi.mp (contDiff_pi.mp hF j) k
  exact SmoothManifolds.BundleOperations.vectorSmoothAt_of_chart S _ p d hd
    (by rw [hsource]; trivial) univ isOpen_univ (mem_univ _) _ hFjk.contDiffOn
      Filter.EventuallyEq.rfl

/-- The metric constructor has exactly the prescribed coordinate pairing. -/
theorem metricOfGlobalChart_pairing
    {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold n a M) (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hsource : d.source = univ) (F : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hpos : ∀ p, (F (d p).val).PosDef)
    (p : M) (hp : p ∈ d.source) (v w : TangentSpace S p) :
    P202.MetricData.pairing (metricOfGlobalChart S d hd hsource F hF hpos) p v w =
      Matrix.toBilin' (F (d p).val)
        ((tangentStructure S).fiberCoordinates.equiv d hd p hp v)
        ((tangentStructure S).fiberCoordinates.equiv d hd p hp w) := by
  let _ := (tangentRealization S).space.topology
  let B := (tangentRealization S).space.bundle
  let i₀ : TangentIndex S := ⟨d, hd⟩
  have hbase : p ∈ B.baseSet i₀ := by
    rw [(tangentRealization S).baseSet i₀]
    exact hp
  change Matrix.toBilin' (F (d p).val) (coordinateMap B i₀ p v) (coordinateMap B i₀ p w) = _
  rw [coordinateMap_of_mem B i₀ p hbase, coordinateMap_of_mem B i₀ p hbase,
    (tangentRealization S).coordinates i₀ p hp v,
    (tangentRealization S).coordinates i₀ p hp w]

/-- Consequently the actual coordinate Gram matrix is exactly the prescribed
matrix field, including the complete off-diagonal entries. -/
theorem metricOfGlobalChart_gramMatrix
    {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold n a M) (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hsource : d.source = univ) (F : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hpos : ∀ p, (F (d p).val).PosDef)
    (p : d.source) :
    P202.VolumeData.gramMatrix (metricOfGlobalChart S d hd hsource F hF hpos)
      (tangentStructure S).fiberCoordinates d hd p = F (d p.val).val := by
  ext i j
  change P202.MetricData.pairing (metricOfGlobalChart S d hd hsource F hF hpos) p.val
    (((tangentStructure S).fiberCoordinates.equiv d hd p.val p.property).symm
      ((Pi.basisFun ℝ (Fin n)) i))
    (((tangentStructure S).fiberCoordinates.equiv d hd p.val p.property).symm
      ((Pi.basisFun ℝ (Fin n)) j)) = _
  rw [metricOfGlobalChart_pairing S d hd hsource F hF hpos p.val p.property]
  simp only [LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  exact Matrix.toBilin'_single _ i j

/-- A smooth positive matrix field on an open Euclidean set produces the
actual Euclidean-model smooth manifold, its full-source coordinate chart and
its canonical-tangent Riemannian metric. -/
theorem exists_openEuclideanChartMetric
    {n : ℕ} (U : Set (Euclidean n)) (hU : IsOpen U) (hne : U.Nonempty)
    (F : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hpos : ∀ x ∈ U, (F x).PosDef) :
    ∃ Q : SmoothManifold n .euclidean U,
      ∃ d : ModelChart n .euclidean U, ∃ hd : d ∈ Q.smoothStructure.val,
        d.source = univ ∧ (∀ p : U, (d p).val = p.val) ∧
        ∃ g : RiemannianMetric Q,
          ∀ p : d.source, P202.VolumeData.gramMatrix g
            (tangentStructure Q).fiberCoordinates d hd p = F p.val.val := by
  obtain ⟨E, hE⟩ := SmoothManifolds.standardEuclidean_exists n
  obtain ⟨Q, _, hQA, _⟩ := SmoothManifolds.exists_openSubset_smoothManifold E U hU
  let hp : Nonempty U := hne.to_subtype
  let d := (SmoothManifolds.euclideanChart n).subtypeRestr (s := ⟨U, hU⟩) hp
  have hd : d ∈ Q.smoothStructure.val := by
    rw [hQA]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _
        E.smoothStructure.property.1 U hU) ⟨hp, SmoothManifolds.euclideanChart n, hE, rfl⟩
  have hsource : d.source = univ := by
    ext p
    simp only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage,
      SmoothManifolds.euclideanChart_source, mem_univ]
  have hdval (p : U) : (d p).val = p.val := rfl
  have hpos' (p : U) : (F (d p).val).PosDef := hpos p.val p.property
  let g := metricOfGlobalChart Q d hd hsource F hF hpos'
  refine ⟨Q, d, hd, hsource, hdval, g, ?_⟩
  intro p
  exact metricOfGlobalChart_gramMatrix Q d hd hsource F hF hpos' p

/-- An actual chart metric on either source model extends across its seam
near every nonempty compact coordinate subset. The result supplies an actual
Euclidean surface and metric and exact agreement of the two coordinate Grams. -/
theorem exists_compact_chart_metric_extension
    {a : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold 2 a M) (g : P202.MetricData.RiemannianMetric S)
    (e : ModelChart 2 a M) (he : e ∈ S.smoothStructure.val)
    (A : Set e.source) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ U : Set (Euclidean 2), IsOpen U ∧ metricChartEmbedding e '' A ⊆ U ∧
      ∃ Q : SmoothManifold 2 .euclidean U,
        ∃ d : ModelChart 2 .euclidean U, ∃ hd : d ∈ Q.smoothStructure.val,
          d.source = univ ∧ (∀ p : U, (d p).val = p.val) ∧
          ∃ h : P202.MetricData.RiemannianMetric Q,
            ∀ p ∈ A, ∀ q : d.source, q.val.val = metricChartEmbedding e p →
              P202.VolumeData.gramMatrix h (tangentStructure Q).fiberCoordinates d hd q =
                P202.VolumeData.gramMatrix g (tangentStructure S).fiberCoordinates e he p := by
  obtain ⟨U, hU, hAU, F, hF, heF, hpos⟩ := exists_chartMetricMatrix_extension
    (P202.VolumeData.libraryMetric g) (tangentStructure S).fiberCoordinates e he A hA
  have hneU : U.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨metricChartEmbedding e p, hAU ⟨p, hp, rfl⟩⟩
  obtain ⟨Q, d, hd, hs, hv, h, hGram⟩ := exists_openEuclideanChartMetric U hU hneU F hF hpos
  refine ⟨U, hU, hAU, Q, d, hd, hs, hv, h, ?_⟩
  intro p hp q hq
  rw [hGram, hq, heF p hp]
  rfl

/-- The extension can be required to agree on an OPEN original neighborhood
of the chosen compact set, which supplies equality of germs at a true seam. -/
theorem exists_chart_metric_extension_near_compact
    {a : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold 2 a M) (g : P202.MetricData.RiemannianMetric S)
    (e : ModelChart 2 a M) (he : e ∈ S.smoothStructure.val)
    (A : Set e.source) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ V : Set e.source, IsOpen V ∧ A ⊆ V ∧
      ∃ U : Set (Euclidean 2), IsOpen U ∧ metricChartEmbedding e '' V ⊆ U ∧
        ∃ Q : SmoothManifold 2 .euclidean U,
          ∃ d : ModelChart 2 .euclidean U, ∃ hd : d ∈ Q.smoothStructure.val,
            d.source = univ ∧ (∀ p : U, (d p).val = p.val) ∧
            ∃ h : P202.MetricData.RiemannianMetric Q,
              ∀ p ∈ V, ∀ q : d.source, q.val.val = metricChartEmbedding e p →
                P202.VolumeData.gramMatrix h (tangentStructure Q).fiberCoordinates d hd q =
                  P202.VolumeData.gramMatrix g (tangentStructure S).fiberCoordinates e he p := by
  let _ : LocallyCompactSpace M := SmoothManifolds.TopologicalManifold.locallyCompactSpace S.topologicalManifold
  let _ : LocallyCompactSpace e.source := e.open_source.locallyCompactSpace
  obtain ⟨A', hA', hAA'⟩ := exists_compact_superset hA
  have hne' : A'.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, interior_subset (hAA' hp)⟩
  obtain ⟨U, hU, hAU, Q, d, hd, hs, hv, h, hGram⟩ :=
    exists_compact_chart_metric_extension S g e he A' hA' hne'
  refine ⟨interior A', isOpen_interior, hAA', U, hU, ?_, Q, d, hd, hs, hv, h, ?_⟩
  · exact (image_mono interior_subset).trans hAU
  · intro p hp q hq
    exact hGram p (interior_subset hp) q hq

end P202.GlobalGaussBonnet
end Round3MetricExtension


/-! Continuation: Round3BoundaryTransport. -/
section Round3BoundaryTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
open P202.CurveConnectionData
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Covariant differentiation depends only on the germ of the actual field
along the same curve. -/
theorem hasCovariantDerivativeAt_congr_field
    (C : Connection (tangentBundle S)) {c : ℝ → M}
    {T U : (t : ℝ) → TangentSpace S (c t)} {s : ℝ}
    {D : TangentSpace S (c s)}
    (hD : HasCovariantDerivativeAt C c T s D)
    (heq : ∀ᶠ t in 𝓝 s, T t = U t) :
    HasCovariantDerivativeAt C c U s D := by
  obtain ⟨V, hV, O, hO, b, hp, v', hv, hframe⟩ := hD
  have hval : T s = U s := heq.self_of_nhds
  have hcoeff : coefficientsAlong b c T =ᶠ[𝓝[univ] s] coefficientsAlong b c U := by
    simp only [nhdsWithin_univ]
    filter_upwards [heq] with t ht
    simp only [coefficientsAlong, ht]
  refine ⟨V, hV, O, hO, b, hp, v',
    hv.congr_of_eventuallyEq_of_mem hcoeff.symm (mem_univ s), ?_⟩
  simpa only [frameDerivative, coefficientsAlong, hval] using hframe

/-- Positive velocity scaling does not change the actual unit tangent. -/
theorem unitTangent_reparam_pos_at (g : RiemannianMetric S)
    (c : ℝ → M) (V : (t : ℝ) → TangentSpace S (c t))
    (φ a : ℝ → ℝ) (s : ℝ) (ha : 0 < a s) :
    unitTangent g (c ∘ φ) (fun t => a t • V (φ t)) s =
      unitTangent g c V (φ s) := by
  dsimp [unitTangent]
  rw [P202.Geometry.SmoothMetrics.tangentNorm_smul, abs_of_pos ha,
    smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt ha), mul_one]

/-- Negative velocity scaling reverses the actual unit tangent. -/
theorem unitTangent_reparam_neg_at (g : RiemannianMetric S)
    (c : ℝ → M) (V : (t : ℝ) → TangentSpace S (c t))
    (φ a : ℝ → ℝ) (s : ℝ) (ha : a s < 0) :
    unitTangent g (c ∘ φ) (fun t => a t • V (φ t)) s =
      -unitTangent g c V (φ s) := by
  dsimp [unitTangent]
  rw [P202.Geometry.SmoothMetrics.tangentNorm_smul, abs_of_neg ha,
    smul_smul, mul_inv_rev]
  have he : (tangentNorm g (c (φ s)) (V (φ s)))⁻¹ * (-a s)⁻¹ * a s =
      -(tangentNorm g (c (φ s)) (V (φ s)))⁻¹ := by
    field_simp [ne_of_lt ha]
  rw [he]
  exact neg_smul ((tangentNorm g (c (φ s)) (V (φ s)))⁻¹) (V (φ s))

/-- Parameter changes with positive derivative preserve the actual D_T T
and thus its pairing with any given normal. No orientation is assumed. -/
theorem regularArc_curvature_reparam_pos
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t))
    (φ a : ℝ → ℝ) (s : ℝ) (ha : ∀ᶠ t in 𝓝 s, 0 < a t)
    (hφ : HasDerivAt φ (a s) s) (hs : φ s ∈ Ioo c.left c.right) :
    inwardCurveCurvature C g (c.curve ∘ φ)
      (unitTangent g (c.curve ∘ φ) (fun t => a t • c.velocity (φ t)))
      (fun t => N (φ t))
      (fun t => tangentNorm g (c.curve (φ t)) (a t • c.velocity (φ t))) s =
        inwardCurveCurvature C g c.curve c.tangent N c.speed (φ s) := by
  obtain ⟨D, hD⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative g C c (φ s) hs
  have hd := P202.Geometry.CurveCovariantDerivative.ordinary_reparam C hD hφ
  have hgerm : ∀ᶠ t in 𝓝 s, c.tangent (φ t) =
      unitTangent g (c.curve ∘ φ) (fun u => a u • c.velocity (φ u)) t := by
    filter_upwards [ha] with t ht
    exact (unitTangent_reparam_pos_at g c.curve c.velocity φ a t ht).symm
  have hd' := hasCovariantDerivativeAt_congr_field C hd hgerm
  have he := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (mem_univ s) uniqueDiffWithinAt_univ hd'
  have hf := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (mem_univ (φ s)) uniqueDiffWithinAt_univ hD
  change pairing g (c.curve (φ s))
    ((tangentNorm g (c.curve (φ s)) (a s • c.velocity (φ s)))⁻¹ •
      covariantDerivative C (c.curve ∘ φ)
        (unitTangent g (c.curve ∘ φ) (fun t => a t • c.velocity (φ t))) s) (N (φ s)) =
    pairing g (c.curve (φ s)) ((c.speed (φ s))⁻¹ •
      covariantDerivative C c.curve c.tangent (φ s)) (N (φ s))
  dsimp only [covariantDerivative]
  rw [he, hf, P202.Geometry.SmoothMetrics.tangentNorm_smul, abs_of_pos (ha.self_of_nhds),
    smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt (ha.self_of_nhds)), mul_one]
  rfl

/-- Parameter changes with negative derivative preserve the actual D_T T:
both the parameter derivative and the unit tangent change direction. -/
theorem regularArc_curvature_reparam_neg
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t))
    (φ a : ℝ → ℝ) (s : ℝ) (ha : ∀ᶠ t in 𝓝 s, a t < 0)
    (hφ : HasDerivAt φ (a s) s) (hs : φ s ∈ Ioo c.left c.right) :
    inwardCurveCurvature C g (c.curve ∘ φ)
      (unitTangent g (c.curve ∘ φ) (fun t => a t • c.velocity (φ t)))
      (fun t => N (φ t))
      (fun t => tangentNorm g (c.curve (φ t)) (a t • c.velocity (φ t))) s =
        inwardCurveCurvature C g c.curve c.tangent N c.speed (φ s) := by
  obtain ⟨D, hD⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative g C c (φ s) hs
  have hd := P202.Geometry.CurveCovariantDerivative.ordinary_reparam C hD hφ
  have hdneg := P202.Geometry.CurveCovariantDerivative.derivative_const_smul C hd (-1)
  simp only [neg_one_smul] at hdneg
  have hgerm : ∀ᶠ t in 𝓝 s, -c.tangent (φ t) =
      unitTangent g (c.curve ∘ φ) (fun u => a u • c.velocity (φ u)) t := by
    filter_upwards [ha] with t ht
    exact (unitTangent_reparam_neg_at g c.curve c.velocity φ a t ht).symm
  have hd' := hasCovariantDerivativeAt_congr_field C hdneg hgerm
  have he := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (mem_univ s) uniqueDiffWithinAt_univ hd'
  have hf := P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (mem_univ (φ s)) uniqueDiffWithinAt_univ hD
  change pairing g (c.curve (φ s))
    ((tangentNorm g (c.curve (φ s)) (a s • c.velocity (φ s)))⁻¹ •
      covariantDerivative C (c.curve ∘ φ)
        (unitTangent g (c.curve ∘ φ) (fun t => a t • c.velocity (φ t))) s) (N (φ s)) =
    pairing g (c.curve (φ s)) ((c.speed (φ s))⁻¹ •
      covariantDerivative C c.curve c.tangent (φ s)) (N (φ s))
  dsimp only [covariantDerivative]
  rw [he, hf, P202.Geometry.SmoothMetrics.tangentNorm_smul, abs_of_neg (ha.self_of_nhds)]
  rw [← neg_smul, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (neg_ne_zero.mpr (ne_of_lt ha.self_of_nhds)), mul_one]
  rfl

/-- Monotone substitution for an unsigned scalar 1-density. Endpoint values
have no effect, and no auxiliary integrability assumption is needed. -/
theorem intervalIntegral_density_reparam_nonneg (f φ a : ℝ → ℝ)
    (l r : ℝ) (hφ : ContinuousOn φ (uIcc l r))
    (hd : ∀ s ∈ Ioo (min l r) (max l r), HasDerivAt φ (a s) s)
    (ha : ∀ s ∈ Ioo (min l r) (max l r), 0 ≤ a s) :
    (∫ s in l..r, f (φ s) * |a s|) = ∫ t in φ l..φ r, f t := by
  calc
    _ = ∫ s in l..r, f (φ s) * a s := by
      apply intervalIntegral.integral_congr_uIoo
      intro s hs
      dsimp only
      rw [abs_of_nonneg (ha s hs)]
    _ = _ := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hφ hd ha

/-- A decreasing parameter change reverses the interval of an unsigned
scalar 1-density. -/
theorem intervalIntegral_density_reparam_nonpos (f φ a : ℝ → ℝ)
    (l r : ℝ) (hφ : ContinuousOn φ (uIcc l r))
    (hd : ∀ s ∈ Ioo (min l r) (max l r), HasDerivAt φ (a s) s)
    (ha : ∀ s ∈ Ioo (min l r) (max l r), a s ≤ 0) :
    (∫ s in l..r, f (φ s) * |a s|) = ∫ t in φ r..φ l, f t := by
  calc
    _ = -(∫ s in l..r, f (φ s) * a s) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_uIoo
      intro s hs
      dsimp only
      rw [abs_of_nonpos (ha s hs)]
      ring
    _ = -(∫ t in φ l..φ r, f t) := by
      exact congrArg Neg.neg
        (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := f) hφ hd ha)
    _ = _ := (intervalIntegral.integral_symm (φ l) (φ r)).symm

/-- Complete increasing parameter transport for the actual curvature times
metric speed. The source arc supplies all covariant-derivative existence. -/
theorem regularArc_curvatureIntegral_reparam_pos
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t))
    (φ a : ℝ → ℝ) (l r : ℝ) (hlr : l ≤ r)
    (ha : ∀ t ∈ Ioo l r, 0 < a t)
    (hφ : ContinuousOn φ (uIcc l r))
    (hd : ∀ s ∈ Ioo l r, HasDerivAt φ (a s) s)
    (hmaps : MapsTo φ (Ioo l r) (Ioo c.left c.right)) :
    (∫ s in l..r,
      inwardCurveCurvature C g (c.curve ∘ φ)
        (unitTangent g (c.curve ∘ φ) (fun t => a t • c.velocity (φ t)))
        (fun t => N (φ t))
        (fun t => tangentNorm g (c.curve (φ t)) (a t • c.velocity (φ t))) s *
          tangentNorm g (c.curve (φ s)) (a s • c.velocity (φ s))) =
      ∫ t in φ l..φ r, inwardCurveCurvature C g c.curve c.tangent N c.speed t * c.speed t := by
  calc
    _ = ∫ s in l..r,
        (inwardCurveCurvature C g c.curve c.tangent N c.speed (φ s) * c.speed (φ s)) * |a s| := by
      apply intervalIntegral.integral_congr_Ioo_of_le hlr
      intro s hs
      dsimp only
      rw [regularArc_curvature_reparam_pos g C c N φ a s
        (by filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht; exact ha t ht)
        (hd s hs) (hmaps hs),
        P202.Geometry.SmoothMetrics.tangentNorm_smul]
      change _ * (|a s| * c.speed (φ s)) = _
      ring
    _ = _ := intervalIntegral_density_reparam_nonneg
      (fun t => inwardCurveCurvature C g c.curve c.tangent N c.speed t * c.speed t) φ a l r hφ
      (by simpa only [min_eq_left hlr, max_eq_right hlr] using hd)
      (by simpa only [min_eq_left hlr, max_eq_right hlr] using fun s hs => (ha s hs).le)

/-- Complete decreasing parameter transport for the actual curvature times
metric speed; the output interval has the increasing image orientation. -/
theorem regularArc_curvatureIntegral_reparam_neg
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t))
    (φ a : ℝ → ℝ) (l r : ℝ) (hlr : l ≤ r)
    (ha : ∀ t ∈ Ioo l r, a t < 0)
    (hφ : ContinuousOn φ (uIcc l r))
    (hd : ∀ s ∈ Ioo l r, HasDerivAt φ (a s) s)
    (hmaps : MapsTo φ (Ioo l r) (Ioo c.left c.right)) :
    (∫ s in l..r,
      inwardCurveCurvature C g (c.curve ∘ φ)
        (unitTangent g (c.curve ∘ φ) (fun t => a t • c.velocity (φ t)))
        (fun t => N (φ t))
        (fun t => tangentNorm g (c.curve (φ t)) (a t • c.velocity (φ t))) s *
          tangentNorm g (c.curve (φ s)) (a s • c.velocity (φ s))) =
      ∫ t in φ r..φ l, inwardCurveCurvature C g c.curve c.tangent N c.speed t * c.speed t := by
  calc
    _ = ∫ s in l..r,
        (inwardCurveCurvature C g c.curve c.tangent N c.speed (φ s) * c.speed (φ s)) * |a s| := by
      apply intervalIntegral.integral_congr_Ioo_of_le hlr
      intro s hs
      dsimp only
      rw [regularArc_curvature_reparam_neg g C c N φ a s
        (by filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht; exact ha t ht)
        (hd s hs) (hmaps hs),
        P202.Geometry.SmoothMetrics.tangentNorm_smul]
      change _ * (|a s| * c.speed (φ s)) = _
      ring
    _ = _ := intervalIntegral_density_reparam_nonpos
      (fun t => inwardCurveCurvature C g c.curve c.tangent N c.speed t * c.speed t) φ a l r hφ
      (by simpa only [min_eq_left hlr, max_eq_right hlr] using hd)
      (by simpa only [min_eq_left hlr, max_eq_right hlr] using fun s hs => (ha s hs).le)

end P202.GlobalGaussBonnet
end Round3BoundaryTransport


/-! Continuation: Round3MetricSectors. -/
section Round3MetricSectors


open scoped Real
namespace P202.GlobalGaussBonnet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]

/-- Complementary turns at the two convex sectors in a tangent half-plane.
No assumption about metric orthogonality of the source rays is used. -/
theorem complementary_abs_metric_turns (o : Orientation ℝ V (Fin 2))
    {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) :
    |(o.oangle (-u) v).toReal| + |(o.oangle (-v) (-u)).toReal| = Real.pi := by
  rw [← o.angle_eq_abs_oangle_toReal (neg_ne_zero.mpr hu) hv,
    ← o.angle_eq_abs_oangle_toReal (neg_ne_zero.mpr hv) (neg_ne_zero.mpr hu),
    InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_neg,
    InnerProductGeometry.angle_comm v u]
  ring

/-- Four actual short turns at a transverse crossing have absolute sum 2π.
The four tangent rays can be an arbitrary injective linear image of the two
coordinate axes; in particular their metric angles need not be right angles. -/
theorem crossing_abs_metric_turns (o : Orientation ℝ V (Fin 2))
    {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) :
    |(o.oangle (-u) v).toReal| + |(o.oangle (-v) (-u)).toReal| +
      |(o.oangle u (-v)).toReal| + |(o.oangle v u).toReal| = 2 * Real.pi := by
  rw [o.oangle_neg_left_eq_neg_right, o.oangle_neg_neg]
  have h := complementary_abs_metric_turns o hu hv
  rw [o.oangle_neg_left_eq_neg_right, o.oangle_neg_neg] at h
  linarith

end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.SurfaceBoundaryData P202Specs.PlanarRegionTopology P202Specs.LocalGaussBonnet
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

theorem chartVector_smul (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x v : Plane) (r : ℝ) :
    chartVector c hc x (r • v) = r • chartVector c hc x v := by
  unfold chartVector
  split <;> simp

/-- Actual signed short metric turn of two coordinate tangent vectors at one
point; this is the arbitrary-vector version of `metricCornerAngle`. -/
def metricChartTurn (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u v : Plane) : ℝ := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact ((P202.SurfaceBoundaryData.planeOrientation g o p).oangle
    (chartVector c hc x u) (chartVector c hc x v)).toReal

theorem metricChartTurn_pos_smul (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u v : Plane) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    metricChartTurn g o c hc x (r • u) (t • v) = metricChartTurn g o c hc x u v := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  unfold metricChartTurn
  simp only [chartVector_smul]
  rw [Orientation.oangle_smul_left_of_pos _ _ _ hr,
    Orientation.oangle_smul_right_of_pos _ _ _ ht]

theorem metricChartTurn_self (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x v : Plane) : metricChartTurn g o c hc x v v = 0 := by
  simp [metricChartTurn]

theorem metricCornerAngle_eq_zero_of_pos_smul {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : P202Specs.PlaneTurning.ArcPresentation q) (j : Fin A.count)
    {r : ℝ} (hr : 0 < r)
    (hvel : P202Specs.PlaneTurning.velocity A (finRotate A.count j) 0 =
      r • P202Specs.PlaneTurning.velocity A j 1) :
    metricCornerAngle g o c hc A j = 0 := by
  change metricChartTurn g o c hc (A.arc j 1) _ _ = 0
  rw [hvel]
  calc
    metricChartTurn g o c hc (A.arc j 1) _ _ =
        metricChartTurn g o c hc (A.arc j 1)
          (P202Specs.PlaneTurning.velocity A j 1)
          (P202Specs.PlaneTurning.velocity A j 1) := by
      simpa only [one_smul] using
        metricChartTurn_pos_smul g o c hc (A.arc j 1)
          (P202Specs.PlaneTurning.velocity A j 1)
          (P202Specs.PlaneTurning.velocity A j 1) zero_lt_one hr
    _ = 0 := metricChartTurn_self _ _ _ _ _ _

/-- The actual metric corner angle depends only on the two oriented tangent
rays, so changing the positive speeds of a boundary presentation preserves it. -/
theorem metricCornerAngle_eq_of_pos_smul_velocities
    {q₁ q₂ : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : P202Specs.PlaneTurning.ArcPresentation q₁)
    (B : P202Specs.PlaneTurning.ArcPresentation q₂) (j : Fin A.count) (k : Fin B.count)
    (hp : B.arc k 1 = A.arc j 1) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hin : P202Specs.PlaneTurning.velocity B k 1 =
      r • P202Specs.PlaneTurning.velocity A j 1)
    (hout : P202Specs.PlaneTurning.velocity B (finRotate B.count k) 0 =
      t • P202Specs.PlaneTurning.velocity A (finRotate A.count j) 0) :
    metricCornerAngle g o c hc B k = metricCornerAngle g o c hc A j := by
  change metricChartTurn g o c hc (B.arc k 1) _ _ =
    metricChartTurn g o c hc (A.arc j 1) _ _
  rw [hp, hin, hout, metricChartTurn_pos_smul g o c hc _ _ _ hr ht]

end P202.GlobalGaussBonnet

open Set
namespace P202.GlobalGaussBonnet
open P202Specs.PlaneTurning P202Specs.PlanarRegionTopology

/-- At a smooth parameter of the underlying original curve, the presentation
velocity is its actual derivative multiplied by the positive parameter width.
At t=0 and t=1 this follows from uniqueness of the one-sided derivative. -/
theorem arcPresentation_velocity_of_differentiable {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ (realLift q.parametrization)
      (A.time j.castSucc + (A.time j.succ - A.time j.castSucc) * t)) :
    velocity A j t = (A.time j.succ - A.time j.castSucc) •
      deriv (realLift q.parametrization)
        (A.time j.castSucc + (A.time j.succ - A.time j.castSucc) * t) := by
  have hcomp := hd.hasDerivAt.scomp t
    (((hasDerivAt_id t).const_mul (A.time j.succ - A.time j.castSucc)).const_add
      (A.time j.castSucc))
  have he : HasDerivWithinAt (A.arc j)
      ((A.time j.succ - A.time j.castSucc) •
        deriv (realLift q.parametrization)
          (A.time j.castSucc + (A.time j.succ - A.time j.castSucc) * t))
      (Icc 0 1) t := by
    simpa using hcomp.hasDerivWithinAt.congr_of_mem (fun z hz => A.agrees j z hz) ht
  exact (uniqueDiffOn_Icc_zero_one t ht).eq_deriv _
    (differentiableAt_of_deriv_ne_zero (A.regular j t ht)).hasDerivAt.hasDerivWithinAt he

theorem arcPresentation_velocity_pos_smul_at_smooth_join {q : RegularJordanCurve}
    (A : ArcPresentation q) (j k : Fin A.count) (hjk : j.val + 1 = k.val)
    (hd : DifferentiableAt ℝ (realLift q.parametrization) (A.time j.succ)) :
    ∃ r : ℝ, 0 < r ∧ velocity A k 0 = r • velocity A j 1 := by
  have htime : A.time j.succ = A.time k.castSucc := congrArg A.time (Fin.ext hjk)
  have hdiffR : DifferentiableAt ℝ (realLift q.parametrization)
      (A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * 0) := by
    simpa only [mul_zero,add_zero,← htime] using hd
  have hdiffL : DifferentiableAt ℝ (realLift q.parametrization)
      (A.time j.castSucc + (A.time j.succ - A.time j.castSucc) * 1) := by
    simpa only [mul_one,add_sub_cancel] using hd
  have hL := arcPresentation_velocity_of_differentiable A j (by simp : (1 : ℝ) ∈ Icc 0 1) hdiffL
  have hR := arcPresentation_velocity_of_differentiable A k (by simp : (0 : ℝ) ∈ Icc 0 1) hdiffR
  have hwj : 0 < A.time j.succ - A.time j.castSucc := sub_pos.mpr (A.strictMono (by simp))
  have hwk : 0 < A.time k.succ - A.time k.castSucc := sub_pos.mpr (A.strictMono (by simp))
  refine ⟨(A.time k.succ - A.time k.castSucc) / (A.time j.succ - A.time j.castSucc),
    div_pos hwk hwj, ?_⟩
  rw [hR,hL,smul_smul,div_mul_cancel₀ _ hwj.ne']
  simp [← htime]

/-- The original circle parametrization has identical derivatives on either
side of the selected period endpoint. No regularity assumption is needed for
this equality of the actual `deriv` values. -/
theorem realLift_deriv_one_eq_deriv_zero (c : C(ParameterCircle, Plane)) :
    deriv (realLift c) 1 = deriv (realLift c) 0 := by
  have hfun : (fun t : ℝ => realLift c (t + 1)) = realLift c := by
    funext t
    simp [realLift]
  have h := deriv_comp_add_const (realLift c) 1 0
  simpa only [hfun, zero_add] using h.symm

/-- Every smooth join of the original circle curve has positively proportional
incoming and outgoing presentation velocities, including the cyclic join. -/
theorem arcPresentation_velocities_pos_smul_at_smooth_join {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count)
    (hd : DifferentiableAt ℝ (realLift q.parametrization) (A.time j.succ)) :
    ∃ r : ℝ, 0 < r ∧
      velocity A (finRotate A.count j) 0 = r • velocity A j 1 := by
  letI : NeZero A.count := ⟨A.positive.ne'⟩
  by_cases hn : j.val + 1 < A.count
  · let k : Fin A.count := ⟨j.val + 1, hn⟩
    have hrot : finRotate A.count j = k := by
      rw [finRotate_apply]
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      exact Nat.mod_eq_of_lt hn
    rw [hrot]
    exact arcPresentation_velocity_pos_smul_at_smooth_join A j k rfl hd
  · let z : Fin A.count := ⟨0,A.positive⟩
    have hj : j.val + 1 = A.count := by omega
    have hrot : finRotate A.count j = z := by
      rw [finRotate_apply]
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      change (j.val + 1) % A.count = 0
      rw [hj, Nat.mod_self]
    have hjlast : j.succ = Fin.last A.count := Fin.ext hj
    have hjtime : A.time j.succ = 1 := hjlast ▸ A.last
    have hztime : A.time z.castSucc = 0 := A.first
    have hd1 : DifferentiableAt ℝ (realLift q.parametrization) 1 := hjtime ▸ hd
    have hfun : (fun t : ℝ => realLift q.parametrization (t + 1)) =
        realLift q.parametrization := by funext t; simp [realLift]
    have hd0 : DifferentiableAt ℝ (realLift q.parametrization) 0 := by
      have hd1' : DifferentiableAt ℝ (realLift q.parametrization) ((0 : ℝ) + 1) := by
        simpa using hd1
      have h := hd1'.comp (0 : ℝ) ((differentiableAt_id (𝕜 := ℝ) (x := (0 : ℝ))).add_const 1)
      change DifferentiableAt ℝ (fun t : ℝ => realLift q.parametrization (t + 1)) 0 at h
      rwa [hfun] at h
    have hdiffR : DifferentiableAt ℝ (realLift q.parametrization)
        (A.time z.castSucc + (A.time z.succ - A.time z.castSucc) * 0) := by
      simpa only [mul_zero,add_zero,hztime] using hd0
    have hdiffL : DifferentiableAt ℝ (realLift q.parametrization)
        (A.time j.castSucc + (A.time j.succ - A.time j.castSucc) * 1) := by
      simpa only [mul_one,add_sub_cancel] using hd
    have hL := arcPresentation_velocity_of_differentiable A j
      (by simp : (1 : ℝ) ∈ Icc 0 1) hdiffL
    have hR := arcPresentation_velocity_of_differentiable A z
      (by simp : (0 : ℝ) ∈ Icc 0 1) hdiffR
    have hwj : 0 < A.time j.succ - A.time j.castSucc := sub_pos.mpr (A.strictMono (by simp))
    have hwz : 0 < A.time z.succ - A.time z.castSucc := sub_pos.mpr (A.strictMono (by simp))
    refine ⟨(A.time z.succ - A.time z.castSucc) / (A.time j.succ - A.time j.castSucc),
      div_pos hwz hwj, ?_⟩
    rw [hrot,hR,hL,smul_smul,div_mul_cancel₀ _ hwj.ne']
    simp only [mul_zero,add_zero,mul_one,add_sub_cancel,hjtime,hztime,
      realLift_deriv_one_eq_deriv_zero]

end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202.MetricData P202Specs.PlanarRegionTopology P202Specs.LocalGaussBonnet
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

/-- A geometric same-ray identification of the actual one-sided coordinate
velocities is sufficient, even when their speeds jump at the original join. -/
theorem metricCornerAngle_eq_zero_of_sameRay {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : P202Specs.PlaneTurning.ArcPresentation q) (j : Fin A.count)
    (h : SameRay ℝ (P202Specs.PlaneTurning.velocity A j 1)
      (P202Specs.PlaneTurning.velocity A (finRotate A.count j) 0)) :
    metricCornerAngle g o c hc A j = 0 := by
  obtain ⟨r, hr, hvel⟩ := h.exists_pos_left
    (A.regular j 1 (by simp)) (A.regular (finRotate A.count j) 0 (by simp))
  exact metricCornerAngle_eq_zero_of_pos_smul g o c hc A j hr hvel.symm

/-- Extra subdivision endpoints where the actual original curve is smooth
contribute exactly zero to the actual metric exterior-angle sum. The cyclic
endpoint is included. -/
theorem metricCornerAngle_eq_zero_at_smooth_join {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : P202Specs.PlaneTurning.ArcPresentation q) (j : Fin A.count)
    (hd : DifferentiableAt ℝ (realLift q.parametrization) (A.time j.succ)) :
    metricCornerAngle g o c hc A j = 0 := by
  obtain ⟨r, hr, hvel⟩ := arcPresentation_velocities_pos_smul_at_smooth_join A j hd
  exact metricCornerAngle_eq_zero_of_pos_smul g o c hc A j hr hvel

theorem metricCornerAngle_eq_zero_of_not_join {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : P202Specs.PlaneTurning.ArcPresentation q) (j : Fin A.count)
    (hjoin : (A.time j.succ : ParameterCircle) ∉ q.joins) :
    metricCornerAngle g o c hc A j = 0 := by
  exact metricCornerAngle_eq_zero_at_smooth_join g o c hc A j
    ((q.smooth_off_joins (A.time j.succ) hjoin).differentiableAt (by simp))

theorem interiorAngle_eq_pi_at_smooth_join {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : P202Specs.PlaneTurning.ArcPresentation q) (s : ℝ) (j : Fin A.count)
    (hd : DifferentiableAt ℝ (realLift q.parametrization) (A.time j.succ)) :
    interiorAngle g o c hc A s j = Real.pi := by
  simp only [interiorAngle, metricCornerAngle_eq_zero_at_smooth_join g o c hc A j hd,
    mul_zero, sub_zero]

end P202.GlobalGaussBonnet
end Round3MetricSectors


/-! Continuation: Round3GramMetricPreserving. -/
section Round3GramMetricPreserving
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.TangentBundleData
open P202.MetricData P202.VolumeData
namespace P202.GlobalGaussBonnet
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}
/-- Equality of actual coordinate Gram matrices proves metric preservation
for every tangent vector. The differential itself is determined by the given
matching coordinates, also when the model kinds differ across a seam. -/
theorem gramMatrix_metricPreserving_at
    (f : M → N) (hf : IsSmoothMap S W f) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : IsDifferential S W f p L)
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ W.smoothStructure.val)
    (hp : p ∈ c.source) (hfp : f p ∈ d.source)
    (hcoord : (fun q => (c q).val) =ᶠ[𝓝 p] (fun q => (d (f q)).val))
    (K : FiberCoordinates S) (J : FiberCoordinates W)
    (hgram : gramMatrix g K c hc ⟨p, hp⟩ = gramMatrix h J d hd ⟨f p, hfp⟩)
    (v w : TangentSpace S p) :
    pairing h (f p) (L v) (L w) = pairing g p v w := by
  let E := K.equiv c hc p hp
  let F := J.equiv d hd (f p) hfp
  have hvec (x : Euclidean n) : L (E.symm x) = F.symm x := by
    apply F.injective
    rw [differential_matching_coordinates f hf p L hL c d hc hd hp hfp hcoord K J,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let b := (Pi.basisFun ℝ (Fin n)).map E.symm
  let B : LinearMap.BilinForm ℝ (TangentSpace S p) :=
    (pairing h (f p)).compl₁₂ L L
  have hB : B = pairing g p := by
    apply LinearMap.BilinForm.ext_basis b
    intro i j
    change pairing h (f p) (L (E.symm ((Pi.basisFun ℝ (Fin n)) i)))
      (L (E.symm ((Pi.basisFun ℝ (Fin n)) j))) =
      pairing g p (E.symm ((Pi.basisFun ℝ (Fin n)) i))
        (E.symm ((Pi.basisFun ℝ (Fin n)) j))
    rw [hvec, hvec]
    exact congrFun (congrFun hgram.symm i) j
  exact congrArg (fun B : LinearMap.BilinForm ℝ (TangentSpace S p) => B v w) hB
end P202.GlobalGaussBonnet
end Round3GramMetricPreserving


/-! Continuation: Round3MetricExtensionMap. -/
section Round3MetricExtensionMap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical BigOperators Matrix.Norms.Elementwise
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.DifferentialData
open P202.MetricData P202.VolumeData
namespace P202.GlobalGaussBonnet

/-- Equality of the full coordinate Grams gives actual metric preservation
under a smooth map with the same full-dimensional coordinates. -/
theorem metricPreserving_of_matching_gramMatrix
    {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {Q : SmoothManifold n b N}
    (f : M → N) (hf : IsSmoothMap S Q f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace Q (f p))
    (hL : ∀ p, IsDifferential S Q f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric Q)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hsource : c.source = univ)
    (d : ModelChart n b N) (hd : d ∈ Q.smoothStructure.val)
    (hs : ∀ p ∈ c.source, f p ∈ d.source)
    (hcoord : ∀ p ∈ c.source, (c p).val = (d (f p)).val)
    (K : FiberCoordinates S) (J : FiberCoordinates Q)
    (hgram : ∀ p : c.source,
      gramMatrix g K c hc p = gramMatrix h J d hd ⟨f p.val, hs p.val p.property⟩) :
    IsMetricPreserving g h f L := by
  intro p v w
  have hp : p ∈ c.source := by rw [hsource]; trivial
  let EK := K.equiv c hc p hp
  let EJ := J.equiv d hd (f p) (hs p hp)
  have hvec (v : TangentSpace S p) : EJ (L p v) = EK v := by
    exact differential_matching_coordinates f hf p (L p) (hL p) c d hc hd hp (hs p hp)
      (by filter_upwards [c.open_source.mem_nhds hp] with q hq; exact hcoord q hq) K J v
  rw [P202.Geometry.SmoothMetrics.bilinear_coordinates EJ (pairing h (f p)) (L p v) (L p w),
    P202.Geometry.SmoothMetrics.bilinear_coordinates EK (pairing g p) v w, hvec, hvec]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hentry := congrFun (congrFun (hgram ⟨p, hp⟩) j) k
  simp only [gramMatrix, Matrix.of_apply, Pi.basisFun_apply] at hentry
  change pairing g p (EK.symm (Pi.single j 1)) (EK.symm (Pi.single k 1)) =
    pairing h (f p) (EJ.symm (Pi.single j 1)) (EJ.symm (Pi.single k 1)) at hentry
  rw [hentry]

/-- A full-source pair of charts with identical ambient coordinates gives a
smooth immersion even at a genuine boundary seam. -/
theorem exists_matchingChart_immersion
    {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (Q : SmoothManifold n b N)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hsource : c.source = univ)
    (d : ModelChart n b N) (hd : d ∈ Q.smoothStructure.val)
    (f : M → N) (hs : ∀ p, f p ∈ d.source)
    (hcoord : ∀ p, (c p).val = (d (f p)).val)
    (hcont : Continuous f) :
    ∃ i : SmoothImmersion S Q f,
      ∀ p v, (tangentStructure Q).fiberCoordinates.equiv d hd (f p) (hs p)
        (i.differential p v) =
          (tangentStructure S).fiberCoordinates.equiv c hc p (by rw [hsource]; trivial) v := by
  have hf : IsSmoothMap S Q f := by
    intro p
    have hp : p ∈ c.source := by rw [hsource]; trivial
    apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      S.smoothStructure.property.1 Q.smoothStructure.property.1 f p).mpr
    exact ⟨hcont.continuousAt, c, hc, d, hd, hp, hs p,
      univ, isOpen_univ, mem_univ _, id, contDiff_id.contDiffOn,
      Filter.Eventually.of_forall hcoord⟩
  let L := SmoothManifolds.differential S Q f hf
  have hL := SmoothManifolds.differential_spec S Q f hf
  have heq (p : M) (v : TangentSpace S p) :
      (tangentStructure Q).fiberCoordinates.equiv d hd (f p) (hs p) (L p v) =
        (tangentStructure S).fiberCoordinates.equiv c hc p (by rw [hsource]; trivial) v :=
    differential_matching_coordinates f hf p (L p) (hL p) c d hc hd
      (by rw [hsource]; trivial) (hs p) (Filter.Eventually.of_forall hcoord)
      (tangentStructure S).fiberCoordinates (tangentStructure Q).fiberCoordinates v
  refine ⟨⟨hf, L, hL, ?_⟩, heq⟩
  intro p v w hvw
  apply ((tangentStructure S).fiberCoordinates.equiv c hc p (by rw [hsource]; trivial)).injective
  rw [← heq p v, ← heq p w, hvw]

open private transportManifold from
  MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.QuotientBundles

/-- Lift the ambient coordinate manifold into the source universe; this is
needed by the original same-universe metric and immersion interfaces. -/
theorem exists_openEuclideanChartMetric_lift
    {n : ℕ} (U : Set (Euclidean n)) (hU : IsOpen U) (hne : U.Nonempty)
    (F : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hpos : ∀ x ∈ U, (F x).PosDef) :
    ∃ Q : SmoothManifold n .euclidean (ULift.{u} U),
      ∃ d : ModelChart n .euclidean (ULift.{u} U), ∃ hd : d ∈ Q.smoothStructure.val,
        d.source = univ ∧ (∀ p : ULift.{u} U, (d p).val = p.down.val) ∧
        ∃ g : RiemannianMetric Q,
          ∀ p : d.source, P202.VolumeData.gramMatrix g
            (tangentStructure Q).fiberCoordinates d hd p = F p.val.down.val := by
  obtain ⟨Q₀, d₀, hd₀, hs₀, hv₀, _, _⟩ := exists_openEuclideanChartMetric U hU hne F hF hpos
  let Q := transportManifold Q₀ (Homeomorph.ulift.symm : U ≃ₜ ULift.{u} U)
  let d := (Homeomorph.ulift : ULift.{u} U ≃ₜ U).toOpenPartialHomeomorph.trans d₀
  have hd : d ∈ Q.smoothStructure.val := ⟨d₀, hd₀, rfl⟩
  have hsource : d.source = univ := by
    ext p
    change (p ∈ Set.univ ∧ p.down ∈ d₀.source) ↔ p ∈ Set.univ
    rw [hs₀]
    simp
  have hdval (p : ULift.{u} U) : (d p).val = p.down.val := hv₀ p.down
  have hpos' (p : ULift.{u} U) : (F (d p).val).PosDef := by
    rw [hdval]
    exact hpos p.down.val p.down.property
  let g := metricOfGlobalChart Q d hd hsource F hF hpos'
  refine ⟨Q, d, hd, hsource, hdval, g, ?_⟩
  intro p
  rw [metricOfGlobalChart_gramMatrix Q d hd hsource F hF hpos' p, hdval]

/-- The ambient extension with source-universe universe level, and with exact
metric coefficients on an open original neighborhood of the compact set. -/
theorem exists_chart_metric_lift_extension_near_compact
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 a M) (g : RiemannianMetric S)
    (e : ModelChart 2 a M) (he : e ∈ S.smoothStructure.val)
    (A : Set e.source) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ V : Set e.source, IsOpen V ∧ A ⊆ V ∧
      ∃ U : Set (Euclidean 2), IsOpen U ∧ metricChartEmbedding e '' V ⊆ U ∧
        ∃ Q : SmoothManifold 2 .euclidean (ULift.{u} U),
          ∃ d : ModelChart 2 .euclidean (ULift.{u} U), ∃ hd : d ∈ Q.smoothStructure.val,
            d.source = univ ∧ (∀ p : ULift.{u} U, (d p).val = p.down.val) ∧
            ∃ h : RiemannianMetric Q,
              ∀ p ∈ V, ∀ q : d.source, q.val.down.val = metricChartEmbedding e p →
                gramMatrix h (tangentStructure Q).fiberCoordinates d hd q =
                  gramMatrix g (tangentStructure S).fiberCoordinates e he p := by
  let _ : LocallyCompactSpace M := SmoothManifolds.TopologicalManifold.locallyCompactSpace S.topologicalManifold
  let _ : LocallyCompactSpace e.source := e.open_source.locallyCompactSpace
  obtain ⟨A', hA', hAA'⟩ := exists_compact_superset hA
  obtain ⟨U, hU, hAU, F, hF, heF, hpos⟩ := exists_chartMetricMatrix_extension
    (libraryMetric g) (tangentStructure S).fiberCoordinates e he A' hA'
  have hneU : U.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨metricChartEmbedding e p, hAU ⟨p, interior_subset (hAA' hp), rfl⟩⟩
  obtain ⟨Q, d, hd, hs, hv, h, hGram⟩ := exists_openEuclideanChartMetric_lift.{u} U hU hneU F hF hpos
  refine ⟨interior A', isOpen_interior, hAA', U, hU, ?_, Q, d, hd, hs, hv, h, ?_⟩
  · exact (image_mono interior_subset).trans hAU
  · intro p hp q hq
    rw [hGram, hq, heF p (interior_subset hp)]
    rfl

/-- A compact chart region on either model lies in an actual open restriction
whose metric immerses isometrically into a Euclidean-model ambient extension.
The ambient and original charts have IDENTICAL ambient coordinates; this is
an immersion at a seam, and requires no local inverse across that seam. -/
theorem exists_chart_metric_extension_immersion
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 a M) (g : RiemannianMetric S)
    (e : ModelChart 2 a M) (he : e ∈ S.smoothStructure.val)
    (A : Set e.source) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ W : Set M, ∃ _hW : IsOpen W, Subtype.val '' A ⊆ W ∧ W ⊆ e.source ∧
      ∃ R : SmoothManifold 2 a W, ∃ i : SmoothImmersion R S Subtype.val,
        ∃ c : ModelChart 2 a W, ∃ _hc : c ∈ R.smoothStructure.val,
          c.source = univ ∧ (∀ p : W, c p = e p.val) ∧
          ∃ U : Set (Euclidean 2), IsOpen U ∧
            ∃ Q : SmoothManifold 2 .euclidean (ULift.{u} U),
              ∃ h : RiemannianMetric Q,
                ∃ d : ModelChart 2 .euclidean (ULift.{u} U),
                  ∃ _hd : d ∈ Q.smoothStructure.val, d.source = univ ∧
                    ∃ f : W → ULift.{u} U, ∃ j : SmoothImmersion R Q f,
                      (∀ p : W, (c p).val = (d (f p)).val) ∧
                      IsMetricPreserving (P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i)
                        h f j.differential := by
  obtain ⟨V, hV, hAV, U, hU, hVU, Q, d, hd, hds, hdval, h, hGram⟩ :=
    exists_chart_metric_lift_extension_near_compact S g e he A hA hne
  let W : Set M := (Subtype.val : e.source → M) '' V
  have hW : IsOpen W := e.open_source.isOpenMap_subtype_val V hV
  have hWe : W ⊆ e.source := by
    rintro p ⟨q, hq, rfl⟩
    exact q.property
  have hVp (p : W) : (⟨p.val, hWe p.property⟩ : e.source) ∈ V := by
    obtain ⟨q, hq, hqp⟩ := p.property
    have hqeq : q = (⟨p.val, hWe p.property⟩ : e.source) := Subtype.ext hqp
    rwa [← hqeq]
  have hAW : Subtype.val '' A ⊆ W := image_mono hAV
  obtain ⟨R, _, hRA, _⟩ := SmoothManifolds.exists_openSubset_smoothManifold S W hW
  have hinc := (SmoothManifolds.TransversePreimage.open_subset_embedded_of_atlas_eq
    S W hW R hRA).1
  obtain ⟨i⟩ := (P202.Geometry.SmoothMetrics.smoothImmersion_iff R S Subtype.val).mpr
    ⟨hinc.1, hinc.2.2.1⟩
  have hneW : Nonempty W := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨⟨p.val, ⟨p, hAV hp, rfl⟩⟩⟩
  let c := e.subtypeRestr (s := ⟨W, hW⟩) hneW
  have hc : c ∈ R.smoothStructure.val := by
    rw [hRA]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _
        S.smoothStructure.property.1 W hW) ⟨hneW, e, he, rfl⟩
  have hcs : c.source = univ := by
    ext p
    simp only [c, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage,
      mem_univ, iff_true]
    exact hWe p.property
  let f : W → ULift.{u} U := fun p => ULift.up ⟨(e p.val).val,
    hVU ⟨⟨p.val, hWe p.property⟩, hVp p, rfl⟩⟩
  have hcoord (p : W) : (c p).val = (d (f p)).val := by
    rw [hdval]
    rfl
  have hfd (p : W) : f p ∈ d.source := by rw [hds]; trivial
  have hcfcont : Continuous (fun p : W => (c p).val) :=
    continuous_iff_continuousAt.mpr (fun p =>
      continuous_subtype_val.continuousAt.comp (c.continuousAt (by rw [hcs]; trivial)))
  have hfcont : Continuous f :=
    Homeomorph.ulift.symm.continuous.comp (hcfcont.subtype_mk _)
  obtain ⟨j, hjcoord⟩ := exists_matchingChart_immersion R Q c hc hcs d hd f hfd hcoord hfcont
  let gR := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i
  have him : IsMetricPreserving gR g Subtype.val i.differential := fun _ _ _ => rfl
  have hgr (p : c.source) :
      gramMatrix gR (tangentStructure R).fiberCoordinates c hc p =
        gramMatrix h (tangentStructure Q).fiberCoordinates d hd ⟨f p.val, hfd p.val⟩ := by
    have hgrS := metricPreserving_gramMatrix Subtype.val i.smooth i.differential
      i.isDifferential gR g him c e hc he p (hWe p.val.property)
      (Filter.Eventually.of_forall (fun _ => rfl))
      (tangentStructure R).fiberCoordinates (tangentStructure S).fiberCoordinates
    have hgrQ := hGram ⟨p.val.val, hWe p.val.property⟩ (hVp p.val)
      ⟨f p.val, hfd p.val⟩ rfl
    exact hgrS.trans hgrQ.symm
  have hjm := metricPreserving_of_matching_gramMatrix f j.smooth j.differential
    j.isDifferential gR h c hc hcs d hd (fun p _ => hfd p) (fun p _ => hcoord p)
    (tangentStructure R).fiberCoordinates (tangentStructure Q).fiberCoordinates hgr
  exact ⟨W, hW, hAW, hWe, R, i, c, hc, hcs, (fun _ => rfl),
    U, hU, Q, h, d, hd, hds, f, j, hcoord, hjm⟩

end P202.GlobalGaussBonnet
end Round3MetricExtensionMap


/-! Continuation: Round3OrientedExtension. -/
section Round3OrientedExtension
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.TangentBundleData
open SmoothManifolds.BundleOperationsData SmoothManifolds.OrientationData
open P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
namespace P202.GlobalGaussBonnet
/-- Every compact chart piece of either original surface model has an actual
oriented ambient Riemannian extension in the SAME universe. The comparison
with the original Gaussian curvature is proved even on the genuine seam. -/
theorem exists_oriented_chart_metric_extension
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 a M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (e : ModelChart 2 a M) (he : e ∈ S.smoothStructure.val)
    (A : Set e.source) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ W : Set M, ∃ _hW : IsOpen W, Subtype.val '' A ⊆ W ∧ W ⊆ e.source ∧
      ∃ R : SmoothManifold 2 a W, ∃ i : SmoothImmersion R S Subtype.val,
        ∃ c : ModelChart 2 a W, ∃ _hc : c ∈ R.smoothStructure.val,
          c.source = univ ∧ (∀ p : W, c p = e p.val) ∧
          ∃ U : Set (Euclidean 2), IsOpen U ∧
            ∃ Q : SmoothManifold 2 .euclidean (ULift.{u} U),
              ∃ h : RiemannianMetric Q,
                ∃ K : Connection (tangentBundle Q), IsLeviCivita h K ∧
                  ∃ TQ : CurvatureTensor Q, RepresentsCurvature K TQ ∧
                    ∃ d : ModelChart 2 .euclidean (ULift.{u} U),
                      ∃ hd : d ∈ Q.smoothStructure.val, d.source = univ ∧
                        ∃ f : W → ULift.{u} U, ∃ j : SmoothImmersion R Q f,
                          (∀ p : W, (c p).val = (d (f p)).val) ∧
                          IsMetricPreserving (P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i)
                            h f j.differential ∧
                          (∀ p : W, P202Specs.GlobalGaussBonnet.gaussianCurvature g T p.val =
                            P202Specs.GlobalGaussBonnet.gaussianCurvature h TQ (f p)) ∧
                          ∃ o : Orientation Q, ∀ B : CotangentBundle Q,
                            P202Specs.ChartRegionStokes.PositiveChart B o d hd := by
  obtain ⟨W, hW, hAW, hWe, R, i, c, hc, hcs, hcval, U, hU, Q, h, d, hd, hds,
    f, j, hcoord, hm⟩ := exists_chart_metric_extension_immersion S g e he A hA hne
  let gR := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i
  obtain ⟨CR, hCR, _⟩ := P202.Geometry.LeviCivita.exists_unique gR
  obtain ⟨TR, hTR, _⟩ := P202.Geometry.CurvatureAlgebra.tensor_exists_unique CR
  obtain ⟨K, hK, _⟩ := P202.Geometry.LeviCivita.exists_unique h
  obtain ⟨TQ, hTQ, _⟩ := P202.Geometry.CurvatureAlgebra.tensor_exists_unique K
  refine ⟨W, hW, hAW, hWe, R, i, c, hc, hcs, hcval, U, hU, Q, h,
    K, hK, TQ, hTQ, d, hd, hds, f, j, hcoord, hm, ?_, ?_⟩
  · intro p
    have hp : p ∈ c.source := by rw [hcs]; trivial
    have hi := matchingChart_gaussianCurvature Subtype.val i.smooth i.differential
      i.isDifferential gR g (fun _ _ _ => rfl) ⟨c, hc⟩ ⟨e, he⟩
      (fun q _ => hWe q.property) (fun q _ => congrArg Subtype.val (hcval q))
      CR C hCR hC TR T hTR hT p hp
    have hj := matchingChart_gaussianCurvature f j.smooth j.differential
      j.isDifferential gR h hm ⟨c, hc⟩ ⟨d, hd⟩
      (fun q _ => by rw [hds]; trivial) (fun q _ => hcoord q)
      CR K hCR hK TR TQ hTR hTQ p hp
    exact hi.symm.trans hj
  · refine ⟨globalChartOrientation (tangentStructure Q).fiberCoordinates d hd hds, ?_⟩
    exact fun B => globalChartOrientation_positive
      (tangentStructure Q).fiberCoordinates d hd hds B
end P202.GlobalGaussBonnet
end Round3OrientedExtension


/-! Continuation: Round3BoundaryRefinement. -/
section Round3BoundaryRefinement
set_option autoImplicit false
open Set Filter
open scoped Topology
open scoped Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet

/-- A connected nonempty set lies in a single member of a finite closed
cover whenever each point has a unique covering index. -/
theorem connected_subset_one_finite_closed_cover
    {X I : Type*} [TopologicalSpace X] [Finite I]
    {A : Set X} (hA : IsConnected A) (F : I → Set X)
    (hF : ∀ i, IsClosed (F i)) (hcover : A ⊆ ⋃ i, F i)
    (hunique : ∀ x ∈ A, ∀ i j, x ∈ F i → x ∈ F j → i = j) :
    ∃ i, A ⊆ F i := by
  obtain ⟨x, hx⟩ := hA.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let G : Set X := ⋃ j, ⋃ (_ : j ≠ i), F j
  have hG : IsClosed G :=
    isClosed_iUnion_of_finite (fun j => isClosed_iUnion_of_finite (fun _ => hF j))
  have hAG : A ⊆ F i ∪ G := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    · exact Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hji, hyj⟩⟩)
  have hdisj : A ∩ (F i ∩ G) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hy, hyi, hyG⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyG
    obtain ⟨hji, hyj⟩ := mem_iUnion.mp hj
    exact hji (hunique y hy j i hyj hyi)
  obtain h | h := isPreconnected_iff_subset_of_disjoint_closed.mp hA.isPreconnected
    (F i) G (hF i) hG hAG hdisj
  · exact ⟨i, h⟩
  · have hxG := h hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxG
    obtain ⟨hji, hxj⟩ := mem_iUnion.mp hj
    exact (hji (hunique x hx j i hxj hxi)).elim

variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- All endpoint images of the finite presentation, with duplicates removed
by set union. No endpoint multiplicity is imposed. -/
def boundaryEndpointSet {g : RiemannianMetric S} (B : BoundaryPresentation g) : Set M :=
  ⋃ i, {(B.arc i).curve (B.arc i).left, (B.arc i).curve (B.arc i).right}

theorem boundaryEndpointSet_finite {g : RiemannianMetric S} (B : BoundaryPresentation g) :
    (boundaryEndpointSet B).Finite := by
  exact finite_iUnion (fun i => Set.toFinite _)

/-- Removing the endpoint images turns membership in a full arc into
membership in its embedded open arc. -/
theorem mem_openArc_of_mem_fullArc_not_endpoint
    {g : RiemannianMetric S} (B : BoundaryPresentation g) (i : Fin B.count)
    {p : M} (hp : p ∈ (B.arc i).curve '' Icc (B.arc i).left (B.arc i).right)
    (hne : p ∉ boundaryEndpointSet B) :
    p ∈ (B.arc i).curve '' Ioo (B.arc i).left (B.arc i).right := by
  obtain ⟨t, ht, rfl⟩ := hp
  have hleft : t ≠ (B.arc i).left := by
    intro he
    apply hne
    apply mem_iUnion.mpr
    exact ⟨i, by simp [he]⟩
  have hright : t ≠ (B.arc i).right := by
    intro he
    apply hne
    apply mem_iUnion.mpr
    exact ⟨i, by simp [he]⟩
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 hleft.symm, lt_of_le_of_ne ht.2 hright⟩, rfl⟩

/-- Away from the finite endpoint set, each boundary point belongs to exactly
one of the full compact arc images. -/
theorem fullArc_index_unique_off_endpoints
    {g : RiemannianMetric S} (B : BoundaryPresentation g) {p : M}
    (hne : p ∉ boundaryEndpointSet B) (i j : Fin B.count)
    (hi : p ∈ (B.arc i).curve '' Icc (B.arc i).left (B.arc i).right)
    (hj : p ∈ (B.arc j).curve '' Icc (B.arc j).left (B.arc j).right) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (B.disjoint hij)
    (mem_openArc_of_mem_fullArc_not_endpoint B i hi hne)
    (mem_openArc_of_mem_fullArc_not_endpoint B j hj hne)

/-- The topological localization used by a common refinement: every
connected subset avoiding the endpoint images lies in one embedded open arc. -/
theorem connected_boundary_subset_one_openArc
    {g : RiemannianMetric S} (B : BoundaryPresentation g) {A : Set M}
    (hA : IsConnected A)
    (hboundary : A ⊆ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (hne : Disjoint A (boundaryEndpointSet B)) :
    ∃ i, A ⊆ (B.arc i).curve '' Ioo (B.arc i).left (B.arc i).right := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  have hfull : ∃ i, A ⊆ (B.arc i).curve '' Icc (B.arc i).left (B.arc i).right := by
    apply connected_subset_one_finite_closed_cover hA
      (fun i => (B.arc i).curve '' Icc (B.arc i).left (B.arc i).right)
    · intro i
      exact (isCompact_Icc.image_of_continuousOn (B.arc i).continuous).isClosed
    · intro p hp
      rw [← B.covers]
      exact hboundary hp
    · intro p hp i j hi hj
      exact fullArc_index_unique_off_endpoints B
        (fun he => Set.disjoint_left.mp hne hp he) i j hi hj
  obtain ⟨i, hi⟩ := hfull
  exact ⟨i, fun p hp => mem_openArc_of_mem_fullArc_not_endpoint B i (hi hp)
    (fun he => Set.disjoint_left.mp hne hp he)⟩

/-- Only finitely many interior parameters of one embedded arc map to the
endpoint images of another finite presentation. These are the cut points for
the common refinement. -/
theorem boundaryEndpoint_cutParameters_finite
    {g : RiemannianMetric S} (B D : BoundaryPresentation g) (i : Fin B.count) :
    (Ioo (B.arc i).left (B.arc i).right ∩
      (B.arc i).curve ⁻¹' boundaryEndpointSet D).Finite := by
  apply Set.Finite.of_injOn (t := boundaryEndpointSet D)
    (fun t ht => ht.2) ((B.injective i).mono inter_subset_left)
  exact boundaryEndpointSet_finite D

/-- Every nontrivial open subinterval that avoids the finitely many cut
parameters lies in a single open arc of the other presentation. -/
theorem boundary_subarc_subset_one_openArc
    {g : RiemannianMetric S} (B D : BoundaryPresentation g) (i : Fin B.count)
    (l r : ℝ) (hlr : l < r)
    (hsub : Ioo l r ⊆ Ioo (B.arc i).left (B.arc i).right)
    (hcuts : Disjoint (Ioo l r) ((B.arc i).curve ⁻¹' boundaryEndpointSet D)) :
    ∃ j, (B.arc i).curve '' Ioo l r ⊆
      (D.arc j).curve '' Ioo (D.arc j).left (D.arc j).right := by
  apply connected_boundary_subset_one_openArc D
  · exact (isConnected_Ioo hlr).image _ ((B.arc i).continuous.mono
      (fun t ht => ⟨(hsub ht).1.le, (hsub ht).2.le⟩))
  · rintro p ⟨t, ht, rfl⟩
    rw [B.covers]
    exact mem_iUnion.mpr ⟨i, t, ⟨(hsub ht).1.le, (hsub ht).2.le⟩, rfl⟩
  · apply Set.disjoint_left.mpr
    rintro p ⟨t, ht, rfl⟩ hp
    exact Set.disjoint_left.mp hcuts ht hp

/-- Away from the finite endpoint set, every open parameter neighborhood of
an embedded arc gives a neighborhood in the genuine intrinsic boundary.
This supplies the topological locality needed before forming transition maps. -/
theorem boundary_openArc_neighborhood
    {g : RiemannianMetric S} (B : BoundaryPresentation g) (i : Fin B.count)
    {J : Set ℝ} (hJ : IsOpen J)
    (hsub : J ⊆ Ioo (B.arc i).left (B.arc i).right)
    {s : ℝ} (hs : s ∈ J) (hne : (B.arc i).curve s ∉ boundaryEndpointSet B) :
    ∃ U : Set M, IsOpen U ∧ (B.arc i).curve s ∈ U ∧
      SmoothManifolds.BoundaryData.intrinsicBoundary S ∩ U ⊆ (B.arc i).curve '' J := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  let K := Icc (B.arc i).left (B.arc i).right \ J
  let F : Set M := ⋃ j, ⋃ (_ : j ≠ i),
    (B.arc j).curve '' Icc (B.arc j).left (B.arc j).right
  have hF : IsClosed F := isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ =>
      (isCompact_Icc.image_of_continuousOn (B.arc j).continuous).isClosed
  have hK : IsClosed ((B.arc i).curve '' K) :=
    ((isCompact_Icc.diff hJ).image_of_continuousOn
      ((B.arc i).continuous.mono diff_subset)).isClosed
  let U := (boundaryEndpointSet B ∪ F ∪ (B.arc i).curve '' K)ᶜ
  refine ⟨U, ((boundaryEndpointSet_finite B).isClosed.union hF |>.union hK).isOpen_compl, ?_, ?_⟩
  · rintro (h | h)
    · rcases h with h | h
      · exact hne h
      · obtain ⟨j, hj⟩ := mem_iUnion.mp h
        obtain ⟨hji, hpj⟩ := mem_iUnion.mp hj
        exact hji (fullArc_index_unique_off_endpoints B hne j i hpj
          ⟨s, ⟨(hsub hs).1.le, (hsub hs).2.le⟩, rfl⟩)
    · obtain ⟨t, ht, he⟩ := h
      have hleft : t ≠ (B.arc i).left := by
        intro hl
        exact hne (mem_iUnion.mpr ⟨i, by simp [← he, hl]⟩)
      have hright : t ≠ (B.arc i).right := by
        intro hr
        exact hne (mem_iUnion.mpr ⟨i, by simp [← he, hr]⟩)
      have htopen : t ∈ Ioo (B.arc i).left (B.arc i).right :=
        ⟨lt_of_le_of_ne ht.1.1 hleft.symm, lt_of_le_of_ne ht.1.2 hright⟩
      have heq : t = s := B.injective i htopen (hsub hs) he
      exact ht.2 (heq.symm ▸ hs)
  · rintro p ⟨hp, hpU⟩
    rw [B.covers] at hp
    obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.mp hp
    have hji : j = i := by
      by_contra hji
      exact hpU (Or.inl (Or.inr (mem_iUnion.mpr ⟨j,
        mem_iUnion.mpr ⟨hji, t, ht, rfl⟩⟩)))
    subst j
    by_cases htJ : t ∈ J
    · exact ⟨t, htJ, rfl⟩
    · exact (hpU (Or.inr ⟨t, ⟨ht, htJ⟩, rfl⟩)).elim

/-- At a point away from the other presentation's endpoint images, the
inverse arc parameter defines a continuous local transition. This theorem
uses exactly the original RegularArc continuity and open-arc injectivity. -/
theorem boundary_arc_continuous_transition
    {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (j : Fin D.count) (s t : ℝ)
    (hs : s ∈ Ioo (B.arc i).left (B.arc i).right)
    (ht : t ∈ Ioo (D.arc j).left (D.arc j).right)
    (hp : (B.arc i).curve s = (D.arc j).curve t)
    (hne : (D.arc j).curve t ∉ boundaryEndpointSet D) :
    ∃ φ : ℝ → ℝ, φ s = t ∧ ContinuousAt φ s ∧
      (∀ᶠ x in 𝓝 s, φ x ∈ Ioo (D.arc j).left (D.arc j).right) ∧
      (∀ᶠ x in 𝓝 s, (D.arc j).curve (φ x) = (B.arc i).curve x) := by
  let φ : ℝ → ℝ := fun x =>
    Function.invFunOn (D.arc j).curve (Ioo (D.arc j).left (D.arc j).right) ((B.arc i).curve x)
  have hφs : φ s = t := by
    dsimp [φ]
    rw [hp]
    exact (D.injective j).leftInvOn_invFunOn ht
  have hc : ContinuousAt (B.arc i).curve s :=
    ((B.arc i).continuous s ⟨hs.1.le, hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hb : ∀ᶠ x in 𝓝 s, (B.arc i).curve x ∈
      SmoothManifolds.BoundaryData.intrinsicBoundary S := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    rw [B.covers]
    exact mem_iUnion.mpr ⟨i, x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
  have hlocal : ∀ J : Set ℝ, IsOpen J → t ∈ J →
      ∀ᶠ x in 𝓝 s, φ x ∈ J ∧ (D.arc j).curve (φ x) = (B.arc i).curve x := by
    intro J hJ htJ
    obtain ⟨U, hU, hpU, hsub⟩ := boundary_openArc_neighborhood D j
      (hJ.inter isOpen_Ioo) inter_subset_right ⟨htJ, ht⟩ hne
    have hpUs : (B.arc i).curve s ∈ U := by rw [hp]; exact hpU
    filter_upwards [hc.eventually (hU.mem_nhds hpUs), hb] with x hxU hxb
    obtain ⟨y, hy, hyEq⟩ := hsub ⟨hxb, hxU⟩
    have hφx : φ x = y := by
      dsimp [φ]
      rw [← hyEq]
      exact (D.injective j).leftInvOn_invFunOn hy.2
    exact ⟨hφx.symm ▸ hy.1, by rw [hφx]; exact hyEq⟩
  refine ⟨φ, hφs, ?_, ?_, ?_⟩
  · rw [ContinuousAt, hφs]
    apply tendsto_def.mpr
    intro V hV
    obtain ⟨J, hJV, hJ, htJ⟩ := mem_nhds_iff.mp hV
    filter_upwards [hlocal J hJ htJ] with x hx
    exact hJV hx.1
  · filter_upwards [hlocal (Ioo (D.arc j).left (D.arc j).right) isOpen_Ioo ht] with x hx
    exact hx.1
  · filter_upwards [hlocal univ isOpen_univ (mem_univ t)] with x hx
    exact hx.2

end P202.GlobalGaussBonnet
end Round3BoundaryRefinement


/-! Continuation: actual boundary transition derivatives. -/
section Round3BoundaryTransition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Any continuous local transition between two actual regular arcs has a
nonzero derivative. One nonzero scalar component of the second velocity
allows differentiation of the transition by `HasDerivAt.of_comp_left`;
the vector chain rule and source regularity then exclude derivative zero. -/
theorem regularArc_transition_hasDerivAt
    {g : RiemannianMetric S} (c d : RegularArc g) (φ : ℝ → ℝ) (s : ℝ)
    (hs : s ∈ Ioo c.left c.right) (ht : φ s ∈ Ioo d.left d.right)
    (hφ : ContinuousAt φ s)
    (heq : ∀ᶠ x in 𝓝 s, d.curve (φ x) = c.curve x) :
    ∃ k : ℝ, k ≠ 0 ∧ HasDerivAt φ k s := by
  have hp := heq.self_of_nhds
  obtain ⟨e, he, hc⟩ := S.smoothStructure.property.1.1 (c.curve s)
  have hd : d.curve (φ s) ∈ e.source := by rw [hp]; exact hc
  let v := (tangentStructure S).fiberCoordinates.equiv e he (c.curve s) hc (c.velocity s)
  let w := (tangentStructure S).fiberCoordinates.equiv e he (d.curve (φ s)) hd (d.velocity (φ s))
  have hv : v ≠ 0 := by
    exact (map_ne_zero_iff _
      ((tangentStructure S).fiberCoordinates.equiv e he (c.curve s) hc).injective).mpr
      (c.regular s ⟨hs.1.le, hs.2.le⟩)
  have hw : w ≠ 0 := by
    exact (map_ne_zero_iff _
      ((tangentStructure S).fiberCoordinates.equiv e he (d.curve (φ s)) hd).injective).mpr
      (d.regular (φ s) ⟨ht.1.le, ht.2.le⟩)
  have hcder : HasDerivAt (fun x => (e (c.curve x)).val) v s :=
    P202.Geometry.PiecewiseCurves.hasVelocityAt_coordinates (c.hasVelocity s hs) e he hc
  have hdder : HasDerivAt (fun x => (e (d.curve x)).val) w (φ s) :=
    P202.Geometry.PiecewiseCurves.hasVelocityAt_coordinates (d.hasVelocity (φ s) ht) e he hd
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, w j ≠ 0 := by
    by_contra hn
    apply hw
    ext j
    exact not_not.mp (not_exists.mp hn j)
  have hscalar : (fun x => (e (d.curve x)).val j) ∘ φ =ᶠ[𝓝 s]
      (fun x => (e (c.curve x)).val j) := by
    filter_upwards [heq] with x hx
    exact congrArg (fun p => (e p).val j) hx
  have hk : HasDerivAt φ (v j / w j) s :=
    HasDerivAt.of_comp_left hφ (hasDerivAt_pi.mp hdder j)
      (hasDerivAt_pi.mp hcder j) hj hscalar
  refine ⟨v j / w j, ?_, hk⟩
  intro hz
  have hcomp := hdder.scomp s hk
  have hvector : (fun x => (e (d.curve x)).val) ∘ φ =ᶠ[𝓝 s]
      (fun x => (e (c.curve x)).val) := by
    filter_upwards [heq] with x hx
    exact congrArg (fun p => (e p).val) hx
  have hsame := (hcomp.congr_of_eventuallyEq hvector.symm).unique hcder
  rw [hz, zero_smul] at hsame
  exact hv hsame.symm

/-- Actual differentiable local transitions between two finite genuine
boundary presentations, off the finite target endpoint set. -/
theorem boundary_arc_differentiable_transition
    {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (j : Fin D.count) (s t : ℝ)
    (hs : s ∈ Ioo (B.arc i).left (B.arc i).right)
    (ht : t ∈ Ioo (D.arc j).left (D.arc j).right)
    (hp : (B.arc i).curve s = (D.arc j).curve t)
    (hne : (D.arc j).curve t ∉ boundaryEndpointSet D) :
    ∃ (φ : ℝ → ℝ) (k : ℝ), k ≠ 0 ∧ φ s = t ∧ HasDerivAt φ k s ∧
      (∀ᶠ x in 𝓝 s, φ x ∈ Ioo (D.arc j).left (D.arc j).right) ∧
      (∀ᶠ x in 𝓝 s, (D.arc j).curve (φ x) = (B.arc i).curve x) := by
  obtain ⟨φ, hφs, hφ, hmaps, hcurve⟩ :=
    boundary_arc_continuous_transition B D i j s t hs ht hp hne
  obtain ⟨k, hk, hder⟩ := regularArc_transition_hasDerivAt (B.arc i) (D.arc j) φ s hs
    (hφs.symm ▸ ht) hφ hcurve
  exact ⟨φ, k, hk, hφs, hder, hmaps, hcurve⟩

end P202.GlobalGaussBonnet
end Round3BoundaryTransition


/-! Continuation: signed metric sectors in canonical chart rays. -/
section Round3SignedMetricSectors

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped Real
open Set
namespace P202.GlobalGaussBonnet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]

/-- Positivity comes from the actual metric oriented area, rather than an
assumed assertion about the angle. -/
theorem oangle_toReal_mem_Ioo_of_areaForm_pos (o : Orientation ℝ V (Fin 2))
    {u v : V} (ha : 0 < o.areaForm u v) :
    (o.oangle u v).toReal ∈ Ioo 0 Real.pi := by
  let z := o.kahler u v
  have him : 0 < z.im := by simpa [z, Orientation.kahler_apply_apply] using ha
  have hz : z ≠ 0 := by intro h; simp [h] at him
  have hsin : 0 < Real.sin z.arg := by
    rw [Complex.sin_arg]
    exact div_pos him (norm_pos_iff.mpr hz)
  have hnonneg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him.le
  have hnzero : z.arg ≠ 0 := by intro h; simp [h] at hsin
  have hnpi : z.arg ≠ Real.pi := by intro h; simp [h] at hsin
  unfold Orientation.oangle
  rw [Complex.arg_coe_angle_toReal_eq_arg]
  exact ⟨lt_of_le_of_ne hnonneg hnzero.symm, (Complex.arg_le_pi z).lt_of_ne hnpi⟩

/-- The two positively directed convex turns in the upper tangent half-plane
are complementary. Their signs are proved from oriented area. -/
theorem complementary_signed_metric_turns_of_areaForm_pos
    (o : Orientation ℝ V (Fin 2)) {u v : V} (ha : 0 < o.areaForm u v) :
    (o.oangle (-v) u).toReal + (o.oangle u v).toReal = Real.pi := by
  have harea : 0 < o.areaForm (-v) u := by
    simpa only [map_neg, LinearMap.neg_apply, o.areaForm_swap v u, neg_neg] using ha
  have hturn₁ := oangle_toReal_mem_Ioo_of_areaForm_pos o harea
  have hturn₂ := oangle_toReal_mem_Ioo_of_areaForm_pos o ha
  have hu : u ≠ 0 := by intro h; simp [h] at ha
  have hv : v ≠ 0 := by intro h; simp [h] at ha
  have hs := complementary_abs_metric_turns o hv hu
  simpa only [o.oangle_neg_neg, abs_of_pos hturn₁.1, abs_of_pos hturn₂.1] using hs

/-- The four signed exterior turns around two transverse lines total 2π.
Positivity of the base orientation is a determinant/area condition. -/
theorem crossing_signed_metric_turns_of_areaForm_pos
    (o : Orientation ℝ V (Fin 2)) {u v : V} (ha : 0 < o.areaForm u v) :
    (o.oangle (-v) u).toReal + (o.oangle u v).toReal +
      (o.oangle v (-u)).toReal + (o.oangle (-u) (-v)).toReal = 2 * Real.pi := by
  have hs := complementary_signed_metric_turns_of_areaForm_pos o ha
  rw [← o.oangle_neg_neg v (-u), neg_neg, o.oangle_neg_neg]
  linarith

end P202.GlobalGaussBonnet

namespace P202.GlobalGaussBonnet
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  SmoothManifolds.OrientationData
open P202.MetricData P202.SurfaceBoundaryData P202Specs.PlanarRegionTopology
  P202Specs.LocalGaussBonnet P202Specs.SurfaceRegionConstruction
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

/-- The actual chart's two ordered axis vectors have positive metric oriented
area, from the literal PositiveChart determinant-ray condition. -/
theorem chart_axes_orientedArea_pos
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpos : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    (x : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    0 < orientedArea g o (chartPoint c x)
      (chartVector c hc x (axisTangent 1))
      (chartVector c hc x (axisTangent 0)) := by
  apply (P202.Geometry.SurfaceBoundaryGeometry.orientation_bridge g _ o _ _).mp
  have h := hpos ⟨chartPoint c x, c.map_target hx⟩
  change IsPositive (o.val (chartPoint c x)) _
  convert h using 1
  congr 1
  funext j
  fin_cases j <;>
    simp [P202.VolumeData.cotangentBundle, chartVector, hx,
      axisTangent, toPlane, EuclideanSpace.equiv]
  all_goals
    ext i
    fin_cases i <;> rfl

theorem chartVector_neg_smul (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x v : Plane) :
    chartVector c hc x (-v) = (-1 : ℝ) • chartVector c hc x v := by
  rw [← neg_one_smul ℝ v, chartVector_smul]

theorem chart_axes_signed_half_plane_turn_sum
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpos : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    (x : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    metricChartTurn g o c hc x (-axisTangent 0) (axisTangent 1) +
      metricChartTurn g o c hc x (axisTangent 1) (axisTangent 0) = Real.pi := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  unfold metricChartTurn
  simp only [chartVector_neg_smul, neg_one_smul]
  exact complementary_signed_metric_turns_of_areaForm_pos (planeOrientation g o p)
    (chart_axes_orientedArea_pos g o c hc hpos x hx)

theorem chart_axes_signed_full_plane_turn_sum
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpos : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    (x : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    metricChartTurn g o c hc x (-axisTangent 0) (axisTangent 1) +
      metricChartTurn g o c hc x (axisTangent 1) (axisTangent 0) +
      metricChartTurn g o c hc x (axisTangent 0) (-axisTangent 1) +
      metricChartTurn g o c hc x (-axisTangent 1) (-axisTangent 0) = 2 * Real.pi := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  unfold metricChartTurn
  simp only [chartVector_neg_smul, neg_one_smul]
  exact crossing_signed_metric_turns_of_areaForm_pos (planeOrientation g o p)
    (chart_axes_orientedArea_pos g o c hc hpos x hx)

/-- Canonical incoming tangent for the positively traversed boundary of the
actual source sign chamber. Its negative is the outgoing ray on that side. -/
def quadrantIncoming (σ : Fin 2 → Bool) : Plane :=
  if σ 0 = σ 1 then -P202.SurfaceRegionConstruction.AxisRays.direction (0, σ 1)
  else -P202.SurfaceRegionConstruction.AxisRays.direction (1, σ 0)

/-- Canonical outgoing tangent for the same chamber, using exactly the source
AxisRays.direction definition. -/
def quadrantOutgoing (σ : Fin 2 → Bool) : Plane :=
  if σ 0 = σ 1 then P202.SurfaceRegionConstruction.AxisRays.direction (1, σ 0)
  else P202.SurfaceRegionConstruction.AxisRays.direction (0, σ 1)

theorem chart_quadrant_metricTurn_mem_Ioo
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpos : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    (x : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target)
    (σ : Fin 2 → Bool) :
    metricChartTurn g o c hc x (quadrantIncoming σ) (quadrantOutgoing σ) ∈
      Ioo 0 Real.pi := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  unfold metricChartTurn
  apply oangle_toReal_mem_Ioo_of_areaForm_pos
  have hbase := chart_axes_orientedArea_pos g o c hc hpos x hx
  change 0 < (planeOrientation g o p).areaForm
    (chartVector c hc x (axisTangent 1)) (chartVector c hc x (axisTangent 0)) at hbase
  have hreverse : (planeOrientation g o p).areaForm
      (chartVector c hc x (axisTangent 0)) (chartVector c hc x (axisTangent 1)) < 0 := by
    rw [(planeOrientation g o p).areaForm_swap
      (chartVector c hc x (axisTangent 0)) (chartVector c hc x (axisTangent 1))]
    exact neg_neg_of_pos hbase
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp only [quadrantIncoming, quadrantOutgoing, h0, h1,
      P202.SurfaceRegionConstruction.AxisRays.direction,
      Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false, chartVector_neg_smul,
      neg_one_smul, map_neg, LinearMap.neg_apply, neg_neg, neg_pos] <;>
    first | exact hbase | exact hreverse

/-- The canonical incoming and outgoing coordinate tangents are unit vectors. -/
theorem quadrantIncoming_norm (σ : Fin 2 → Bool) : ‖quadrantIncoming σ‖ = 1 := by
  unfold quadrantIncoming
  split <;> simp [P202.SurfaceRegionConstruction.AxisRays.direction_norm]

theorem quadrantOutgoing_norm (σ : Fin 2 → Bool) : ‖quadrantOutgoing σ‖ = 1 := by
  unfold quadrantOutgoing
  split <;> simp [P202.SurfaceRegionConstruction.AxisRays.direction_norm]

theorem quadrantOutgoing_eq_quarterTurn (σ : Fin 2 → Bool) :
    quadrantOutgoing σ = quarterTurn (quadrantIncoming σ) := by
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> ext i <;> fin_cases i <;>
    norm_num [quadrantIncoming, quadrantOutgoing,
      P202.SurfaceRegionConstruction.AxisRays.direction, axisTangent, toPlane,
      quarterTurn, h0, h1]

theorem quadrantIncoming_eq_neg_quarterTurn (σ : Fin 2 → Bool) :
    -quadrantIncoming σ = quarterTurn (quadrantOutgoing σ) := by
  rw [quadrantOutgoing_eq_quarterTurn]
  ext i
  fin_cases i <;> simp [quarterTurn]

/-- The source sign chamber lies on the left of both canonical directed
boundary rays. This proves their geometrical orientation, rather than assuming
an angle-sign certificate. -/
theorem quadrant_boundary_rays_have_chamber_on_left
    (σ : Fin 2 → Bool) {R t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hsize : t + r < R) :
    (-t) • quadrantIncoming σ + r • quarterTurn (quadrantIncoming σ) ∈
      P202.SurfaceRegionConstruction.NormalSectors.chamber univ R σ ∧
    t • quadrantOutgoing σ + r • quarterTurn (quadrantOutgoing σ) ∈
      P202.SurfaceRegionConstruction.NormalSectors.chamber univ R σ := by
  have hin_norm : ‖(-t) • quadrantIncoming σ + r • quarterTurn (quadrantIncoming σ)‖ < R := by
    calc
      _ ≤ ‖(-t) • quadrantIncoming σ‖ + ‖r • quarterTurn (quadrantIncoming σ)‖ := norm_add_le _ _
      _ = t + r := by
        rw [← quadrantOutgoing_eq_quarterTurn]
        simp [norm_smul, quadrantIncoming_norm, quadrantOutgoing_norm,
          Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hr]
      _ < R := hsize
  have hout_norm : ‖t • quadrantOutgoing σ + r • quarterTurn (quadrantOutgoing σ)‖ < R := by
    calc
      _ ≤ ‖t • quadrantOutgoing σ‖ + ‖r • quarterTurn (quadrantOutgoing σ)‖ := norm_add_le _ _
      _ = t + r := by
        rw [← quadrantIncoming_eq_neg_quarterTurn]
        simp [norm_smul, quadrantIncoming_norm, quadrantOutgoing_norm,
          Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hr]
      _ < R := hsize
  constructor
  · refine ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hin_norm, ?_⟩
    apply mem_iInter₂.mpr
    intro a _
    fin_cases a <;> cases h0 : σ 0 <;> cases h1 : σ 1 <;>
      simp [quadrantIncoming, P202.SurfaceRegionConstruction.AxisRays.direction,
        axisTangent, toPlane, quarterTurn, h0, h1, ht, hr]
  · refine ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hout_norm, ?_⟩
    apply mem_iInter₂.mpr
    intro a _
    fin_cases a <;> cases h0 : σ 0 <;> cases h1 : σ 1 <;>
      simp [quadrantOutgoing, P202.SurfaceRegionConstruction.AxisRays.direction,
        axisTangent, toPlane, quarterTurn, h0, h1, ht, hr]

/-- Each actual metric quadrant angle is strictly between 0 and π. -/
theorem chart_quadrant_metricInterior_mem_Ioo
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpos : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    (x : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target)
    (σ : Fin 2 → Bool) :
    Real.pi - metricChartTurn g o c hc x (quadrantIncoming σ) (quadrantOutgoing σ) ∈
      Ioo 0 Real.pi := by
  have h := chart_quadrant_metricTurn_mem_Ioo g o c hc hpos x hx σ
  constructor <;> linarith [h.1, h.2]

/-- The two occupied metric quadrant angles in the upper half-plane sum to π. -/
theorem chart_axes_metric_half_plane_angle_sum
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpos : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    (x : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    (Real.pi - metricChartTurn g o c hc x (-axisTangent 0) (axisTangent 1)) +
      (Real.pi - metricChartTurn g o c hc x (axisTangent 1) (axisTangent 0)) = Real.pi := by
  have h := chart_axes_signed_half_plane_turn_sum g o c hc hpos x hx
  linarith

/-- The four occupied metric quadrant angles at a crossing sum to 2π. -/
theorem chart_axes_metric_full_plane_angle_sum
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpos : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    (x : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) :
    (Real.pi - metricChartTurn g o c hc x (-axisTangent 0) (axisTangent 1)) +
      (Real.pi - metricChartTurn g o c hc x (axisTangent 1) (axisTangent 0)) +
      (Real.pi - metricChartTurn g o c hc x (axisTangent 0) (-axisTangent 1)) +
      (Real.pi - metricChartTurn g o c hc x (-axisTangent 1) (-axisTangent 0)) =
        2 * Real.pi := by
  have h := chart_axes_signed_full_plane_turn_sum g o c hc hpos x hx
  linarith

end P202.GlobalGaussBonnet
end Round3SignedMetricSectors


/-! Continuation: full area transport for both original model kinds. -/
section Round3ExtensionArea
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.TangentBundleData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.ConnectionData P202.CurvatureData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.PlanarRegionTopology
namespace P202.GlobalGaussBonnet

/-- Evaluation of the actual model-zero-extended chart integrand at an actual
chart point works on both the full-plane and half-space source models. -/
theorem chartIntegrand_indicator_at_point
    {a : ModelKind} {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 a M}
    (g : RiemannianMetric S) (c : ModelChart 2 a M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) (A : Set M) (hAc : A ⊆ c.source) (p : M) (hp : p ∈ A) :
    P202.VolumeData.chartIntegrand g (A.indicator f)
      (tangentStructure S).fiberCoordinates c hc (c p).val =
        f p * Real.sqrt (P202.VolumeData.gramMatrix g
          (tangentStructure S).fiberCoordinates c hc ⟨p, hAc hp⟩).det := by
  simp only [P202.VolumeData.chartIntegrand, SmoothManifolds.LocalIntegrationData.extendModel,
    Subtype.coe_prop, dite_true, c.map_source (hAc hp), c.left_inv (hAc hp),
    Set.indicator_of_mem hp]

/-- The original chart integrand with a supported indicator is zero away
from the actual ambient coordinate image, including outside a half-space. -/
theorem chartIntegrand_indicator_eq_zero_off_image
    {a : ModelKind} {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 a M}
    (g : RiemannianMetric S) (c : ModelChart 2 a M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) (A : Set M) (x : Plane) (hx : x ∉ coordinates c '' A) :
    P202.VolumeData.chartIntegrand g (A.indicator f)
      (tangentStructure S).fiberCoordinates c hc (EuclideanSpace.equiv (Fin 2) ℝ x) = 0 := by
  unfold P202.VolumeData.chartIntegrand SmoothManifolds.LocalIntegrationData.extendModel
  split
  · rename_i hm
    dsimp only
    split
    · rename_i ht
      have hp : c.symm ⟨EuclideanSpace.equiv (Fin 2) ℝ x, hm⟩ ∉ A := by
        intro hp
        apply hx
        refine ⟨_, hp, ?_⟩
        unfold coordinates
        rw [c.right_inv ht]
        simp [toPlane]
      rw [Set.indicator_of_notMem hp, zero_mul]
    · rfl
  · rfl

/-- Pointwise density transport from either original source model into a
Euclidean ambient chart. The assumptions are equal actual coordinates,
Gaussian values and full Gram matrices on the original set, not an assumed
integration identity. -/
theorem matched_chart_curvatureIntegrand_indicator
    {a : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 2 a M} {Q : SmoothManifold 2 .euclidean N}
    (g : RiemannianMetric S) (T : CurvatureTensor S)
    (h : RiemannianMetric Q) (H : CurvatureTensor Q)
    (c : ModelChart 2 a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart 2 .euclidean N) (hd : d ∈ Q.smoothStructure.val)
    (A : Set M) (hAc : A ⊆ c.source) (q : A → N)
    (hqd : ∀ p, q p ∈ d.source)
    (hcoord : ∀ p, (c p.val).val = (d (q p)).val)
    (hgauss : ∀ p, gaussianCurvature g T p.val = gaussianCurvature h H (q p))
    (hgram : ∀ p : A, P202.VolumeData.gramMatrix g
      (tangentStructure S).fiberCoordinates c hc ⟨p.val, hAc p.property⟩ =
        P202.VolumeData.gramMatrix h (tangentStructure Q).fiberCoordinates d hd ⟨q p, hqd p⟩)
    (x : Plane) :
    P202.VolumeData.chartIntegrand g (A.indicator (gaussianCurvature g T))
      (tangentStructure S).fiberCoordinates c hc (EuclideanSpace.equiv (Fin 2) ℝ x) =
        (coordinates c '' A).indicator
          (P202Specs.LocalGaussBonnet.curvatureIntegrand h H d hd) x := by
  classical
  by_cases hx : x ∈ coordinates c '' A
  · obtain ⟨p, hp, hpx⟩ := hx
    let pa : A := ⟨p, hp⟩
    have hcp : (c p).val = EuclideanSpace.equiv (Fin 2) ℝ x := by
      apply toPlane.injective
      simpa [coordinates, toPlane] using hpx
    have hdq : d (q pa) = P202Specs.ChartRegionStokes.modelPoint x := by
      apply Subtype.ext
      exact (hcoord pa).symm.trans hcp
    have hdt : P202Specs.ChartRegionStokes.modelPoint x ∈ d.target :=
      hdq ▸ d.map_source (hqd pa)
    have hpnt : P202Specs.LocalGaussBonnet.chartPoint d x = q pa := by
      rw [P202Specs.LocalGaussBonnet.chartPoint, ← hdq, d.left_inv (hqd pa)]
    have hx' : x ∈ coordinates c '' A := ⟨p, hp, hpx⟩
    rw [Set.indicator_of_mem hx', ← hcp,
      chartIntegrand_indicator_at_point g c hc _ A hAc p hp]
    unfold P202Specs.LocalGaussBonnet.curvatureIntegrand P202Specs.LocalGaussBonnet.areaWeight
    rw [dite_eq_left hdt]
    change gaussianCurvature g T p * Real.sqrt _ = _
    rw [← gaussianCurvature_eq_local]
    simp only [hpnt]
    rw [hgauss pa, hgram pa]
  · rw [Set.indicator_of_notMem hx, chartIntegrand_indicator_eq_zero_off_image g c hc _ A x hx]

/-- The original intrinsic curvature integral equals the Euclidean ambient
local curvature integral, for either original model, from actual scalar and
Gram agreement in matching chart coordinates. -/
theorem matched_local_curvatureIntegral_eq_intrinsic
    {a : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 2 a M} {Q : SmoothManifold 2 .euclidean N}
    (g : RiemannianMetric S) (T : CurvatureTensor S)
    (h : RiemannianMetric Q) (H : CurvatureTensor Q)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (c : ModelChart 2 a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart 2 .euclidean N) (hd : d ∈ Q.smoothStructure.val)
    (R : PlanarRegion) (A : Set M) (hA : @MeasurableSet M (borel M) A)
    (hAc : A ⊆ c.source) (hAR : coordinates c '' A = R.carrier) (q : A → N)
    (hqd : ∀ p, q p ∈ d.source)
    (hcoord : ∀ p, (c p.val).val = (d (q p)).val)
    (hgauss : ∀ p, gaussianCurvature g T p.val = gaussianCurvature h H (q p))
    (hgram : ∀ p : A, P202.VolumeData.gramMatrix g
      (tangentStructure S).fiberCoordinates c hc ⟨p.val, hAc p.property⟩ =
        P202.VolumeData.gramMatrix h (tangentStructure Q).fiberCoordinates d hd ⟨q p, hqd p⟩)
    (hf : letI : MeasurableSpace M := borel M; IntegrableOn (gaussianCurvature g T) A μ) :
    (letI : MeasurableSpace M := borel M; ∫ p in A, gaussianCurvature g T p ∂μ) =
      P202Specs.LocalGaussBonnet.curvatureIntegral h H d hd R := by
  let _ : MeasurableSpace M := borel M
  have hfi : Integrable (A.indicator (gaussianCurvature g T)) μ :=
    (integrable_indicator_iff hA).mpr hf
  rw [← integral_indicator hA, areaMeasure_integral_chart g μ hμ c hc _ hfi
    (support_indicator_subset.trans hAc)]
  rw [← (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.measurableEmbedding]
  have hfun : (fun x : Plane =>
      P202.VolumeData.chartIntegrand g (A.indicator (gaussianCurvature g T))
        (tangentStructure S).fiberCoordinates c hc (EuclideanSpace.equiv (Fin 2) ℝ x)) =
      R.carrier.indicator (P202Specs.LocalGaussBonnet.curvatureIntegrand h H d hd) := by
    funext x
    rw [matched_chart_curvatureIntegrand_indicator g T h H c hc d hd A hAc q
      hqd hcoord hgauss hgram x, hAR]
  change (∫ x : Plane, P202.VolumeData.chartIntegrand g (A.indicator (gaussianCurvature g T))
    (tangentStructure S).fiberCoordinates c hc (EuclideanSpace.equiv (Fin 2) ℝ x)) = _
  rw [hfun]
  exact integral_indicator isClosed_closure.measurableSet

/-- Compact-source version: the original Levi–Civita geometry supplies all
integrability, including when the original region meets the true boundary. -/
theorem matched_local_curvatureIntegral_eq_intrinsic_of_isCompact
    {a : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 2 a M} {Q : SmoothManifold 2 .euclidean N}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (h : RiemannianMetric Q) (H : CurvatureTensor Q)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (c : ModelChart 2 a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart 2 .euclidean N) (hd : d ∈ Q.smoothStructure.val)
    (R : PlanarRegion) (A : Set M) (hA : @MeasurableSet M (borel M) A)
    (hAK : IsCompact A) (hAc : A ⊆ c.source)
    (hAR : coordinates c '' A = R.carrier) (q : A → N)
    (hqd : ∀ p, q p ∈ d.source)
    (hcoord : ∀ p, (c p.val).val = (d (q p)).val)
    (hgauss : ∀ p, gaussianCurvature g T p.val = gaussianCurvature h H (q p))
    (hgram : ∀ p : A, P202.VolumeData.gramMatrix g
      (tangentStructure S).fiberCoordinates c hc ⟨p.val, hAc p.property⟩ =
        P202.VolumeData.gramMatrix h (tangentStructure Q).fiberCoordinates d hd ⟨q p, hqd p⟩) :
    (letI : MeasurableSpace M := borel M; ∫ p in A, gaussianCurvature g T p ∂μ) =
      P202Specs.LocalGaussBonnet.curvatureIntegral h H d hd R := by
  exact matched_local_curvatureIntegral_eq_intrinsic g T h H μ hμ c hc d hd R A hA hAc hAR q
    hqd hcoord hgauss hgram
      (integrableOn_gaussianCurvature_of_isCompact g C hC T hT μ hμ A hAK hA)

/-- Coordinate Grams agree between the original surface and its actual
ambient metric extension, as a consequence of the TWO genuine metric-preserving
differentials through the open restriction. -/
theorem restriction_extension_gramMatrix
    {n : ℕ} {a : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (g : RiemannianMetric S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (W : Set M) (hWe : W ⊆ e.source) (R : SmoothManifold n a W)
    (i : SmoothImmersion R S Subtype.val)
    (c : ModelChart n a W) (hc : c ∈ R.smoothStructure.val)
    (hcs : c.source = univ) (hcval : ∀ p : W, c p = e p.val)
    (Q : SmoothManifold n .euclidean N) (h : RiemannianMetric Q)
    (d : ModelChart n .euclidean N) (hd : d ∈ Q.smoothStructure.val)
    (f : W → N) (j : SmoothImmersion R Q f) (hfd : ∀ p, f p ∈ d.source)
    (hcoord : ∀ p, (c p).val = (d (f p)).val)
    (hm : IsMetricPreserving (P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i)
      h f j.differential) (p : W) :
    P202.VolumeData.gramMatrix g (tangentStructure S).fiberCoordinates e he ⟨p.val, hWe p.property⟩ =
      P202.VolumeData.gramMatrix h (tangentStructure Q).fiberCoordinates d hd ⟨f p, hfd p⟩ := by
  let gR := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i
  have hp : p ∈ c.source := by rw [hcs]; trivial
  have hgrS := metricPreserving_gramMatrix Subtype.val i.smooth i.differential
    i.isDifferential gR g (fun _ _ _ => rfl) c e hc he ⟨p, hp⟩ (hWe p.property)
    (Filter.Eventually.of_forall (fun q => congrArg Subtype.val (hcval q)))
    (tangentStructure R).fiberCoordinates (tangentStructure S).fiberCoordinates
  have hgrQ := metricPreserving_gramMatrix f j.smooth j.differential
    j.isDifferential gR h hm c d hc hd ⟨p, hp⟩ (hfd p)
    (Filter.Eventually.of_forall hcoord)
    (tangentStructure R).fiberCoordinates (tangentStructure Q).fiberCoordinates
  exact hgrS.symm.trans hgrQ

/-- Direct area-integral bridge for the actual extension package: all Gram
compatibility is discharged from the genuine inclusion and extension immersions.
Only pointwise Gaussian naturality, already proved by the extension construction,
is supplied. The original source model is arbitrary. -/
theorem extension_local_curvatureIntegral_eq_intrinsic_of_isCompact
    {a : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold 2 a M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (e : ModelChart 2 a M) (he : e ∈ S.smoothStructure.val)
    (W : Set M) (hWe : W ⊆ e.source) (R : SmoothManifold 2 a W)
    (i : SmoothImmersion R S Subtype.val)
    (c : ModelChart 2 a W) (hc : c ∈ R.smoothStructure.val)
    (hcs : c.source = univ) (hcval : ∀ p : W, c p = e p.val)
    (Q : SmoothManifold 2 .euclidean N) (h : RiemannianMetric Q) (H : CurvatureTensor Q)
    (d : ModelChart 2 .euclidean N) (hd : d ∈ Q.smoothStructure.val)
    (f : W → N) (j : SmoothImmersion R Q f) (hfd : ∀ p, f p ∈ d.source)
    (hcoord : ∀ p, (c p).val = (d (f p)).val)
    (hm : IsMetricPreserving (P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val i)
      h f j.differential)
    (hgauss : ∀ p : W, gaussianCurvature g T p.val = gaussianCurvature h H (f p))
    (D : PlanarRegion) (A : Set M) (hA : @MeasurableSet M (borel M) A)
    (hAK : IsCompact A) (hAW : A ⊆ W)
    (hAD : coordinates e '' A = D.carrier) :
    (letI : MeasurableSpace M := borel M; ∫ p in A, gaussianCurvature g T p ∂μ) =
      P202Specs.LocalGaussBonnet.curvatureIntegral h H d hd D := by
  let q : A → N := fun p => f ⟨p.val, hAW p.property⟩
  apply matched_local_curvatureIntegral_eq_intrinsic_of_isCompact g C hC T hT h H μ hμ e he d hd
    D A hA hAK (hAW.trans hWe) hAD q (fun p => hfd ⟨p.val, hAW p.property⟩)
  · intro p
    exact (congrArg Subtype.val (hcval ⟨p.val, hAW p.property⟩)).symm.trans
      (hcoord ⟨p.val, hAW p.property⟩)
  · intro p
    exact hgauss ⟨p.val, hAW p.property⟩
  · intro p
    exact restriction_extension_gramMatrix S g e he W hWe R i c hc hcs hcval Q h d hd f j
      hfd hcoord hm ⟨p.val, hAW p.property⟩

end P202.GlobalGaussBonnet
end Round3ExtensionArea


/-! Continuation: Round4BoundaryOrder. -/
section Round4BoundaryOrder

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace P202.GlobalGaussBonnet

/-- An injective differentiable real parameter change on a nonempty open
interval has one derivative sign throughout that interval. -/
theorem injective_interval_derivative_sign {φ : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hc : ContinuousOn φ (Ioo l r))
    (hi : InjOn φ (Ioo l r))
    (hd : ∀ x ∈ Ioo l r, DifferentiableAt ℝ φ x)
    (hn : ∀ x ∈ Ioo l r, deriv φ x ≠ 0) :
    (∀ x ∈ Ioo l r, 0 < deriv φ x) ∨
      (∀ x ∈ Ioo l r, deriv φ x < 0) := by
  obtain hm | hm := hc.strictMonoOn_of_injOn_Ioo hlr hi
  · left
    intro x hx
    have hnneg : 0 ≤ deriv φ x := by
      rw [← (hd x hx).derivWithin (isOpen_Ioo.uniqueDiffWithinAt hx)]
      exact hm.monotoneOn.derivWithin_nonneg
    exact lt_of_le_of_ne hnneg (hn x hx).symm
  · right
    intro x hx
    have hnpos : deriv φ x ≤ 0 := by
      rw [← (hd x hx).derivWithin (isOpen_Ioo.uniqueDiffWithinAt hx)]
      exact hm.antitoneOn.derivWithin_nonpos
    exact lt_of_le_of_ne hnpos (hn x hx)

/-- A bounded injective differentiable transition on an open interval extends
continuously to both endpoints. The extension has the original strict
orientation and its derivative sign on the whole open interval. -/
theorem bounded_interval_transition_extension {φ : ℝ → ℝ} {l r a b : ℝ}
    (hlr : l < r) (hc : ContinuousOn φ (Ioo l r))
    (hi : InjOn φ (Ioo l r))
    (hd : ∀ x ∈ Ioo l r, DifferentiableAt ℝ φ x)
    (hn : ∀ x ∈ Ioo l r, deriv φ x ≠ 0)
    (hmaps : MapsTo φ (Ioo l r) (Icc a b)) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Icc l r) ∧ EqOn ψ φ (Ioo l r) ∧
      MapsTo ψ (Icc l r) (Icc a b) ∧
      (∀ x ∈ Ioo l r, HasDerivAt ψ (deriv φ x) x) ∧
      ((StrictMonoOn ψ (Icc l r) ∧ ∀ x ∈ Ioo l r, 0 < deriv φ x) ∨
        (StrictAntiOn ψ (Icc l r) ∧ ∀ x ∈ Ioo l r, deriv φ x < 0)) := by
  let ψ := extendFrom (Ioo l r) φ
  have hnonempty : (Ioo l r).Nonempty := nonempty_Ioo.mpr hlr
  have hbelow : BddBelow (φ '' Ioo l r) := ⟨a, by rintro y ⟨x, hx, rfl⟩; exact (hmaps hx).1⟩
  have habove : BddAbove (φ '' Ioo l r) := ⟨b, by rintro y ⟨x, hx, rfl⟩; exact (hmaps hx).2⟩
  have heq : EqOn ψ φ (Ioo l r) := by
    intro x hx
    exact extendFrom_eq (subset_closure hx) (hc x hx)
  have hcψ : ContinuousOn ψ (Icc l r) := by
    obtain hm | hm := hc.strictMonoOn_of_injOn_Ioo hlr hi
    · exact continuousOn_Icc_extendFrom_Ioo hc
        (hm.monotoneOn.tendsto_nhdsWithin_Ioo_right hnonempty hbelow)
        (hm.monotoneOn.tendsto_nhdsWithin_Ioo_left hnonempty habove)
    · exact continuousOn_Icc_extendFrom_Ioo hc
        (hm.antitoneOn.tendsto_nhdsWithin_Ioo_right hnonempty habove)
        (hm.antitoneOn.tendsto_nhdsWithin_Ioo_left hnonempty hbelow)
  have hmapsψ : MapsTo ψ (Icc l r) (Icc a b) := by
    have hmaps' : MapsTo ψ (Ioo l r) (Icc a b) := fun x hx => by
      rw [heq hx]
      exact hmaps hx
    have h := hmaps'.closure_of_continuousOn (by simpa [closure_Ioo hlr.ne] using hcψ)
    simpa [closure_Ioo hlr.ne, isClosed_Icc.closure_eq] using h
  have hdψ : ∀ x ∈ Ioo l r, HasDerivAt ψ (deriv φ x) x := by
    intro x hx
    apply (hd x hx).hasDerivAt.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact heq hy
  refine ⟨ψ, hcψ, heq, hmapsψ, hdψ, ?_⟩
  obtain hp | hp := injective_interval_derivative_sign hlr hc hi hd hn
  · left
    refine ⟨strictMonoOn_of_deriv_pos (convex_Icc l r) hcψ ?_, hp⟩
    intro x hx
    rw [interior_Icc] at hx
    rw [(hdψ x hx).deriv]
    exact hp x hx
  · right
    refine ⟨strictAntiOn_of_deriv_neg (convex_Icc l r) hcψ ?_, hp⟩
    intro x hx
    rw [interior_Icc] at hx
    rw [(hdψ x hx).deriv]
    exact hp x hx

end P202.GlobalGaussBonnet
end Round4BoundaryOrder


/-! Continuation: Round4BoundaryGerms. -/
section Round4BoundaryGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.FrameData SmoothManifolds.BundleData
open P202.MetricData P202.ConnectionData P202.CurveConnectionData
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

theorem coefficientsAlong_heq (c d : ℝ → M)
    (T : (t : ℝ) → TangentSpace S (c t)) (U : (t : ℝ) → TangentSpace S (d t))
    {V : Set M} {hV : IsOpen V} (b : LocalFrame (tangentBundle S) V hV)
    {t : ℝ} (hp : c t = d t) (hT : HEq (T t) (U t)) :
    coefficientsAlong b c T t = coefficientsAlong b d U t := by
  classical
  have key : ∀ (p q : M) (h : p = q)
      (v : TangentSpace S p) (w : TangentSpace S q), HEq v w →
      (if h : p ∈ V then (b.basis ⟨p, h⟩).equivFun v else 0) =
        (if h : q ∈ V then (b.basis ⟨q, h⟩).equivFun w else 0) := by
    rintro p q rfl v w h
    cases h
    rfl
  exact key (c t) (d t) hp (T t) (U t) hT

theorem frameDerivative_heq (C : Connection (tangentBundle S))
    (c d : ℝ → M)
    (T : (t : ℝ) → TangentSpace S (c t)) (U : (t : ℝ) → TangentSpace S (d t))
    {V : Set M} {hV : IsOpen V} (b : LocalFrame (tangentBundle S) V hV)
    {t : ℝ} (hp : c t = d t) (hT : HEq (T t) (U t))
    (pc : c t ∈ V) (pd : d t ∈ V)
    (v : TangentSpace S (c t)) (w : TangentSpace S (d t)) (hv : HEq v w)
    (a : Euclidean 2) :
    HEq (frameDerivative C b c T t pc v a) (frameDerivative C b d U t pd w a) := by
  unfold frameDerivative
  rw [P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem b c T t pc,
    P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem b d U t pd]
  have key : ∀ (p q : M) (h : p = q)
      (X : TangentSpace S p) (Y : TangentSpace S q), HEq X Y →
      ∀ (v : TangentSpace S p) (w : TangentSpace S q), HEq v w →
      ∀ (pc : p ∈ V) (pd : q ∈ V),
      HEq ((b.basis ⟨p, pc⟩).equivFun.symm
        (a + (connectionMatrix C b ⟨p, pc⟩ v).mulVec ((b.basis ⟨p, pc⟩).equivFun X)))
        ((b.basis ⟨q, pd⟩).equivFun.symm
        (a + (connectionMatrix C b ⟨q, pd⟩ w).mulVec ((b.basis ⟨q, pd⟩).equivFun Y))) := by
    rintro p q rfl X Y hXY v w hvw pc pd
    cases hXY
    cases hvw
    rfl
  exact key (c t) (d t) hp (T t) (U t) hT v w hv pc pd

/-- Covariant differentiation along actual curves is local even when the
curve functions are only equal near the parameter and their tangent fibers
therefore have different dependent types. -/
theorem hasCovariantDerivativeAt_congr_curve
    (C : Connection (tangentBundle S)) {c d : ℝ → M}
    {T : (t : ℝ) → TangentSpace S (c t)} {U : (t : ℝ) → TangentSpace S (d t)}
    {t : ℝ} {D : TangentSpace S (c t)}
    (hD : HasCovariantDerivativeAt C c T t D)
    (hc : c =ᶠ[𝓝 t] d) (hT : ∀ᶠ s in 𝓝 t, HEq (T s) (U s)) :
    ∃ D' : TangentSpace S (d t), HEq D D' ∧ HasCovariantDerivativeAt C d U t D' := by
  obtain ⟨v, hvel, V, hV, b, pc, a, hda, hframe⟩ := hD
  let w : TangentSpace S (d t) := cast (congrArg (TangentSpace S) hc.eq_of_nhds) v
  have hvw : HEq v w := (cast_heq _ _).symm
  have hw : HasVelocityWithinAt S d univ t w := by
    obtain ⟨hcont, e, he, pe, hder⟩ := hvel
    have pe' : d t ∈ e.source := hc.eq_of_nhds ▸ pe
    refine ⟨hcont.congr_of_eventuallyEq (hc.symm.filter_mono nhdsWithin_le_nhds) hc.eq_of_nhds.symm,
      e, he, pe', ?_⟩
    rw [P202.Geometry.PiecewiseCurves.fiberCoordinates_cast
      e he (c t) (d t) pe pe' hc.eq_of_nhds v]
    exact hder.congr_of_eventuallyEq_of_mem
      ((hc.fun_comp (fun p => (e p).val)).symm.filter_mono nhdsWithin_le_nhds)
      (mem_univ t)
  have hcoef : coefficientsAlong b c T =ᶠ[𝓝 t] coefficientsAlong b d U := by
    filter_upwards [hc, hT] with s hs hsT
    exact coefficientsAlong_heq c d T U b hs hsT
  have pd : d t ∈ V := hc.eq_of_nhds ▸ pc
  refine ⟨frameDerivative C b d U t pd w a, ?_, w, hw, V, hV, b, pd, a, ?_, rfl⟩
  · rw [hframe]
    exact frameDerivative_heq C c d T U b hc.eq_of_nhds hT.self_of_nhds pc pd v w hvw a
  · exact hda.congr_of_eventuallyEq_of_mem
      (hcoef.symm.filter_mono nhdsWithin_le_nhds) (mem_univ t)

/-- The canonical chosen covariant derivatives respect the same curve and
field germs whenever the actual derivative exists. -/
theorem covariantDerivative_heq_of_germs
    (C : Connection (tangentBundle S)) {c d : ℝ → M}
    {T : (t : ℝ) → TangentSpace S (c t)} {U : (t : ℝ) → TangentSpace S (d t)}
    {t : ℝ} {D : TangentSpace S (c t)}
    (hD : HasCovariantDerivativeAt C c T t D)
    (hc : c =ᶠ[𝓝 t] d) (hT : ∀ᶠ s in 𝓝 t, HEq (T s) (U s)) :
    HEq (covariantDerivative C c T t) (covariantDerivative C d U t) := by
  obtain ⟨D', hDD', hD'⟩ := hasCovariantDerivativeAt_congr_curve C hD hc hT
  dsimp only [covariantDerivative]
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ t) uniqueDiffWithinAt_univ hD,
    P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ t) uniqueDiffWithinAt_univ hD']
  exact hDD'
end P202.GlobalGaussBonnet
end Round4BoundaryGerms


/-! Continuation: Round4OccupiedAngles. -/
section Round4OccupiedAngles

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Set Filter
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning
open P202Specs.MetricBoundaryTurning

namespace P202.GlobalGaussBonnet
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

private def occupiedChartVectorEquiv (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    Plane ≃ₗ[ℝ] TangentSpace S (chartPoint c x) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.trans
    ((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x) (c.map_target hx)).symm

private lemma occupiedChartVectorEquiv_apply (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (v : Plane) :
    occupiedChartVectorEquiv c hc x hx v = chartVector c hc x v := by
  have hx' : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target := hx
  simp only [occupiedChartVectorEquiv, chartVector, dite_eq_left hx']
  rfl

private lemma occupiedChartVector_smul (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x v : Plane) (r : ℝ) :
    chartVector c hc x (r • v) = r • chartVector c hc x v := by
  unfold chartVector
  split <;> simp

lemma positiveMetricAngle_pos_smul_right
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u v : Plane) {r : ℝ} (hr : 0 < r) :
    positiveMetricAngle g o c hc x u (r • v) = positiveMetricAngle g o c hc x u v := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  simp only [positiveMetricAngle]
  rw [occupiedChartVector_smul,
    Orientation.oangle_smul_right_of_pos _ _ _ hr]

lemma positiveMetricAngle_eq_of_normalize_eq
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u : Plane) {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : NormedSpace.normalize v = NormedSpace.normalize w) :
    positiveMetricAngle g o c hc x u v = positiveMetricAngle g o c hc x u w := by
  calc
    _ = positiveMetricAngle g o c hc x u (NormedSpace.normalize v) := by
      rw [← positiveMetricAngle_pos_smul_right g o c hc x u
        (NormedSpace.normalize v) (norm_pos_iff.mpr hv), NormedSpace.norm_smul_normalize]
    _ = positiveMetricAngle g o c hc x u (NormedSpace.normalize w) := by rw [h]
    _ = _ := by
      rw [← positiveMetricAngle_pos_smul_right g o c hc x u
        (NormedSpace.normalize w) (norm_pos_iff.mpr hw), NormedSpace.norm_smul_normalize]

lemma positiveMetricAngle_self
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u : Plane) : positiveMetricAngle g o c hc x u u = 2 * Real.pi := by
  simp [positiveMetricAngle]

lemma positiveMetricAngle_surjective_Ioo
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (hu : u ≠ 0)
    {theta : ℝ} (htheta : theta ∈ Ioo 0 (2 * Real.pi)) :
    ∃ v : Plane, v ≠ 0 ∧ positiveMetricAngle g o c hc x u v = theta := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let f := occupiedChartVectorEquiv c hc x hx
  let op := planeOrientation g o p
  have hfu : f u ≠ 0 := f.map_ne_zero_iff.mpr hu
  let v := f.symm (op.rotation (theta : Real.Angle) (f u))
  have hv : v ≠ 0 := by
    dsimp [v]
    exact f.symm.map_ne_zero_iff.mpr ((op.rotation (theta : Real.Angle)).map_ne_zero_iff.mpr hfu)
  refine ⟨v, hv, ?_⟩
  have hturn : op.oangle (chartVector c hc x u) (chartVector c hc x v) = (theta : Real.Angle) := by
    rw [← occupiedChartVectorEquiv_apply c hc x hx u,
      ← occupiedChartVectorEquiv_apply c hc x hx v]
    change op.oangle (f u) (f (f.symm _)) = _
    rw [f.apply_symm_apply, op.oangle_rotation_self_right hfu]
  change (if 0 < (op.oangle _ _).toReal then
    (op.oangle _ _).toReal else (op.oangle _ _).toReal + 2 * Real.pi) = theta
  rw [hturn]
  by_cases hpi : theta ≤ Real.pi
  · rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos,htheta.1], hpi⟩]
    simp only [htheta.1, ↓reduceIte]
  · have heq : (theta : Real.Angle).toReal = theta - 2 * Real.pi :=
      Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr
        ⟨lt_of_not_ge hpi, by linarith [htheta.2,Real.pi_pos]⟩
    rw [heq, if_neg (by linarith [htheta.2])]
    ring

/-- The actual domain ray-germ characterization determines a unique angle.
The exclusions of the two boundary rays do not leave any ambiguity. -/
lemma occupiedSectorAngle_unique
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (i : Fin R.boundaryCount)
    (A : ArcPresentation (R.curve i)) (s : ℝ) (j : Fin A.count)
    (hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c)
    {alpha beta : ℝ}
    (ha : IsOccupiedSectorAngle g o c hc R i A s j alpha)
    (hb : IsOccupiedSectorAngle g o c hc R i A s j beta) : alpha = beta := by
  have hout : outgoingRay A s j ≠ 0 := by
    unfold outgoingRay
    split
    · exact A.regular _ _ (by simp)
    · exact neg_ne_zero.mpr (A.regular _ _ (by simp))
  have hin : incomingRay A s j ≠ 0 := by
    unfold incomingRay
    split
    · exact neg_ne_zero.mpr (A.regular _ _ (by simp))
    · exact A.regular _ _ (by simp)
  have hle : ∀ {a b : ℝ},
      IsOccupiedSectorAngle g o c hc R i A s j a →
      IsOccupiedSectorAngle g o c hc R i A s j b → a ≤ b := by
    intro a b hA hB
    by_contra hn
    have hba : b < a := lt_of_not_ge hn
    let phi := positiveMetricAngle g o c hc (A.arc j 1)
      (outgoingRay A s j) (incomingRay A s j)
    have htheta : ∃ theta : ℝ, b < theta ∧ theta < a ∧ theta ≠ phi := by
      obtain ⟨t, hbt, hta⟩ := exists_between hba
      by_cases htp : t = phi
      · obtain ⟨r, hbr, hrt⟩ := exists_between hbt
        exact ⟨r, hbr, hrt.trans hta, by rw [← htp]; exact hrt.ne⟩
      · exact ⟨t, hbt, hta, htp⟩
    obtain ⟨theta, hbtheta, hthetaa, hne⟩ := htheta
    obtain ⟨v, hv, hangle⟩ := positiveMetricAngle_surjective_Ioo g o c hc
      (A.arc j 1) (outgoingRay A s j) hx hout
      ⟨hB.1.trans hbtheta, hthetaa.trans hA.2.1⟩
    have hvout : NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay A s j) := by
      intro heq
      have he := positiveMetricAngle_eq_of_normalize_eq g o c hc
        (A.arc j 1) (outgoingRay A s j) hv hout heq
      rw [hangle, positiveMetricAngle_self] at he
      exact (hthetaa.trans hA.2.1).ne he
    have hvin : NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay A s j) := by
      intro heq
      have he := positiveMetricAngle_eq_of_normalize_eq g o c hc
        (A.arc j 1) (outgoingRay A s j) hv hin heq
      exact hne (hangle.symm.trans he)
    have hcut := (hA.2.2 v hv hvout hvin).symm.trans (hB.2.2 v hv hvout hvin)
    rw [hangle] at hcut
    exact (not_lt_of_gt hbtheta) (hcut.mp hthetaa)
  exact le_antisymm (hle ha hb) (hle hb ha)

end P202.GlobalGaussBonnet
end Round4OccupiedAngles


/-! Continuation: Round4RegionalRays. -/
section Round4RegionalRays

set_option autoImplicit false
open Set
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202Specs.PlanarRegionTopology P202Specs.SurfaceRegionConstruction

namespace P202.GlobalGaussBonnet

/-- A regular actual boundary tail selects a star ray with positive speed.
The conclusion identifies vectors, not merely a topological ray label. -/
lemma graphStar_velocity_pos_smul
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (g : GraphStar G p) (c : ℝ → M) (hc0 : c 0 = p)
    (delta : ℝ) (hdelta : 0 < delta) (hc : ContinuousOn c (Icc 0 delta))
    (hmem : ∀ t ∈ Icc 0 delta, c t ∈ g.neighborhood)
    (hne : ∀ t ∈ Ioo 0 delta, c t ≠ p)
    (hgraph : ∀ t ∈ Ioo 0 delta, c t ∈ G.carrier)
    (v : Plane) (hder : HasDerivAt (fun t => coordinates g.chart (c t)) v 0)
    (hv : v ≠ 0) :
    ∃ (i : Fin g.rayCount) (r : ℝ), 0 < r ∧ v = r • g.direction i := by
  obtain ⟨i, hi⟩ := P202.SurfaceRegionConstruction.BoundaryCycles.fixed_ray_of_graphStar_arc
    g c delta hdelta hc hmem hne hgraph
  have hnonzero : ∀ t ∈ Ioo 0 delta,
      coordinates g.chart (c t) - coordinates g.chart (c 0) ≠ 0 := by
    intro t ht heq
    apply hne t ht
    rw [hc0] at heq
    exact P202.SurfaceRegionConstruction.coordinates_injOn g.chart
      (hmem t ⟨ht.1.le, ht.2.le⟩).1 g.mem_source (sub_eq_zero.mp heq)
  obtain ⟨r, hr, heq⟩ :=
    P202.SurfaceRegionConstruction.BoundaryCycles.derivative_points_along_ray
      (fun t => coordinates g.chart (c t)) v (g.direction i) hder hv
      (g.direction_unit i) delta hdelta hnonzero (by simpa only [hc0] using hi)
  exact ⟨i, r, hr, heq⟩

/-- A genuine ambient coordinate germ need agree with the original curve
only on its inward one-sided parameter interval. This applies at half-space
seams, where the original manifold-valued curve need not have a two-sided
coordinate derivative. -/
lemma graphStar_ambient_velocity_pos_smul
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (g : GraphStar G p) (c : ℝ → M) (hc0 : c 0 = p)
    (delta : ℝ) (hdelta : 0 < delta) (hc : ContinuousOn c (Icc 0 delta))
    (hmem : ∀ t ∈ Icc 0 delta, c t ∈ g.neighborhood)
    (hne : ∀ t ∈ Ioo 0 delta, c t ≠ p)
    (hgraph : ∀ t ∈ Ioo 0 delta, c t ∈ G.carrier)
    (F : ℝ → Plane)
    (hagrees : ∀ t ∈ Icc 0 delta, F t = coordinates g.chart (c t))
    (v : Plane) (hder : HasDerivAt F v 0) (hv : v ≠ 0) :
    ∃ (i : Fin g.rayCount) (r : ℝ), 0 < r ∧ v = r • g.direction i := by
  obtain ⟨i, hi⟩ := P202.SurfaceRegionConstruction.BoundaryCycles.fixed_ray_of_graphStar_arc
    g c delta hdelta hc hmem hne hgraph
  have hF0 : F 0 = coordinates g.chart p := by
    rw [hagrees 0 ⟨le_rfl, hdelta.le⟩, hc0]
  have hnonzero : ∀ t ∈ Ioo 0 delta, F t - F 0 ≠ 0 := by
    intro t ht heq
    apply hne t ht
    rw [hagrees t ⟨ht.1.le, ht.2.le⟩, hF0] at heq
    exact P202.SurfaceRegionConstruction.coordinates_injOn g.chart
      (hmem t ⟨ht.1.le, ht.2.le⟩).1 g.mem_source (sub_eq_zero.mp heq)
  have hray : ∀ t ∈ Ioo 0 delta,
      F t - F 0 = ‖F t - F 0‖ • g.direction i := by
    intro t ht
    rw [hagrees t ⟨ht.1.le, ht.2.le⟩, hF0]
    exact hi t ht
  obtain ⟨r, hr, heq⟩ :=
    P202.SurfaceRegionConstruction.BoundaryCycles.derivative_points_along_ray
      F v (g.direction i) hder hv (g.direction_unit i) delta hdelta hnonzero hray
  exact ⟨i, r, hr, heq⟩

/-- The actual planar-region boundary is exactly the graph part of the
closure of its original complementary component, in its assigned chart. -/
lemma region_boundary_eq_coordinates_graph
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (R : RegionDecomposition S) (j : Fin R.regionCount) :
    (R.region j).boundary = (coordinates (R.chart j)) ''
      (closure (componentSet R.graph.carrierᶜ (R.component j)) ∩ R.graph.carrier) := by
  let C := componentSet R.graph.carrierᶜ (R.component j)
  have hsource : closure C ⊆ (R.chart j).source := R.closure_in_chart j
  have hcsource : C ⊆ (R.chart j).source := subset_closure.trans hsource
  ext x
  change x ∈ frontier (R.region j).domain ↔ _
  rw [frontier, (R.region j).open_domain.interior_eq]
  constructor
  · intro hx
    have hxcar : x ∈ (R.region j).carrier := hx.1
    rw [← R.closure_coordinates j] at hxcar
    obtain ⟨p, hp, rfl⟩ := hxcar
    have hpnot : p ∉ C := by
      intro hpC
      apply hx.2
      rw [← R.domain_coordinates j]
      exact ⟨p, hpC, rfl⟩
    have hpfr : p ∈ frontier C := by
      rw [frontier, (R.open_components j).interior_eq]
      exact ⟨hp, hpnot⟩
    refine ⟨p, ?_, rfl⟩
    exact (R.frontiers_on_graph j) ▸ hpfr
  · rintro ⟨p, hp, rfl⟩
    constructor
    · change coordinates (R.chart j) p ∈ (R.region j).carrier
      rw [← R.closure_coordinates j]
      exact ⟨p, hp.1, rfl⟩
    · intro hxdom
      rw [← R.domain_coordinates j] at hxdom
      obtain ⟨q, hq, heq⟩ := hxdom
      have hqp : q = p := P202.SurfaceRegionConstruction.coordinates_injOn
        (R.chart j) (hcsource hq) (hsource hp.1) heq
      subst q
      have hpfr : p ∈ frontier C := (R.frontiers_on_graph j).symm ▸ hp
      rw [frontier, (R.open_components j).interior_eq] at hpfr
      exact hpfr.2 hq

/-- Every presentation corner belongs to the actual graph, with its exact
assigned chart coordinates. Extra smooth subdivision corners are included. -/
lemma region_corner_on_graph
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (R : RegionDecomposition S)
    (j : Fin R.regionCount) (i : Fin (R.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((R.region j).curve i))
    (k : Fin A.count) :
    ∃ p ∈ closure (componentSet R.graph.carrierᶜ (R.component j)) ∩ R.graph.carrier,
      p ∈ (R.chart j).source ∧ coordinates (R.chart j) p = A.arc k 1 := by
  have hx : A.arc k 1 ∈ (R.region j).boundary := by
    change A.arc k 1 ∈ frontier (R.region j).domain
    rw [(R.region j).boundary_eq]
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    refine ⟨(A.time k.succ : ParameterCircle), ?_⟩
    simpa only [P202Specs.PlanarRegionTopology.realLift, mul_one, add_sub_cancel]
      using (A.agrees k 1 (by simp)).symm
  rw [region_boundary_eq_coordinates_graph R j] at hx
  obtain ⟨p, hp, he⟩ := hx
  exact ⟨p, hp, R.closure_in_chart j hp.1, he⟩

end P202.GlobalGaussBonnet
end Round4RegionalRays


/-! Continuation: Round4NormalTransport. -/
section Round4NormalTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
namespace P202.GlobalGaussBonnet

/-- A genuine differential intertwines the scalar derivatives of locally
smooth defining functions whose actual germs agree after composition. -/
theorem scalarDerivative_related_of_germ
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {Q : SmoothManifold m b N}
    (f : M → N) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace Q (f p))
    (hL : IsDifferential S Q f p L)
    (φ : M → ℝ) (ψ : N → ℝ)
    (hφ : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val φ p)
    (hψ : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      Q.smoothStructure.val ψ (f p))
    (he : φ =ᶠ[𝓝 p] ψ ∘ f) (v : TangentSpace S p) :
    scalarDerivative Q ψ (f p) (L v) = scalarDerivative S φ p v := by
  apply hL v (scalarGerm Q ψ (f p)) (scalarGerm S φ p) ψ
  · simp only [scalarGerm, dite_eq_left hψ]
  · simp only [scalarGerm, dite_eq_left hφ]
    exact Germ.coe_eq.mpr he.symm

/-- Unit inward normals commute with a surjective linear isometry and the
actual pullback of a defining conormal. No orientation is used. -/
theorem normalVector_metricPreserving
    {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 2 a M} {Q : SmoothManifold 2 b N}
    (g : RiemannianMetric S) (h : RiemannianMetric Q) (p : M) (q : N)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace Q q)
    (hL : Function.Surjective L)
    (hm : ∀ v w, pairing h q (L v) (L w) = pairing g p v w)
    (ℓ : Module.Dual ℝ (TangentSpace S p))
    (η : Module.Dual ℝ (TangentSpace Q q)) (hℓ : ℓ ≠ 0)
    (he : ∀ v, η (L v) = ℓ v) :
    L (normalVector g p ℓ) = normalVector h q η := by
  have hη : η ≠ 0 := by
    intro hz
    apply hℓ
    ext v
    simpa only [hz, LinearMap.zero_apply] using (he v).symm
  have hn := P202.Geometry.SurfaceBoundaryGeometry.normalVector_inward g p ℓ hℓ
  apply inwardUnitNormal_unique h q η _ _ _
    (P202.Geometry.SurfaceBoundaryGeometry.normalVector_inward h q η hη)
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    exact hn.1
  · intro V hV
    obtain ⟨v, rfl⟩ := hL V
    rw [hm]
    apply hn.2.1
    rwa [he] at hV
  · rw [he]
    exact hn.2.2

/-- Matching full-dimensional coordinates make the actual tangent map
bijective, including at a boundary point sent into an ambient extension. -/
theorem matchingChart_differential_bijective
    {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {Q : SmoothManifold n b N}
    (f : M → N) (hf : IsSmoothMap S Q f) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace Q (f p))
    (hL : IsDifferential S Q f p L)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ Q.smoothStructure.val)
    (hp : p ∈ c.source) (hfp : f p ∈ d.source)
    (he : ∀ᶠ q in 𝓝 p, (c q).val = (d (f q)).val) :
    Function.Bijective L := by
  let E := (tangentStructure S).fiberCoordinates.equiv c hc p hp
  let F := (tangentStructure Q).fiberCoordinates.equiv d hd (f p) hfp
  have hcoord (v : TangentSpace S p) : F (L v) = E v :=
    differential_matching_coordinates f hf p L hL c d hc hd hp hfp he
      (tangentStructure S).fiberCoordinates (tangentStructure Q).fiberCoordinates v
  constructor
  · intro v w hvw
    apply E.injective
    rw [← hcoord, ← hcoord, hvw]
  · intro w
    refine ⟨E.symm (F w), ?_⟩
    apply F.injective
    rw [hcoord, LinearEquiv.apply_symm_apply]

/-- Actual boundary normals are natural under a metric-preserving map when
the two genuine local defining functions describe the same pulled-back side. -/
theorem boundaryNormal_metricPreserving_of_germ
    {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 2 a M} {Q : SmoothManifold 2 b N}
    (g : RiemannianMetric S) (h : RiemannianMetric Q)
    (f : M → N) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace Q (f p))
    (hL : IsDifferential S Q f p L) (hsurj : Function.Surjective L)
    (hm : ∀ v w, pairing h (f p) (L v) (L w) = pairing g p v w)
    {D : Set M} {E : Set N} (B : BoundarySideAt (S := S) D p)
    (A : BoundarySideAt (S := Q) E (f p))
    (he : B.definingFunction =ᶠ[𝓝 p] A.definingFunction ∘ f) :
    L (boundaryNormal g B) = boundaryNormal h A := by
  apply normalVector_metricPreserving g h p (f p) L hsurj hm _ _ B.regular
  exact scalarDerivative_related_of_germ f p L hL _ _
    (B.smooth p B.contains) (A.smooth (f p) A.contains) he

/-- Matching actual chart coordinates discharge the surjectivity needed to
transport the genuine inward unit normals, including at a boundary seam. -/
theorem matchingChart_boundaryNormal
    {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 2 a M} {Q : SmoothManifold 2 b N}
    (g : RiemannianMetric S) (h : RiemannianMetric Q)
    (f : M → N) (hf : IsSmoothMap S Q f) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace Q (f p))
    (hL : IsDifferential S Q f p L)
    (c : ModelChart 2 a M) (d : ModelChart 2 b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ Q.smoothStructure.val)
    (hp : p ∈ c.source) (hfp : f p ∈ d.source)
    (hcoord : ∀ᶠ q in 𝓝 p, (c q).val = (d (f q)).val)
    (hm : ∀ v w, pairing h (f p) (L v) (L w) = pairing g p v w)
    {D : Set M} {E : Set N} (B : BoundarySideAt (S := S) D p)
    (A : BoundarySideAt (S := Q) E (f p))
    (he : B.definingFunction =ᶠ[𝓝 p] A.definingFunction ∘ f) :
    L (boundaryNormal g B) = boundaryNormal h A := by
  exact boundaryNormal_metricPreserving_of_germ g h f p L hL
    (matchingChart_differential_bijective f hf p L hL c d hc hd hp hfp hcoord).2 hm B A he

end P202.GlobalGaussBonnet
end Round4NormalTransport


/-! Continuation: Round4BoundaryFixedTransition. -/
section Round4BoundaryFixedTransition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The literal inverse target parameter of a source arc. Its behavior away
from the common arc image is irrelevant. -/
def boundaryArcTransition {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (j : Fin D.count) (x : ℝ) : ℝ :=
  Function.invFunOn (D.arc j).curve (Ioo (D.arc j).left (D.arc j).right) ((B.arc i).curve x)

theorem boundaryArcTransition_spec {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (j : Fin D.count) {x : ℝ}
    (hx : (B.arc i).curve x ∈ (D.arc j).curve '' Ioo (D.arc j).left (D.arc j).right) :
    boundaryArcTransition B D i j x ∈ Ioo (D.arc j).left (D.arc j).right ∧
      (D.arc j).curve (boundaryArcTransition B D i j x) = (B.arc i).curve x := by
  obtain ⟨y, hy, heq⟩ := hx
  have hφ : boundaryArcTransition B D i j x = y := by
    unfold boundaryArcTransition
    rw [← heq]
    exact (D.injective j).leftInvOn_invFunOn hy
  exact ⟨hφ.symm ▸ hy, by rw [hφ]; exact heq⟩

/-- One fixed inverse, rather than a different transition chosen at each
point, is differentiable with nonzero derivative throughout any cut-free
open subarc lying in one target arc. -/
theorem boundaryArcTransition_differentiable {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (i : Fin B.count) (j : Fin D.count)
    {l r : ℝ}
    (hsub : Ioo l r ⊆ Ioo (B.arc i).left (B.arc i).right)
    (hmaps : (B.arc i).curve '' Ioo l r ⊆
      (D.arc j).curve '' Ioo (D.arc j).left (D.arc j).right)
    (hcuts : Disjoint (Ioo l r) ((B.arc i).curve ⁻¹' boundaryEndpointSet D)) :
    ∀ x ∈ Ioo l r,
      HasDerivAt (boundaryArcTransition B D i j)
        (deriv (boundaryArcTransition B D i j) x) x ∧
      deriv (boundaryArcTransition B D i j) x ≠ 0 := by
  intro x hx
  obtain ⟨ht, heq⟩ := boundaryArcTransition_spec B D i j (hmaps ⟨x, hx, rfl⟩)
  have hne : (D.arc j).curve (boundaryArcTransition B D i j x) ∉ boundaryEndpointSet D := by
    rw [heq]
    exact fun he => Set.disjoint_left.mp hcuts hx he
  obtain ⟨ψ, k, hk, hψx, hψder, hψmaps, hψcurve⟩ :=
    boundary_arc_differentiable_transition B D i j x (boundaryArcTransition B D i j x)
      (hsub hx) ht heq.symm hne
  have hgerm : boundaryArcTransition B D i j =ᶠ[𝓝 x] ψ := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2, hψmaps, hψcurve] with y hy hψy heqy
    have hφy := boundaryArcTransition_spec B D i j (hmaps ⟨y, hy, rfl⟩)
    exact D.injective j hφy.1 hψy (hφy.2.trans heqy.symm)
  have hφder : HasDerivAt (boundaryArcTransition B D i j) k x :=
    hψder.congr_of_eventuallyEq hgerm
  exact ⟨hφder.deriv ▸ hφder, hφder.deriv.symm ▸ hk⟩

/-- The fixed inverse parameter is continuous and strictly oriented on the
whole cut interval, and extends continuously to its two endpoints. -/
theorem boundary_subarc_transition_extension {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (i : Fin B.count) (l r : ℝ) (hlr : l < r)
    (hsub : Ioo l r ⊆ Ioo (B.arc i).left (B.arc i).right)
    (hcuts : Disjoint (Ioo l r) ((B.arc i).curve ⁻¹' boundaryEndpointSet D)) :
    ∃ (j : Fin D.count) (φ : ℝ → ℝ),
      ContinuousOn φ (Icc l r) ∧
      MapsTo φ (Icc l r) (Icc (D.arc j).left (D.arc j).right) ∧
      MapsTo φ (Ioo l r) (Ioo (D.arc j).left (D.arc j).right) ∧
      (∀ x ∈ Ioo l r, (D.arc j).curve (φ x) = (B.arc i).curve x) ∧
      (∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x ∧ deriv φ x ≠ 0) ∧
      ((StrictMonoOn φ (Icc l r) ∧ ∀ x ∈ Ioo l r, 0 < deriv φ x) ∨
        (StrictAntiOn φ (Icc l r) ∧ ∀ x ∈ Ioo l r, deriv φ x < 0)) := by
  obtain ⟨j, hj⟩ := boundary_subarc_subset_one_openArc B D i l r hlr hsub hcuts
  let ψ := boundaryArcTransition B D i j
  have hψ : ∀ x ∈ Ioo l r, ψ x ∈ Ioo (D.arc j).left (D.arc j).right ∧
      (D.arc j).curve (ψ x) = (B.arc i).curve x :=
    fun x hx => boundaryArcTransition_spec B D i j (hj ⟨x, hx, rfl⟩)
  have hd : ∀ x ∈ Ioo l r, HasDerivAt ψ (deriv ψ x) x ∧ deriv ψ x ≠ 0 :=
    boundaryArcTransition_differentiable B D i j hsub hj hcuts
  have hc : ContinuousOn ψ (Ioo l r) := fun x hx => (hd x hx).1.continuousAt.continuousWithinAt
  have hinj : InjOn ψ (Ioo l r) := by
    intro x hx y hy heq
    apply B.injective i (hsub hx) (hsub hy)
    rw [← (hψ x hx).2, ← (hψ y hy).2, heq]
  obtain ⟨φ, hcφ, heq, hmapφ, hdφ, hsign⟩ := bounded_interval_transition_extension hlr hc hinj
    (fun x hx => (hd x hx).1.differentiableAt) (fun x hx => (hd x hx).2)
    (fun x hx => Ioo_subset_Icc_self (hψ x hx).1)
  have hder : ∀ x ∈ Ioo l r, deriv φ x = deriv ψ x := fun x hx => (hdφ x hx).deriv
  refine ⟨j, φ, hcφ, hmapφ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [heq hx]
    exact (hψ x hx).1
  · intro x hx
    rw [heq hx]
    exact (hψ x hx).2
  · intro x hx
    exact ⟨hder x hx ▸ hdφ x hx, hder x hx ▸ (hd x hx).2⟩
  · rcases hsign with ⟨hm, hs⟩ | ⟨hm, hs⟩
    · exact Or.inl ⟨hm, fun x hx => (hder x hx).symm ▸ hs x hx⟩
    · exact Or.inr ⟨hm, fun x hx => (hder x hx).symm ▸ hs x hx⟩

/-- The continuous transition matches the actual curves at the cut endpoints
as well, and maps each open/closed parameter interval onto its endpoint
image interval without any multiplicity. -/
theorem boundary_subarc_transition_closed {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (i : Fin B.count) (l r : ℝ) (hlr : l < r)
    (hsub : Ioo l r ⊆ Ioo (B.arc i).left (B.arc i).right)
    (hcuts : Disjoint (Ioo l r) ((B.arc i).curve ⁻¹' boundaryEndpointSet D)) :
    ∃ (j : Fin D.count) (φ : ℝ → ℝ),
      ContinuousOn φ (Icc l r) ∧
      MapsTo φ (Icc l r) (Icc (D.arc j).left (D.arc j).right) ∧
      MapsTo φ (Ioo l r) (Ioo (D.arc j).left (D.arc j).right) ∧
      (∀ x ∈ Icc l r, (D.arc j).curve (φ x) = (B.arc i).curve x) ∧
      (∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x ∧ deriv φ x ≠ 0) ∧
      φ '' Ioo l r = uIoo (φ l) (φ r) ∧
      φ '' Icc l r = uIcc (φ l) (φ r) ∧
      ((StrictMonoOn φ (Icc l r) ∧ ∀ x ∈ Ioo l r, 0 < deriv φ x) ∨
        (StrictAntiOn φ (Icc l r) ∧ ∀ x ∈ Ioo l r, deriv φ x < 0)) := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  obtain ⟨j, φ, hc, hmaps, hopen, heq, hd, hsign⟩ :=
    boundary_subarc_transition_extension B D i l r hlr hsub hcuts
  have hclosed : Icc l r ⊆ Icc (B.arc i).left (B.arc i).right := by
    have h := closure_mono hsub
    simpa only [closure_Ioo hlr.ne, closure_Ioo (B.arc i).ordered.ne] using h
  have heqclosed : EqOn (fun x => (D.arc j).curve (φ x)) (B.arc i).curve (Icc l r) := by
    exact Set.EqOn.of_subset_closure heq ((D.arc j).continuous.comp hc hmaps)
      ((B.arc i).continuous.mono hclosed) Ioo_subset_Icc_self
      (by rw [closure_Ioo hlr.ne])
  refine ⟨j, φ, hc, hmaps, hopen, heqclosed, hd, ?_, ?_, hsign⟩
  · rcases hsign with ⟨hm, _⟩ | ⟨hm, _⟩
    · have hlt := hm (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr
      rw [uIoo_of_lt hlt]
      exact hc.image_Ioo_of_strictMonoOn hlr.le hm
    · have hlt := hm (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr
      rw [uIoo_of_gt hlt]
      exact hc.image_Ioo_of_strictAntiOn hlr.le hm
  · rcases hsign with ⟨hm, _⟩ | ⟨hm, _⟩
    · have hlt := hm (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr
      rw [uIcc_of_lt hlt]
      exact hc.image_Icc_of_monotoneOn hlr.le hm.monotoneOn
    · have hlt := hm (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr
      rw [uIcc_of_gt hlt]
      exact hc.image_Icc_of_antitoneOn hlr.le hm.antitoneOn
end P202.GlobalGaussBonnet
end Round4BoundaryFixedTransition


/-! Continuation: Round4BoundaryDensity. -/
section Round4BoundaryDensity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.SurfaceBoundaryData
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

theorem pairing_heq (g : RiemannianMetric S) {p q : M} (hp : p = q)
    {V N : TangentSpace S p} {W P : TangentSpace S q}
    (hV : HEq V W) (hN : HEq N P) : pairing g p V N = pairing g q W P := by
  subst q
  cases hV
  cases hN
  rfl

theorem normalizedVector_heq (g : RiemannianMetric S) {p q : M} (hp : p = q)
    {V : TangentSpace S p} {W : TangentSpace S q} (hV : HEq V W) :
    HEq ((tangentNorm g p V)⁻¹ • V) ((tangentNorm g q W)⁻¹ • W) := by
  subst q
  cases hV
  rfl

theorem regularArc_velocity_transition_heq {g : RiemannianMetric S}
    (c d : RegularArc g) (φ : ℝ → ℝ) (s a : ℝ)
    (hs : s ∈ Ioo c.left c.right) (ht : φ s ∈ Ioo d.left d.right)
    (hd : HasDerivAt φ a s)
    (heq : (d.curve ∘ φ) =ᶠ[𝓝 s] c.curve) :
    HEq (a • d.velocity (φ s)) (c.velocity s) := by
  have hv := P202.Geometry.PiecewiseCurves.HasVelocityAt.reparam (d.hasVelocity (φ s) ht) hd
  have hc := P202.Geometry.PiecewiseCurves.HasVelocityAt.congr hv heq
  have h := P202.Geometry.PiecewiseCurves.hasVelocityAt_unique hc (c.hasVelocity s hs)
  exact ((cast_heq _ _).symm).trans (heq_of_eq h)

theorem regularArc_tangent_transition_pos {g : RiemannianMetric S}
    (c d : RegularArc g) (φ : ℝ → ℝ) (s a : ℝ)
    (hs : s ∈ Ioo c.left c.right) (ht : φ s ∈ Ioo d.left d.right)
    (hd : HasDerivAt φ a s) (ha : 0 < a)
    (heq : (d.curve ∘ φ) =ᶠ[𝓝 s] c.curve) :
    HEq (d.tangent (φ s)) (c.tangent s) := by
  have h := normalizedVector_heq g heq.eq_of_nhds
    (regularArc_velocity_transition_heq c d φ s a hs ht hd heq)
  have hscale : (tangentNorm g (d.curve (φ s)) (a • d.velocity (φ s)))⁻¹ •
      (a • d.velocity (φ s)) = d.tangent (φ s) := by
    dsimp [RegularArc.tangent, unitTangent]
    rw [P202.Geometry.SmoothMetrics.tangentNorm_smul, abs_of_pos ha,
      smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt ha), mul_one]
  change HEq _ (c.tangent s) at h
  dsimp only [Function.comp_apply] at h
  rw [hscale] at h
  exact h

theorem regularArc_tangent_transition_neg {g : RiemannianMetric S}
    (c d : RegularArc g) (φ : ℝ → ℝ) (s a : ℝ)
    (hs : s ∈ Ioo c.left c.right) (ht : φ s ∈ Ioo d.left d.right)
    (hd : HasDerivAt φ a s) (ha : a < 0)
    (heq : (d.curve ∘ φ) =ᶠ[𝓝 s] c.curve) :
    HEq (-d.tangent (φ s)) (c.tangent s) := by
  have h := normalizedVector_heq g heq.eq_of_nhds
    (regularArc_velocity_transition_heq c d φ s a hs ht hd heq)
  have hscale : (tangentNorm g (d.curve (φ s)) (a • d.velocity (φ s)))⁻¹ •
      (a • d.velocity (φ s)) = -d.tangent (φ s) := by
    dsimp [RegularArc.tangent, unitTangent]
    rw [P202.Geometry.SmoothMetrics.tangentNorm_smul, abs_of_neg ha,
      smul_smul, mul_inv_rev]
    have he : (tangentNorm g (d.curve (φ s)) (d.velocity (φ s)))⁻¹ * (-a)⁻¹ * a =
        -(tangentNorm g (d.curve (φ s)) (d.velocity (φ s)))⁻¹ := by
      field_simp [ne_of_lt ha]
    rw [he]
    exact neg_smul ((tangentNorm g (d.curve (φ s)) (d.velocity (φ s)))⁻¹) (d.velocity (φ s))
  change HEq _ (c.tangent s) at h
  dsimp only [Function.comp_apply] at h
  rw [hscale] at h
  exact h

/-- Actual covariant curvature density for two independent curve functions,
under an increasing common parameter transition and equal normal vectors. -/
theorem regularArc_covariantDensity_reparam_pos {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (Nc : (t : ℝ) → TangentSpace S (c.curve t))
    (Nd : (t : ℝ) → TangentSpace S (d.curve t))
    (φ : ℝ → ℝ) {l r s : ℝ} (hs : s ∈ Ioo l r)
    (hsub : Ioo l r ⊆ Ioo c.left c.right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo d.left d.right))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hpos : ∀ x ∈ Ioo l r, 0 < deriv φ x)
    (hcurve : ∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x)
    (hnormal : HEq (Nd (φ s)) (Nc s)) :
    pairing g (c.curve s) (covariantDerivative C c.curve c.tangent s) (Nc s) =
      pairing g (d.curve (φ s)) (covariantDerivative C d.curve d.tangent (φ s))
        (Nd (φ s)) * |deriv φ s| := by
  have hgerm : ∀ x ∈ Ioo l r, (d.curve ∘ φ) =ᶠ[𝓝 x] c.curve := by
    intro x hx
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hcurve y hy
  obtain ⟨D, hD⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative g C d (φ s) (hmaps hs)
  have hcomp := P202.Geometry.CurveCovariantDerivative.ordinary_reparam C hD (hder s hs)
  have hT : ∀ᶠ x in 𝓝 s, HEq (d.tangent (φ x)) (c.tangent x) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    exact regularArc_tangent_transition_pos c d φ x (deriv φ x)
      (hsub hx) (hmaps hx) (hder x hx) (hpos x hx) (hgerm x hx)
  obtain ⟨D', hDD', hD'⟩ := hasCovariantDerivativeAt_congr_curve C hcomp (hgerm s hs) hT
  dsimp only [covariantDerivative]
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ s) uniqueDiffWithinAt_univ hD',
    P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ (φ s)) uniqueDiffWithinAt_univ hD]
  rw [← pairing_heq g (hcurve s hs) hDD' hnormal,
    LinearMap.BilinForm.smul_left, abs_of_pos (hpos s hs), mul_comm]

theorem regularArc_covariantDensity_reparam_neg {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (Nc : (t : ℝ) → TangentSpace S (c.curve t))
    (Nd : (t : ℝ) → TangentSpace S (d.curve t))
    (φ : ℝ → ℝ) {l r s : ℝ} (hs : s ∈ Ioo l r)
    (hsub : Ioo l r ⊆ Ioo c.left c.right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo d.left d.right))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hneg : ∀ x ∈ Ioo l r, deriv φ x < 0)
    (hcurve : ∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x)
    (hnormal : HEq (Nd (φ s)) (Nc s)) :
    pairing g (c.curve s) (covariantDerivative C c.curve c.tangent s) (Nc s) =
      pairing g (d.curve (φ s)) (covariantDerivative C d.curve d.tangent (φ s))
        (Nd (φ s)) * |deriv φ s| := by
  have hgerm : ∀ x ∈ Ioo l r, (d.curve ∘ φ) =ᶠ[𝓝 x] c.curve := by
    intro x hx
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hcurve y hy
  obtain ⟨D, hD⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative g C d (φ s) (hmaps hs)
  have hcomp := P202.Geometry.CurveCovariantDerivative.ordinary_reparam C hD (hder s hs)
  have hcompneg := P202.Geometry.CurveCovariantDerivative.derivative_const_smul C hcomp (-1)
  simp only [neg_one_smul] at hcompneg
  have hT : ∀ᶠ x in 𝓝 s, HEq (-d.tangent (φ x)) (c.tangent x) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    exact regularArc_tangent_transition_neg c d φ x (deriv φ x)
      (hsub hx) (hmaps hx) (hder x hx) (hneg x hx) (hgerm x hx)
  obtain ⟨D', hDD', hD'⟩ := hasCovariantDerivativeAt_congr_curve C hcompneg (hgerm s hs) hT
  dsimp only [covariantDerivative]
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ s) uniqueDiffWithinAt_univ hD',
    P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ (φ s)) uniqueDiffWithinAt_univ hD]
  rw [← pairing_heq g (hcurve s hs) hDD' hnormal]
  simp only [map_neg, LinearMap.neg_apply, LinearMap.BilinForm.smul_left, abs_of_neg (hneg s hs)]
  ring
end P202.GlobalGaussBonnet
end Round4BoundaryDensity


/-! Continuation: Round4BoundarySubarcIntegral. -/
section Round4BoundarySubarcIntegral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The actual side normal of an arc, with an irrelevant zero extension. -/
def boundaryArcNormal {g : RiemannianMetric S} (B : BoundaryPresentation g)
    (i : Fin B.count) (t : ℝ) : TangentSpace S ((B.arc i).curve t) :=
  if ht : t ∈ Ioo (B.arc i).left (B.arc i).right then boundaryNormal g (B.side i t ht) else 0

theorem boundary_curvatureIntegrand_eq_arcNormal {g : RiemannianMetric S}
    (B : BoundaryPresentation g) (C : Connection (tangentBundle S)) (i : Fin B.count)
    {t : ℝ} (ht : t ∈ Ioo (B.arc i).left (B.arc i).right) :
    B.curvatureIntegrand C i t = pairing g ((B.arc i).curve t)
      (covariantDerivative C (B.arc i).curve (B.arc i).tangent t) (boundaryArcNormal B i t) := by
  rw [boundary_curvatureIntegrand_eq g B C i t ht, boundaryArcNormal, dite_eq_left ht]

theorem boundaryArcNormal_heq {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (j : Fin D.count) {s t : ℝ}
    (hs : s ∈ Ioo (B.arc i).left (B.arc i).right)
    (ht : t ∈ Ioo (D.arc j).left (D.arc j).right)
    (hp : (D.arc j).curve t = (B.arc i).curve s) :
    HEq (boundaryArcNormal D j t) (boundaryArcNormal B i s) := by
  rw [boundaryArcNormal, boundaryArcNormal, dite_eq_left ht, dite_eq_left hs]
  have hb : (D.arc j).curve t ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S := by
    rw [D.covers]
    exact mem_iUnion.mpr ⟨j, t, Ioo_subset_Icc_self ht, rfl⟩
  have key : ∀ (p q : M) (h : p = q)
      (bp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
      (b₁ : BoundarySideAt (S := S) univ p) (b₂ : BoundarySideAt (S := S) univ q),
      HEq (boundaryNormal g b₁) (boundaryNormal g b₂) := by
    rintro p q rfl bp b₁ b₂
    exact heq_of_eq (boundaryNormal_eq g bp b₂ b₁)
  exact key _ _ hp hb (D.side j t ht) (B.side i s hs)

/-- The genuine boundary density, for independently represented arcs, is
multiplied by the unsigned derivative of their transition. -/
theorem boundary_curvatureIntegrand_reparam {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (C : Connection (tangentBundle S))
    (i : Fin B.count) (j : Fin D.count) (φ : ℝ → ℝ) {l r : ℝ}
    (hsub : Ioo l r ⊆ Ioo (B.arc i).left (B.arc i).right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo (D.arc j).left (D.arc j).right))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hsign : (∀ x ∈ Ioo l r, 0 < deriv φ x) ∨ (∀ x ∈ Ioo l r, deriv φ x < 0))
    (hcurve : ∀ x ∈ Ioo l r, (D.arc j).curve (φ x) = (B.arc i).curve x) :
    ∀ s ∈ Ioo l r,
      B.curvatureIntegrand C i s = D.curvatureIntegrand C j (φ s) * |deriv φ s| := by
  intro s hs
  rw [boundary_curvatureIntegrand_eq_arcNormal B C i (hsub hs),
    boundary_curvatureIntegrand_eq_arcNormal D C j (hmaps hs)]
  rcases hsign with hpos | hneg
  · exact regularArc_covariantDensity_reparam_pos C (B.arc i) (D.arc j)
      (boundaryArcNormal B i) (boundaryArcNormal D j) φ hs hsub hmaps hder hpos hcurve
      (boundaryArcNormal_heq B D i j (hsub hs) (hmaps hs) (hcurve s hs))
  · exact regularArc_covariantDensity_reparam_neg C (B.arc i) (D.arc j)
      (boundaryArcNormal B i) (boundaryArcNormal D j) φ hs hsub hmaps hder hneg hcurve
      (boundaryArcNormal_heq B D i j (hsub hs) (hmaps hs) (hcurve s hs))

/-- Complete curvature-integral transport on any genuine cut-free subarc.
The target endpoints have increasing order even for a reversed transition. -/
theorem boundary_subarc_curvatureIntegral_eq {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (C : Connection (tangentBundle S))
    (i : Fin B.count) (l r : ℝ) (hlr : l < r)
    (hsub : Ioo l r ⊆ Ioo (B.arc i).left (B.arc i).right)
    (hcuts : Disjoint (Ioo l r) ((B.arc i).curve ⁻¹' boundaryEndpointSet D)) :
    ∃ (j : Fin D.count) (a b : ℝ),
      (D.arc j).left ≤ a ∧ a < b ∧ b ≤ (D.arc j).right ∧
      (B.arc i).curve '' Ioo l r = (D.arc j).curve '' Ioo a b ∧
      (∫ t in l..r, B.curvatureIntegrand C i t) =
        ∫ t in a..b, D.curvatureIntegrand C j t := by
  obtain ⟨j, φ, hc, hmapsc, hmaps, hcurve, hd, himage, _, hsign⟩ :=
    boundary_subarc_transition_closed B D i l r hlr hsub hcuts
  have hφl := hmapsc (left_mem_Icc.mpr hlr.le)
  have hφr := hmapsc (right_mem_Icc.mpr hlr.le)
  have hdensity := boundary_curvatureIntegrand_reparam B D C i j φ hsub hmaps
    (fun x hx => (hd x hx).1) (hsign.imp And.right And.right)
    (fun x hx => hcurve x (Ioo_subset_Icc_self hx))
  have heq : (∫ t in l..r, B.curvatureIntegrand C i t) =
      ∫ t in l..r, D.curvatureIntegrand C j (φ t) * |deriv φ t| := by
    exact intervalIntegral.integral_congr_Ioo_of_le hlr.le hdensity
  rcases hsign with ⟨hm, hpos⟩ | ⟨hm, hneg⟩
  · have hlt := hm (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr
    refine ⟨j, φ l, φ r, hφl.1, hlt, hφr.2, ?_, ?_⟩
    · rw [uIoo_of_lt hlt] at himage
      rw [← himage, image_image]
      exact Set.image_congr (fun t ht => hcurve t (Ioo_subset_Icc_self ht)) |>.symm
    · rw [heq]
      calc
        _ = ∫ t in l..r, D.curvatureIntegrand C j (φ t) * deriv φ t := by
          apply intervalIntegral.integral_congr_Ioo_of_le hlr.le
          intro t ht
          dsimp only
          rw [abs_of_pos (hpos t ht)]
        _ = _ := by
          simpa only [Function.comp_apply] using (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (f := φ) (f' := deriv φ) (g := D.curvatureIntegrand C j) (a := l) (b := r)
            (by simpa only [uIcc_of_le hlr.le] using hc)
            (by simpa only [min_eq_left hlr.le, max_eq_right hlr.le] using fun t ht => (hd t ht).1)
            (by simpa only [min_eq_left hlr.le, max_eq_right hlr.le] using fun t ht => (hpos t ht).le))
  · have hlt := hm (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr
    refine ⟨j, φ r, φ l, hφr.1, hlt, hφl.2, ?_, ?_⟩
    · rw [uIoo_of_gt hlt] at himage
      rw [← himage, image_image]
      exact Set.image_congr (fun t ht => hcurve t (Ioo_subset_Icc_self ht)) |>.symm
    · rw [heq]
      calc
        _ = -(∫ t in l..r, D.curvatureIntegrand C j (φ t) * deriv φ t) := by
          rw [← intervalIntegral.integral_neg]
          apply intervalIntegral.integral_congr_Ioo_of_le hlr.le
          intro t ht
          dsimp only
          rw [abs_of_neg (hneg t ht)]
          ring
        _ = -(∫ t in φ l..φ r, D.curvatureIntegrand C j t) := by
          simpa only [Function.comp_apply] using (congrArg Neg.neg
            (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (f := φ) (f' := deriv φ) (a := l) (b := r)
            (g := D.curvatureIntegrand C j)
              (by simpa only [uIcc_of_le hlr.le] using hc)
              (by simpa only [min_eq_left hlr.le, max_eq_right hlr.le] using fun t ht => (hd t ht).1)
            (by simpa only [min_eq_left hlr.le, max_eq_right hlr.le] using fun t ht => (hneg t ht).le)))
        _ = _ := (intervalIntegral.integral_symm (φ l) (φ r)).symm
end P202.GlobalGaussBonnet
end Round4BoundarySubarcIntegral


/-! Continuation: Round4FiniteGaps. -/
section Round4FiniteGaps
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace P202.GlobalGaussBonnet

/-- Adjacent ordered members of a finite set of real cuts. -/
def FiniteGap (F : Finset ℝ) :=
  {p : F × F // p.1.val < p.2.val ∧ Disjoint (Ioo p.1.val p.2.val) (F : Set ℝ)}
namespace FiniteGap
variable {F : Finset ℝ}
def left (q : FiniteGap F) : ℝ := q.val.1.val
def right (q : FiniteGap F) : ℝ := q.val.2.val
instance : Fintype (FiniteGap F) := by
  classical
  exact inferInstanceAs (Fintype {p : F × F // _})
theorem ordered (q : FiniteGap F) : q.left < q.right := q.property.1
theorem left_mem (q : FiniteGap F) : q.left ∈ F := q.val.1.property
theorem right_mem (q : FiniteGap F) : q.right ∈ F := q.val.2.property
theorem avoids (q : FiniteGap F) : Disjoint (Ioo q.left q.right) (F : Set ℝ) := q.property.2

/-- Each non-cut point between two cuts belongs to an adjacent cut interval. -/
theorem containing (F : Finset ℝ) {l r x : ℝ} (hl : l ∈ F) (hr : r ∈ F)
    (hx : x ∈ Ioo l r) (hnot : x ∉ F) :
    ∃ q : FiniteGap F, x ∈ Ioo q.left q.right := by
  obtain ⟨a, ha, hax, hmax⟩ := F.exists_next_left ⟨l, hl, hx.1⟩
  obtain ⟨b, hb, hxb, hmin⟩ := F.exists_next_right ⟨r, hr, hx.2⟩
  have hav : Disjoint (Ioo a b) (F : Set ℝ) := by
    apply Set.disjoint_left.mpr
    intro z hz hzF
    rcases lt_trichotomy z x with hzx | hzx | hxz
    · exact (hmax z hzF hzx).not_gt hz.1
    · exact hnot (hzx ▸ hzF)
    · exact (hmin z hzF hxz).not_gt hz.2
  exact ⟨⟨(⟨a, ha⟩, ⟨b, hb⟩), hax.trans hxb, hav⟩, hax, hxb⟩

theorem disjoint (F : Finset ℝ) : Pairwise (fun q p : FiniteGap F =>
    Disjoint (Ioo q.left q.right) (Ioo p.left p.right)) := by
  intro q p hqp
  apply Set.disjoint_left.mpr
  rintro x hxq hxp
  have hl : q.left = p.left := by
    apply le_antisymm
    · by_contra h
      exact Set.disjoint_left.mp p.avoids ⟨lt_of_not_ge h, hxq.1.trans hxp.2⟩ q.left_mem
    · by_contra h
      exact Set.disjoint_left.mp q.avoids ⟨lt_of_not_ge h, hxp.1.trans hxq.2⟩ p.left_mem
  have hr : q.right = p.right := by
    apply le_antisymm
    · by_contra h
      exact Set.disjoint_left.mp q.avoids ⟨hxq.1.trans hxp.2, lt_of_not_ge h⟩ p.right_mem
    · by_contra h
      exact Set.disjoint_left.mp p.avoids ⟨hxp.1.trans hxq.2, lt_of_not_ge h⟩ q.right_mem
  apply hqp
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hl) (Subtype.ext hr)
end FiniteGap

/-- Finite disjoint open subintervals covering an interval off finitely many
points recover its full integral. Their order in the finite index is arbitrary. -/
theorem intervalIntegral_eq_sum_of_finite_cover {κ : Type*} [Fintype κ]
    (f : ℝ → ℝ) {l r : ℝ} (hlr : l ≤ r) (a b : κ → ℝ)
    (hordered : ∀ k, a k ≤ b k)
    (hsub : ∀ k, Ioo (a k) (b k) ⊆ Ioo l r)
    (hdisj : Pairwise (fun k j => Disjoint (Ioo (a k) (b k)) (Ioo (a j) (b j))))
    (E : Set ℝ) (hE : E.Finite)
    (hcover : Ioo l r \ E ⊆ ⋃ k, Ioo (a k) (b k))
    (hf : IntervalIntegrable f volume l r) :
    (∫ x in l..r, f x) = ∑ k, ∫ x in a k..b k, f x := by
  have heq : Ioo l r =ᵐ[volume] ⋃ k, Ioo (a k) (b k) := by
    filter_upwards [hE.countable.ae_notMem volume] with x hx
    apply propext
    constructor
    · intro hxl
      exact hcover ⟨hxl, hx⟩
    · intro hxU
      obtain ⟨k, hk⟩ := mem_iUnion.mp hxU
      exact hsub k hk
  have hfi : IntegrableOn f (Ioo l r) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mp hf
  rw [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_set heq, integral_iUnion_fintype (fun _ => measurableSet_Ioo) hdisj
      (fun k => hfi.mono_set (hsub k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_of_le (hordered k), integral_Ioc_eq_integral_Ioo]

end P202.GlobalGaussBonnet
end Round4FiniteGaps


/-! Continuation: Round4BoundaryComparison. -/
section Round4BoundaryComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

def boundaryCutParameters {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) : Finset ℝ := by
  classical
  exact insert (B.arc i).left (insert (B.arc i).right
    (boundaryEndpoint_cutParameters_finite B D i).toFinset)

theorem mem_boundaryCutParameters {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (t : ℝ) :
    t ∈ boundaryCutParameters B D i ↔
      t = (B.arc i).left ∨ t = (B.arc i).right ∨
        (t ∈ Ioo (B.arc i).left (B.arc i).right ∧ (B.arc i).curve t ∈ boundaryEndpointSet D) := by
  classical
  simp [boundaryCutParameters]

theorem boundaryCutParameters_bounds {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) : (boundaryCutParameters B D i : Set ℝ) ⊆ Icc (B.arc i).left (B.arc i).right := by
  intro t ht
  rcases (mem_boundaryCutParameters B D i t).mp ht with rfl | rfl | ht
  · exact left_mem_Icc.mpr (B.arc i).ordered.le
  · exact right_mem_Icc.mpr (B.arc i).ordered.le
  · exact Ioo_subset_Icc_self ht.1

theorem boundaryGap_sub {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (q : FiniteGap (boundaryCutParameters B D i)) :
    Ioo q.left q.right ⊆ Ioo (B.arc i).left (B.arc i).right := by
  intro x hx
  exact ⟨(boundaryCutParameters_bounds B D i q.left_mem).1.trans_lt hx.1,
    hx.2.trans_le (boundaryCutParameters_bounds B D i q.right_mem).2⟩

theorem boundaryGap_avoids {g : RiemannianMetric S} (B D : BoundaryPresentation g)
    (i : Fin B.count) (q : FiniteGap (boundaryCutParameters B D i)) :
    Disjoint (Ioo q.left q.right) ((B.arc i).curve ⁻¹' boundaryEndpointSet D) := by
  apply Set.disjoint_left.mpr
  intro x hx hxe
  apply Set.disjoint_left.mp q.avoids hx
  exact (mem_boundaryCutParameters B D i x).mpr (Or.inr (Or.inr ⟨boundaryGap_sub B D i q hx, hxe⟩))

def BoundaryGap {g : RiemannianMetric S} (B D : BoundaryPresentation g) :=
  Σ i : Fin B.count, FiniteGap (boundaryCutParameters B D i)
instance {g : RiemannianMetric S} (B D : BoundaryPresentation g) : Fintype (BoundaryGap B D) :=
  inferInstanceAs (Fintype (Σ i : Fin B.count, FiniteGap (boundaryCutParameters B D i)))

theorem boundaryGap_images_disjoint {g : RiemannianMetric S} (B D : BoundaryPresentation g) :
    Pairwise (fun k z : BoundaryGap B D => Disjoint
      ((B.arc k.1).curve '' Ioo k.2.left k.2.right)
      ((B.arc z.1).curve '' Ioo z.2.left z.2.right)) := by
  intro ⟨i, q⟩ ⟨j, p⟩ hne
  by_cases hij : i = j
  · subst j
    have hqp : q ≠ p := fun h => hne (by cases h; rfl)
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
    have hts := B.injective i (boundaryGap_sub B D i p ht) (boundaryGap_sub B D i q hs) he
    exact Set.disjoint_left.mp (FiniteGap.disjoint _ hqp) hs (hts ▸ ht)
  · exact (B.disjoint hij).mono (image_mono (boundaryGap_sub B D i q))
      (image_mono (boundaryGap_sub B D j p))

theorem boundary_arc_integral_eq_sum_gaps {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (C : Connection (tangentBundle S))
    (i : Fin B.count)
    (hf : IntervalIntegrable (B.curvatureIntegrand C i) volume (B.arc i).left (B.arc i).right) :
    (∫ x in (B.arc i).left..(B.arc i).right, B.curvatureIntegrand C i x) =
      ∑ q : FiniteGap (boundaryCutParameters B D i),
        ∫ x in q.left..q.right, B.curvatureIntegrand C i x := by
  apply intervalIntegral_eq_sum_of_finite_cover _ (B.arc i).ordered.le
    FiniteGap.left FiniteGap.right (fun q => q.ordered.le) (boundaryGap_sub B D i)
    (FiniteGap.disjoint _) (boundaryCutParameters B D i) (Finset.finite_toSet _) _ hf
  intro x hx
  obtain ⟨q, hq⟩ := FiniteGap.containing (boundaryCutParameters B D i)
    ((mem_boundaryCutParameters B D i _).mpr (Or.inl rfl))
    ((mem_boundaryCutParameters B D i _).mpr (Or.inr (Or.inl rfl))) hx.1 hx.2
  exact mem_iUnion.mpr ⟨q, hq⟩

/-- All actual finite presentations have the same integral. The explicit
integrability premises are discharged by boundary_curvatureIntegrand_integrable
in the unconditional wrapper; the geometric comparison uses no LC assumption. -/
theorem boundary_curvatureIntegral_eq_of_integrable {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (C : Connection (tangentBundle S))
    (hB : ∀ i, IntervalIntegrable (B.curvatureIntegrand C i) volume (B.arc i).left (B.arc i).right)
    (hD : ∀ j, IntervalIntegrable (D.curvatureIntegrand C j) volume (D.arc j).left (D.arc j).right) :
    B.curvatureIntegral C = D.curvatureIntegral C := by
  classical
  let κ := BoundaryGap B D
  have htransport : ∀ k : κ, ∃ (j : Fin D.count) (a b : ℝ),
      (D.arc j).left ≤ a ∧ a < b ∧ b ≤ (D.arc j).right ∧
      (B.arc k.1).curve '' Ioo k.2.left k.2.right = (D.arc j).curve '' Ioo a b ∧
      (∫ t in k.2.left..k.2.right, B.curvatureIntegrand C k.1 t) =
        ∫ t in a..b, D.curvatureIntegrand C j t := by
    intro k
    exact boundary_subarc_curvatureIntegral_eq B D C k.1 k.2.left k.2.right k.2.ordered
      (boundaryGap_sub B D k.1 k.2) (boundaryGap_avoids B D k.1 k.2)
  choose j a b hleft hlt hright himage hint using htransport
  have hab (k : κ) : Ioo (a k) (b k) ⊆ Ioo (D.arc (j k)).left (D.arc (j k)).right := by
    intro x hx
    exact ⟨(hleft k).trans_lt hx.1, hx.2.trans_le (hright k)⟩
  have htarget : ∀ z : Fin D.count,
      (∫ t in (D.arc z).left..(D.arc z).right, D.curvatureIntegrand C z t) =
        ∑ k : {k : κ // j k = z}, ∫ t in a k.val..b k.val, D.curvatureIntegrand C z t := by
    intro z
    let E : Set ℝ := Ioo (D.arc z).left (D.arc z).right ∩
      (D.arc z).curve ⁻¹' (boundaryEndpointSet B ∪ boundaryEndpointSet D)
    have hE : E.Finite := by
      apply Set.Finite.of_injOn (t := boundaryEndpointSet B ∪ boundaryEndpointSet D)
        (fun x hx => hx.2) ((D.injective z).mono inter_subset_left)
      exact (boundaryEndpointSet_finite B).union (boundaryEndpointSet_finite D)
    apply intervalIntegral_eq_sum_of_finite_cover _ (D.arc z).ordered.le
      (fun k : {k : κ // j k = z} => a k.val) (fun k => b k.val)
      (fun k => (hlt k.val).le) _ _ E hE _ (hD z)
    · intro k
      simpa only [k.property] using hab k.val
    · intro k k' hne
      apply Set.disjoint_left.mpr
      intro t ht ht'
      have hmem : (D.arc z).curve t ∈ (D.arc (j k.val)).curve '' Ioo (a k.val) (b k.val) := by
        rw [k.property]
        exact ⟨t, ht, rfl⟩
      have hmem' : (D.arc z).curve t ∈ (D.arc (j k'.val)).curve '' Ioo (a k'.val) (b k'.val) := by
        rw [k'.property]
        exact ⟨t, ht', rfl⟩
      rw [← himage k.val] at hmem
      rw [← himage k'.val] at hmem'
      exact Set.disjoint_left.mp (boundaryGap_images_disjoint B D
        (fun he => hne (Subtype.ext he))) hmem hmem'
    · intro t ht
      have hp : (D.arc z).curve t ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S := by
        rw [D.covers]
        exact mem_iUnion.mpr ⟨z, t, Ioo_subset_Icc_self ht.1, rfl⟩
      have hnot : (D.arc z).curve t ∉ boundaryEndpointSet B ∪ boundaryEndpointSet D :=
        fun h => ht.2 ⟨ht.1, h⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (B.covers ▸ hp)
      obtain ⟨s, hs, hst⟩ := mem_openArc_of_mem_fullArc_not_endpoint B i hi
        (fun he => hnot (Or.inl he))
      have hscut : s ∉ boundaryCutParameters B D i := by
        intro h
        rcases (mem_boundaryCutParameters B D i s).mp h with he | he | h
        · exact hs.1.ne' he
        · exact hs.2.ne he
        · exact hnot (Or.inr (hst ▸ h.2))
      obtain ⟨q, hq⟩ := FiniteGap.containing (boundaryCutParameters B D i)
        ((mem_boundaryCutParameters B D i _).mpr (Or.inl rfl))
        ((mem_boundaryCutParameters B D i _).mpr (Or.inr (Or.inl rfl))) hs hscut
      let k : κ := ⟨i, q⟩
      have hpimage : (D.arc z).curve t ∈ (D.arc (j k)).curve '' Ioo (a k) (b k) := by
        rw [← himage k]
        exact ⟨s, hq, hst⟩
      obtain ⟨x, hx, hxt⟩ := hpimage
      have hjz : j k = z := by
        by_contra hjz
        exact Set.disjoint_left.mp (D.disjoint hjz) ⟨x, hab k hx, hxt⟩ ⟨t, ht.1, rfl⟩
      apply mem_iUnion.mpr
      refine ⟨⟨k, hjz⟩, ?_⟩
      have hxt' : (D.arc z).curve x = (D.arc z).curve t := by simpa only [hjz] using hxt
      have hxin : x ∈ Ioo (D.arc z).left (D.arc z).right := by simpa only [hjz] using hab k hx
      exact (D.injective z hxin ht.1 hxt') ▸ hx
  calc
    B.curvatureIntegral C = ∑ k : κ,
        ∫ t in k.2.left..k.2.right, B.curvatureIntegrand C k.1 t := by
      unfold BoundaryPresentation.curvatureIntegral
      simp_rw [boundary_arc_integral_eq_sum_gaps B D C _ (hB _)]
      exact (Fintype.sum_sigma (fun k : κ => ∫ t in k.2.left..k.2.right, B.curvatureIntegrand C k.1 t)).symm
    _ = ∑ k : κ, ∫ t in a k..b k, D.curvatureIntegrand C (j k) t :=
      Finset.sum_congr rfl (fun k _ => hint k)
    _ = ∑ z : Fin D.count, ∑ k : {k : κ // j k = z},
        ∫ t in a k.val..b k.val, D.curvatureIntegrand C z t := by
      rw [← Fintype.sum_fiberwise j (fun k => ∫ t in a k..b k, D.curvatureIntegrand C (j k) t)]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro k _
      rw [k.property]
    _ = D.curvatureIntegral C := by
      unfold BoundaryPresentation.curvatureIntegral
      exact Finset.sum_congr rfl (fun z _ => (htarget z).symm)
end P202.GlobalGaussBonnet
end Round4BoundaryComparison


/-! Continuation: Round4RegionalLocal. -/
section Round4RegionalLocal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
open SmoothManifolds.OrientationData
open P202.MetricData P202.ConnectionData P202.CurvatureData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.SurfaceRegionsEuler P202Specs.PlanarRegionTopology
namespace P202.GlobalGaussBonnet

/-- Matching coordinates put the actual planar carrier inside the ambient
positive chart. -/
theorem regionalChartGeometry_carrier_subset
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r) :
    (D.region r).carrier ⊆ P202Specs.ChartRegionStokes.chartTarget G.ambientChart := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := (D.closure_coordinates r).symm ▸ hx
  change P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p) ∈ G.ambientChart.target
  have heq : P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p) =
      G.ambientChart (G.map ⟨p, G.closure_subset hp⟩) := by
    apply Subtype.ext
    simp only [P202Specs.ChartRegionStokes.modelPoint, coordinates, toPlane]
    exact (congrArg Subtype.val (G.restrictedChart_eq ⟨p, G.closure_subset hp⟩)).symm.trans
      (G.matching_coordinates ⟨p, G.closure_subset hp⟩)
  rw [heq]
  exact G.ambientChart.map_source (by rw [G.ambientChart_source]; trivial)

/-- Every actual component closure has genuine ambient regional geometry.
No orientation, nonemptiness or boundarylessness of the original surface is
required; nonemptiness belongs to the actual component closure. -/
theorem exists_regionalChartGeometry
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) :
    Nonempty (RegionalChartGeometry g D r) := by
  let A : Set (D.chart r).source := Subtype.val ⁻¹' regionClosure D r
  have hAimage : Subtype.val '' A = regionClosure D r := by
    ext p
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hp
      exact ⟨⟨p, D.closure_in_chart r hp⟩, hp, rfl⟩
  have hA : IsCompact A := Subtype.isCompact_iff.mpr (hAimage ▸ D.compact_closures r)
  have hne : A.Nonempty := by
    obtain ⟨p, hp⟩ := (D.connected_closures r).nonempty
    exact ⟨⟨p, D.closure_in_chart r hp⟩, hp⟩
  obtain ⟨W, hW, hAW, hWe, R, i, c, hc, hcs, hcval, U, hU, Q, h,
    d, hd, hds, f, j, hcoord, hm⟩ :=
    exists_chart_metric_extension_immersion S g (D.chart r) (D.chart_mem r) A hA hne
  obtain ⟨K, hK, _⟩ := P202.Geometry.LeviCivita.exists_unique h
  obtain ⟨H, hH, _⟩ := P202.Geometry.CurvatureAlgebra.tensor_exists_unique K
  exact ⟨{
    neighborhood := W
    neighborhood_open := hW
    closure_subset := hAimage ▸ hAW
    source_subset := hWe
    restriction := R
    inclusion := i
    restrictedChart := c
    restrictedChart_mem := hc
    restrictedChart_source := hcs
    restrictedChart_eq := hcval
    ambientDomain := U
    ambientDomain_open := hU
    ambientSurface := Q
    metric := h
    connection := K
    connection_LC := hK
    curvature := H
    curvature_represents := hH
    ambientChart := d
    ambientChart_mem := hd
    ambientChart_source := hds
    map := f
    immersion := j
    matching_coordinates := hcoord
    metric_preserving := hm
    orientation := globalChartOrientation (tangentStructure Q).fiberCoordinates d hd hds
    orientation_positive := globalChartOrientation_positive
      (tangentStructure Q).fiberCoordinates d hd hds (P202.VolumeData.cotangentBundle Q) }⟩

/-- The package contains actual Riemannian geometry, so Gaussian naturality
is proved from matching charts and Levi--Civita uniqueness. -/
theorem regionalChartGeometry_gaussianCurvature
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (p : G.neighborhood) :
    gaussianCurvature g T p.val = gaussianCurvature G.metric G.curvature (G.map p) := by
  let gR := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val G.inclusion
  obtain ⟨CR, hCR, _⟩ := P202.Geometry.LeviCivita.exists_unique gR
  obtain ⟨TR, hTR, _⟩ := P202.Geometry.CurvatureAlgebra.tensor_exists_unique CR
  have hp : p ∈ G.restrictedChart.source := by rw [G.restrictedChart_source]; trivial
  have hi := matchingChart_gaussianCurvature Subtype.val G.inclusion.smooth G.inclusion.differential
    G.inclusion.isDifferential gR g (fun _ _ _ => rfl)
    ⟨G.restrictedChart, G.restrictedChart_mem⟩ ⟨D.chart r, D.chart_mem r⟩
    (fun q _ => G.source_subset q.property)
    (fun q _ => congrArg Subtype.val (G.restrictedChart_eq q))
    CR C hCR hC TR T hTR hT p hp
  have hj := matchingChart_gaussianCurvature G.map G.immersion.smooth G.immersion.differential
    G.immersion.isDifferential gR G.metric G.metric_preserving
    ⟨G.restrictedChart, G.restrictedChart_mem⟩ ⟨G.ambientChart, G.ambientChart_mem⟩
    (fun q _ => by rw [G.ambientChart_source]; trivial)
    (fun q _ => G.matching_coordinates q)
    CR G.connection hCR G.connection_LC TR G.curvature hTR G.curvature_represents p hp
  exact hi.symm.trans hj

/-- The original intrinsic bulk integral agrees with that of every actual
regional ambient package. No Gaussian comparison is a package assumption. -/
theorem regionalChartGeometry_curvatureIntegral
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ) :
    (letI : MeasurableSpace M := borel M;
      ∫ p in regionClosure D r, gaussianCurvature g T p ∂μ) =
      P202Specs.LocalGaussBonnet.curvatureIntegral G.metric G.curvature
        G.ambientChart G.ambientChart_mem (D.region r) := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact extension_local_curvatureIntegral_eq_intrinsic_of_isCompact
    S g C hC T hT μ hμ (D.chart r) (D.chart_mem r)
    G.neighborhood G.source_subset G.restriction G.inclusion
    G.restrictedChart G.restrictedChart_mem G.restrictedChart_source G.restrictedChart_eq
    G.ambientSurface G.metric G.curvature G.ambientChart G.ambientChart_mem
    G.map G.immersion (fun _ => by rw [G.ambientChart_source]; trivial)
    G.matching_coordinates G.metric_preserving
    (regionalChartGeometry_gaussianCurvature G C hC T hT)
    (D.region r) (regionClosure D r) isClosed_closure.measurableSet
    (D.compact_closures r) G.closure_subset (D.closure_coordinates r)

/-- Actual compact component closures have integrable original Gaussian
curvature for the canonical area measure. -/
theorem region_integrableOn_gaussianCurvature
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (D : RegionDecomposition S) (r : Fin D.regionCount) :
    letI : MeasurableSpace M := borel M
    IntegrableOn (gaussianCurvature g T) (regionClosure D r) μ := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact integrableOn_gaussianCurvature_of_isCompact g C hC T hT μ hμ
    (regionClosure D r) (D.compact_closures r) isClosed_closure.measurableSet

/-- Full local formula for every actual regional package and every smooth
presentation with induced component signs. The bulk integral uses the original
area measure; all remaining terms use the package's actual ambient geometry. -/
theorem regionalChartGeometry_local_formula
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ) :
    (∃ s, IsInducedBoundaryOrientation (D.region r) s) ∧
      Nonempty (∀ b, P202Specs.PlaneTurning.ArcPresentation ((D.region r).curve b)) ∧
      ∀ (A : ∀ b, P202Specs.PlaneTurning.ArcPresentation ((D.region r).curve b))
        (s : Fin (D.region r).boundaryCount → ℝ),
        IsInducedBoundaryOrientation (D.region r) s →
        IntegrableOn (P202Specs.LocalGaussBonnet.curvatureIntegrand G.metric G.curvature
          G.ambientChart G.ambientChart_mem) (D.region r).carrier ∧
        (∀ b k, IntervalIntegrable
          (P202Specs.LocalGaussBonnet.geodesicIntegrand G.metric G.connection G.orientation
            G.ambientChart G.ambientChart_mem (A b) k) volume 0 1) ∧
        (∀ b k, 0 < P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
            G.ambientChart G.ambientChart_mem (A b) (s b) k ∧
          P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
            G.ambientChart G.ambientChart_mem (A b) (s b) k < 2 * Real.pi) ∧
        (∀ b k, P202Specs.MetricBoundaryTurning.IsOccupiedSectorAngle
          G.metric G.orientation G.ambientChart G.ambientChart_mem (D.region r) b (A b) (s b) k
          (P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
            G.ambientChart G.ambientChart_mem (A b) (s b) k)) ∧
        ∃ hD : P202Specs.EulerPoincare.HomologyFiniteType ℚ (D.region r).carrier,
          (letI : MeasurableSpace M := borel M;
            ∫ p in regionClosure D r, gaussianCurvature g T p ∂μ) +
            P202Specs.LocalGaussBonnet.geodesicIntegral G.metric G.connection G.orientation
              G.ambientChart G.ambientChart_mem (D.region r) A s +
            P202Specs.LocalGaussBonnet.exteriorAngleSum G.metric G.orientation
              G.ambientChart G.ambientChart_mem (D.region r) A s =
              2 * Real.pi * (P202Specs.EulerPoincare.topologicalEuler (D.region r).carrier hD : ℝ) := by
  obtain ⟨hne, hlocal⟩ := P202.LocalGaussBonnet.localGaussBonnet
    G.ambientSurface G.metric G.connection G.connection_LC G.curvature G.curvature_represents
    G.orientation G.ambientChart G.ambientChart_mem G.orientation_positive
    (D.region r) (regionalChartGeometry_carrier_subset G)
  refine ⟨(P202.PlanarRegionTopology.regionCollarAndOrientation (D.region r)).2, hne, ?_⟩
  intro A s hs
  obtain ⟨hcurv, hint, hbounds, hsector, ⟨hD, hformula⟩, _⟩ := hlocal A s hs
  refine ⟨hcurv, hint, hbounds, hsector, hD, ?_⟩
  rw [regionalChartGeometry_curvatureIntegral G C hC T hT μ hμ]
  exact hformula

end P202.GlobalGaussBonnet
end Round4RegionalLocal


/-! Continuation: Round4RegionalGeometryAssembly. -/
section Round4RegionalGeometryAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurvatureData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.SurfaceRegionsEuler P202Specs.EulerPoincare
namespace P202.GlobalGaussBonnet

/-- Actual regional geometry discharges all local formulas and bulk-area
premises in the Euler assembly. The two remaining hypotheses are precisely
the boundary and corner gluing obligations, not additional source assumptions. -/
theorem assemble_regionalChartGeometry
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (D : RegionDecomposition S) (B : BoundaryPresentation g)
    (G : ∀ j, RegionalChartGeometry g D j)
    (A : ∀ j i, P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (s : ∀ j, Fin (D.region j).boundaryCount → ℝ)
    (hs : ∀ j, P202Specs.PlanarRegionTopology.IsInducedBoundaryOrientation (D.region j) (s j))
    (hboundary :
      (∑ j, P202Specs.LocalGaussBonnet.geodesicIntegral
        (G j).metric (G j).connection (G j).orientation
        (G j).ambientChart (G j).ambientChart_mem (D.region j) (A j) (s j)) =
          B.curvatureIntegral C)
    (hcorners :
      (∑ j, P202Specs.LocalGaussBonnet.exteriorAngleSum
        (G j).metric (G j).orientation (G j).ambientChart (G j).ambientChart_mem
        (D.region j) (A j) (s j)) =
          2 * Real.pi * ((D.graph.edgeCount : ℝ) - (D.graph.vertexCount : ℝ))) :
    (letI : MeasurableSpace M := borel M;
      Integrable (gaussianCurvature g T) μ) ∧
      ∃ hS : HomologyFiniteType ℚ M,
        totalCurvature g T μ + B.curvatureIntegral C =
          2 * Real.pi * (topologicalEuler M hS : ℝ) := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have hreg (j : Fin D.regionCount) :=
    (regionalChartGeometry_local_formula (G j) C hC T hT μ hμ).2.2 (A j) (s j) (hs j)
  let hP (j : Fin D.regionCount) := (hreg j).2.2.2.2.choose
  apply assemble_actual_region_formulas g C T μ hμ D B
    (fun j => ∫ p in regionClosure D j, gaussianCurvature g T p ∂μ)
    (fun j => P202Specs.LocalGaussBonnet.geodesicIntegral
      (G j).metric (G j).connection (G j).orientation
      (G j).ambientChart (G j).ambientChart_mem (D.region j) (A j) (s j))
    (fun j => P202Specs.LocalGaussBonnet.exteriorAngleSum
      (G j).metric (G j).orientation (G j).ambientChart (G j).ambientChart_mem
      (D.region j) (A j) (s j)) hP
  · intro j
    exact (hreg j).2.2.2.2.choose_spec
  · intro j
    exact integrableOn_gaussianCurvature_of_isCompact g C hC T hT μ hμ
      (regionClosure D j) (D.compact_closures j) isClosed_closure.measurableSet
  · intro j
    rfl
  · exact hboundary
  · exact hcorners

end P202.GlobalGaussBonnet
end Round4RegionalGeometryAssembly

section Round4BoundaryComparisonComplete
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData
open P202Specs.GlobalGaussBonnet
namespace P202.GlobalGaussBonnet
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Every genuine finite boundary presentation gives the same actual
curvature integral. All geometric and analytic premises are discharged. -/
theorem boundary_curvatureIntegral_eq {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (C : Connection (tangentBundle S)) :
    B.curvatureIntegral C = D.curvatureIntegral C := by
  exact boundary_curvatureIntegral_eq_of_integrable B D C
    (boundary_curvatureIntegrand_integrable g C B)
    (boundary_curvatureIntegrand_integrable g C D)

end P202.GlobalGaussBonnet
end Round4BoundaryComparisonComplete
