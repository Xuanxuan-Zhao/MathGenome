import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology

/-! The canonical tangent bundle on the intrinsic derivation fibers.
The tangent charts construct its topology and maximal smooth atlas, and the
coordinate calculus proves smooth vector operations and the tangent functor. -/
namespace SmoothManifolds.TangentBundle
open ModelData AtlasData MapData TangentData DifferentialData ProductData BoundaryData
open TangentBundleData Set Filter
open scoped Topology
universe u v

abbrev totalSpace := @TangentBundleData.TotalSpace
abbrev projection := @TangentBundleData.projection
abbrev zeroSection := @TangentBundleData.zeroSection
abbrev map := @TangentBundleData.totalMap
abbrev CoordinateSystem := @TangentBundleData.FiberCoordinates
abbrev Structure := @TangentBundleData.TangentBundleStructure
abbrev SmoothScalar := @TangentBundleData.SmoothScalar

/-- Realizing all intrinsic fibers in all base charts uses the previously proved
coordinate model, without equipping the base with any further certificate. -/
theorem fiberCoordinates_exists :
    Specs.SmoothManifolds.Tangent.Bundle.fiberCoordinates_existsType.{u} := by
  intro n a M _ S
  classical
  have h (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
      (p : M) (hp : p ∈ e.source) :
      ∃ E : TangentSpace S p ≃ₗ[ℝ] Euclidean n, IsChartCoordinates S p e E := by
    obtain ⟨xs, b, E, hxs, hE, _⟩ := coordinate_tangent_model S p e he hp
    exact ⟨E, xs, hxs, hE⟩
  exact ⟨{
    equiv := fun e he p hp => Classical.choose (h e he p hp)
    isCoordinates := fun e he p hp => Classical.choose_spec (h e he p hp) }⟩

/-- Intrinsic coordinate linear equivalences are unique, since all coordinate
germs are fixed. Thus choices in their existence do not affect tangent charts. -/
theorem chartCoordinates_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {p : M}
    {e : ModelChart n a M} {E F : TangentSpace S p ≃ₗ[ℝ] Euclidean n}
    (hE : IsChartCoordinates S p e E) (hF : IsChartCoordinates S p e F) : E = F := by
  obtain ⟨xs, hxs, hE⟩ := hE
  obtain ⟨ys, hys, hF⟩ := hF
  ext z i
  rw [hE, hF]
  congr 1
  exact Subtype.ext ((hxs i).trans (hys i).symm)

theorem transition_jacobian :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_transition_jacobianType.{u} := by
  intro n a M _ S K e d he hd p hp hpd U F hU hpU hF hrep v
  have hid : IsSmoothMap S S id :=
    manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1
  exact differential_jacobian S S id hid p LinearMap.id (differential_id S p)
    e d he hd hp hpd (K.equiv e he p hp) (K.equiv d hd p hpd)
    (K.isCoordinates e he p hp) (K.isCoordinates d hd p hpd)
    U F hU hpU hF hrep v

/-- Derivatives of a single ambient transition give smooth matrix coefficients
on an ambient neighborhood, including when its center is a boundary point. -/
theorem transition_smooth :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_transition_smoothType.{u} := by
  intro n a M _ S K e d he hd p hp hpd
  have hc := S.smoothStructure.property.1.2 e he d hd
  have hpt : e p ∈ (e.symm.trans d).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    exact ⟨e.map_source hp, by simpa only [e.left_inv hp] using hpd⟩
  obtain ⟨U, hU, hpU, F, hF, heq⟩ := hc.1 (e p) hpt
  refine ⟨U, hU, hpU, fderiv ℝ F, hF.fderiv_of_isOpen hU (by simp), ?_⟩
  intro q hq hqd hqU v
  have hrep : (fun y => F (e y).val) =ᶠ[𝓝 q] (fun y => (d y).val) := by
    filter_upwards [e.open_source.mem_nhds hq, d.open_source.mem_nhds hqd,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hq)).preimage_mem_nhds
        (hU.mem_nhds hqU)] with y hye hyd hyU
    have hyt : e y ∈ (e.symm.trans d).source := by
      simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
      exact ⟨e.map_source hye, by simpa only [e.left_inv hye] using hyd⟩
    simpa only [OpenPartialHomeomorph.trans_apply, e.left_inv hye] using heq (e y) hyt hyU
  have h := transition_jacobian S K e d he hd q hq hqd U F hU hqU hF hrep
    ((K.equiv e he q hq).symm v)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- Smoothness of the ambient tangent lift is the analytic fact used for both
chart transitions and tangent maps. Its domain is open in the full product. -/
theorem ambientLift_contDiffOn {n m : ℕ} {U : Set (Euclidean n)}
    (hU : IsOpen U) {F : Euclidean n → Euclidean m}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Euclidean n × Euclidean n => (F z.1, fderiv ℝ F z.1 z.2))
      (U ×ˢ univ) := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  exact (hF.comp contDiffOn_fst (fun _ hz => hz.1)).prodMk
    ((hd.comp contDiffOn_fst (fun _ hz => hz.1)).clm_apply contDiffOn_snd)

theorem operations_coordinates :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_operations_coordinatesType.{u} := by
  intro n a M _ S K
  refine ⟨contDiff_fst.prodMk (contDiff_snd.fst.add contDiff_snd.snd),
    contDiff_snd.fst.prodMk (contDiff_fst.smul contDiff_snd.snd), ?_⟩
  intro e he p hp v w s
  exact ⟨map_add _ v w, map_smul _ s v⟩

theorem map_covers :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_totalMap_coversType.{u} := by
  intro n m a b M N _ _ S T f L
  rfl

theorem map_id :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_totalMap_idType.{u} := by
  intro n a M _ S L hL
  have hid : IsSmoothMap S S id :=
    manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1
  funext z
  rcases z with ⟨p, v⟩
  have h : L p = LinearMap.id :=
    (differential_exists S S id hid p).unique (hL p) (differential_id S p)
  change (⟨p, L p v⟩ : TotalSpace S) = ⟨p, v⟩
  rw [h]
  rfl

theorem map_comp :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_totalMap_compType.{u} := by
  intro n m k a b c M N Q _ _ _ S T R f g hf hg L K H hL hK hH
  have hfg : IsSmoothMap S R (g ∘ f) :=
    manifoldContDiff_comp (⊤ : ℕ∞) S.smoothStructure.val T.smoothStructure.val
      R.smoothStructure.val T.smoothStructure.property.1.1 f g hf hg
  funext z
  rcases z with ⟨p, v⟩
  have h : H p = (K (f p)).comp (L p) :=
    (differential_exists S R (g ∘ f) hfg p).unique (hH p)
      (differential_comp S T R f g hf hg p (L p) (K (f p)) (hL p) (hK (f p)))
  change (⟨g (f p), H p v⟩ : TotalSpace R) = ⟨g (f p), K (f p) (L p v)⟩
  rw [h]
  rfl

theorem empty : Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_emptyType.{u} := by
  intro n a M _ _ S
  exact ⟨fun z => isEmptyElim z.1⟩

/-- The prescribed charts belong to the maximal atlas. This follows from
maximality and symmetry of compatibility, not from an extra certificate. -/
theorem chart_mem {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) :
    letI := B.topology
    B.chart e he ∈ B.manifold.smoothStructure.val := by
  letI := B.topology
  let A := B.manifold.smoothStructure.val
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A := B.manifold.smoothStructure.property.1
  have hmax : maximalExtension (⊤ : ℕ∞) A = A :=
    B.manifold.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas hA)
      (subset_maximalExtension hA)
  change B.chart e he ∈ A
  rw [← hmax]
  intro d hd
  have hd' := hd
  change d ∈ B.manifold.smoothStructure.val at hd'
  rw [B.maximalAtlas] at hd'
  exact contDiffCompatible_symm (hd' (B.chart e he) ⟨e, he, rfl⟩)

/-- Decode a tangent chart back into its base and vector coordinates. -/
theorem chart_decode {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (z : TotalSpace S) (hz : z.1 ∈ e.source) :
    B.productCoordinates.homeomorph.symm (B.chart e he z) =
      (e z.1, ⟨B.fiberCoordinates.equiv e he z.1 hz z.2, mem_univ _⟩) := by
  apply B.productCoordinates.homeomorph.injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (B.chart_apply e he z hz)

theorem projection_smooth :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_projection_smoothType.{u} := by
  intro n a M _ S B
  letI := B.topology
  intro z
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 z.1
  let t := B.chart e he
  have hz : z ∈ t.source := by simpa only [t, B.chart_source, TangentBundleData.projection, TangentBundleData.zeroSection, mem_preimage] using hp
  have hπ : ContinuousAt (projection S) z := by
    have htarget : (B.productCoordinates.homeomorph.symm (t z)).1 ∈ e.target := by
      rw [chart_decode S B e he z hp]
      exact e.map_source hp
    have hdec : ContinuousAt
        (fun y : TotalSpace S => (B.productCoordinates.homeomorph.symm (t y)).1) z :=
      continuous_fst.continuousAt.comp
        (B.productCoordinates.homeomorph.symm.continuous.continuousAt.comp (t.continuousAt hz))
    have hc : ContinuousAt (fun y : TotalSpace S =>
        e.symm ((B.productCoordinates.homeomorph.symm (t y)).1)) z :=
      (e.symm.continuousAt htarget).comp (f := fun y : TotalSpace S =>
        (B.productCoordinates.homeomorph.symm (t y)).1) hdec
    apply hc.congr
    filter_upwards [t.open_source.mem_nhds hz] with y hy
    have hyp : y.1 ∈ e.source := by simpa only [t, B.chart_source, TangentBundleData.projection, TangentBundleData.zeroSection, mem_preimage] using hy
    change e.symm ((B.productCoordinates.homeomorph.symm (t y)).1) = y.1
    rw [chart_decode S B e he y hyp]
    exact e.left_inv hyp
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    B.manifold.smoothStructure.property.1 S.smoothStructure.property.1 (projection S) z).mpr
  refine ⟨hπ, t, chart_mem S B e he, e, he, hz, hp, ?_⟩
  let L := (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp
    B.productCoordinates.linearEquiv.symm.toContinuousLinearMap
  refine ⟨univ, isOpen_univ, mem_univ _, L, L.contDiff.contDiffOn, ?_⟩
  filter_upwards [t.open_source.mem_nhds hz] with y hy
  have hyp : y.1 ∈ e.source := by simpa only [t, B.chart_source, TangentBundleData.projection, TangentBundleData.zeroSection, mem_preimage] using hy
  change (B.productCoordinates.linearEquiv.symm (t y).val).1 = (e y.1).val
  rw [B.chart_apply e he y hyp, ContinuousLinearEquiv.symm_apply_apply]

theorem zero_smooth :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_zero_smoothType.{u} := by
  intro n a M _ S B
  letI := B.topology
  intro p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let t := B.chart e he
  let g : M → ModelSpace (n+n) a := fun q =>
    B.productCoordinates.homeomorph (e q, ⟨0, mem_univ _⟩)
  have hg (q : M) (hq : q ∈ e.source) : t (zeroSection S q) = g q := by
    apply Subtype.ext
    change ((B.chart e he) (zeroSection S q)).val =
      B.productCoordinates.linearEquiv ((e q).val, 0)
    have hh := B.chart_apply e he (zeroSection S q) hq
    change ((B.chart e he) (zeroSection S q)).val =
      B.productCoordinates.linearEquiv ((e q).val, B.fiberCoordinates.equiv e he q hq 0) at hh
    simpa only [map_zero] using hh
  have hzt : zeroSection S p ∈ t.source := by
    simpa only [t, B.chart_source, TangentBundleData.projection, TangentBundleData.zeroSection, mem_preimage] using hp
  have hgt : g p ∈ t.target := hg p hp ▸ t.map_source hzt
  have hc : ContinuousAt (zeroSection S) p := by
    have hc := (t.symm.continuousAt hgt).comp
      (B.productCoordinates.homeomorph.continuous.continuousAt.comp
        ((e.continuousAt hp).prodMk continuousAt_const))
    apply hc.congr
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    change t.symm (g q) = zeroSection S q
    rw [← hg q hq]
    apply t.left_inv
    simpa only [t, B.chart_source, TangentBundleData.projection, TangentBundleData.zeroSection, mem_preimage] using hq
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 B.manifold.smoothStructure.property.1 (zeroSection S) p).mpr
  refine ⟨hc, e, he, t, chart_mem S B e he, hp, hzt, ?_⟩
  let F : Euclidean n → Euclidean (n+n) :=
    fun x => B.productCoordinates.linearEquiv (x, 0)
  refine ⟨univ, isOpen_univ, mem_univ _, F,
    (B.productCoordinates.linearEquiv.contDiff.comp
      (contDiff_id.prodMk contDiff_const)).contDiffOn, ?_⟩
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (congrArg Subtype.val (hg q hq)).symm

theorem locallyTrivial :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_locallyTrivialType.{u} := by
  intro n a M _ S B e he
  letI := B.topology
  let t := B.chart e he
  have hs : (projection S ⁻¹' e.source) = t.source := (B.chart_source e he).symm
  have ht (y : ModelSpace (n+n) a) : y ∈ t.target ↔
      B.productCoordinates.homeomorph.symm y ∈ e.target ×ˢ univ := by
    rw [B.chart_target]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [Homeomorph.symm_apply_apply] using hq
    · intro hy
      exact ⟨_, hy, B.productCoordinates.homeomorph.apply_symm_apply y⟩
  let h1 := Homeomorph.setCongr hs
  let h2 := B.productCoordinates.homeomorph.symm.subtype ht
  let h3 := Homeomorph.Set.prod e.target (univ : Set (ModelSpace n .euclidean))
  let hv : (univ : Set (ModelSpace n .euclidean)) ≃ₜ Euclidean n :=
    (Homeomorph.Set.univ (ModelSpace n .euclidean)).trans (Homeomorph.Set.univ (Euclidean n))
  let h := h1.trans (t.toHomeomorphSourceTarget.trans
    (h2.trans (h3.trans (e.toHomeomorphSourceTarget.symm.prodCongr hv))))
  refine ⟨h, ?_⟩
  intro z
  constructor
  · change e.symm ((B.productCoordinates.homeomorph.symm (t z.val)).1) = z.val.1
    rw [chart_decode S B e he z.val z.property]
    exact e.left_inv z.property
  · change (B.productCoordinates.homeomorph.symm (t z.val)).2.val = _
    rw [chart_decode S B e he z.val z.property]

/-- Every allowed rearrangement of the product coordinates preserves its face.
This argument includes the empty face in dimension zero. -/
theorem productCoordinates_face {n m : ℕ} {a : ModelKind}
    (C : ProductCoordinates n a m .euclidean a) (x : Euclidean n) (v : Euclidean m)
    (hx : x ∈ modelSet n a) :
    C.linearEquiv (x, v) ∈ modelFace (n+m) a ↔ x ∈ modelFace n a := by
  have hpre : C.linearEquiv ⁻¹' modelSet (n+m) a = modelSet n a ×ˢ univ := by
    ext z
    exact C.mem_model z
  have hi := congrArg (fun s : Set (Euclidean n × Euclidean m) => (x, v) ∈ s)
    (C.linearEquiv.toHomeomorph.preimage_interior (modelSet (n+m) a))
  change (C.linearEquiv (x, v) ∈ interior (modelSet (n+m) a)) =
    ((x, v) ∈ interior (C.linearEquiv ⁻¹' modelSet (n+m) a)) at hi
  rw [hpre, interior_prod_eq, interior_univ] at hi
  have hc : C.linearEquiv (x, v) ∈ modelSet (n+m) a := (C.mem_model _).mpr ⟨hx, mem_univ _⟩
  rw [mem_modelFace_iff_not_mem_interior ⟨_, hc⟩, mem_modelFace_iff_not_mem_interior ⟨x, hx⟩]
  simpa only [mem_preimage, mem_prod, mem_univ, and_true] using not_congr (iff_of_eq hi)

theorem boundary : Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_boundaryType.{u} := by
  intro n a M _ S B
  letI := B.topology
  ext z
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 z.1
  have hz : z ∈ (B.chart e he).source := by simpa only [B.chart_source, TangentBundleData.projection, mem_preimage] using hp
  rw [intrinsicBoundary_iff_chart B.manifold (B.chart e he) (chart_mem S B e he) z hz]
  change ((B.chart e he) z).val ∈ modelFace (n+n) a ↔ z.1 ∈ intrinsicBoundary S
  rw [intrinsicBoundary_iff_chart S e he z.1 hp, B.chart_apply e he z hp]
  exact productCoordinates_face B.productCoordinates (e z.1).val
    (B.fiberCoordinates.equiv e he z.1 hp z.2) (e z.1).property

theorem zeroDimension :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_zeroDimensionType.{u} := by
  intro a M _ S B
  letI := B.topology
  letI := _root_.SmoothManifolds.TopologicalManifold.toChartedSpace S.topologicalManifold
  letI : DiscreteTopology M := ChartedSpace.discreteTopology (ModelSpace 0 a) M
  letI := _root_.SmoothManifolds.TopologicalManifold.toChartedSpace B.manifold.topologicalManifold
  letI : DiscreteTopology (TotalSpace S) := ChartedSpace.discreteTopology (ModelSpace 0 a) _
  refine ⟨inferInstance, ?_⟩
  let h : TotalSpace S ≃ M := {
    toFun := projection S
    invFun := zeroSection S
    left_inv := fun z => by
      rcases z with ⟨p, v⟩
      haveI := tangent_zero S p
      exact congrArg (Sigma.mk p) (Subsingleton.elim _ _)
    right_inv := fun _ => rfl }
  exact ⟨⟨h, continuous_of_discreteTopology, continuous_of_discreteTopology⟩, rfl⟩

/-- The fiber component of a tangent chart, globally defined for germ arguments. -/
def chartFiber {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (z : TotalSpace S) :
    Euclidean n := (B.productCoordinates.linearEquiv.symm ((B.chart e he) z).val).2

theorem chartFiber_eq {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (z : TotalSpace S) (hz : z.1 ∈ e.source) :
    chartFiber B e he z = B.fiberCoordinates.equiv e he z.1 hz z.2 := by
  unfold chartFiber
  rw [B.chart_apply e he z hz, ContinuousLinearEquiv.symm_apply_apply]

/-- Postcomposition of an ambient representative by a continuous linear map. -/
theorem extension_linear {X : Type*} [TopologicalSpace X] {k n m : ℕ}
    {ι : X → Euclidean k} {f : X → Euclidean n} {x : X}
    (h : LocalCoordinateExtension (⊤ : ℕ∞) ι f x)
    (L : Euclidean n →L[ℝ] Euclidean m) :
    LocalCoordinateExtension (⊤ : ℕ∞) ι (fun y => L (f y)) x := by
  obtain ⟨U, hU, hx, F, hF, he⟩ := h
  exact ⟨U, hU, hx, fun z => L (F z), L.contDiff.comp_contDiffOn hF,
    he.fun_comp L⟩

theorem chartFiber_smoothAt {n k : ℕ} {a c : ModelKind} {M : Type u} {Q : Type v}
    [TopologicalSpace M] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (R : SmoothManifold k c Q) (f : Q → TotalSpace S) (x : Q)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hx : (f x).1 ∈ e.source) :
    letI := B.topology
    ManifoldContDiffAt (⊤ : ℕ∞) R.smoothStructure.val B.manifold.smoothStructure.val f x →
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val
      (fun y => chartFiber B e he (f y)) x := by
  letI := B.topology
  intro hf
  let L := (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
    B.productCoordinates.linearEquiv.symm.toContinuousLinearMap
  have ht : f x ∈ (B.chart e he).source := by
    simpa only [B.chart_source, TangentBundleData.projection, mem_preimage] using hx
  refine ⟨L.continuous.continuousAt.comp
    (continuous_subtype_val.continuousAt.comp (((B.chart e he).continuousAt ht).comp hf.1)), ?_⟩
  intro d hd hxd
  exact extension_linear (hf.2 d hd (B.chart e he) (chart_mem S B e he) hxd ht) L

/-- Reconstruct a smooth lift from its base and a local smooth fiber component.
Continuity of the lift is proved here using the inverse of its tangent chart. -/
theorem lift_smoothAt_of_coeff {n k : ℕ} {a c : ModelKind} {M : Type u} {Q : Type v}
    [TopologicalSpace M] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (R : SmoothManifold k c Q) (f : Q → TotalSpace S) (x : Q)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hx : (f x).1 ∈ e.source) (w : Q → Euclidean n)
    (hp : ManifoldContDiffAt (⊤ : ℕ∞) R.smoothStructure.val S.smoothStructure.val
      (fun y => (f y).1) x)
    (hw : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val w x)
    (heq : ∀ᶠ y in 𝓝 x, ∃ hy : (f y).1 ∈ e.source,
      w y = B.fiberCoordinates.equiv e he (f y).1 hy (f y).2) :
    letI := B.topology
    ManifoldContDiffAt (⊤ : ℕ∞) R.smoothStructure.val B.manifold.smoothStructure.val f x := by
  letI := B.topology
  let t := B.chart e he
  let g : Q → ModelSpace (n+n) a := fun y =>
    B.productCoordinates.homeomorph (e (f y).1, ⟨w y, mem_univ _⟩)
  have htg : ∀ᶠ y in 𝓝 x, t (f y) = g y := by
    filter_upwards [heq] with y hy
    obtain ⟨hy, hwy⟩ := hy
    apply Subtype.ext
    change (t (f y)).val = B.productCoordinates.linearEquiv ((e (f y).1).val, w y)
    rw [hwy, B.chart_apply e he (f y) hy]
  have ht : f x ∈ t.source := by
    simpa only [t, B.chart_source, TangentBundleData.projection, mem_preimage] using hx
  have htg0 : t (f x) = g x := (show (fun y => t (f y)) =ᶠ[𝓝 x] g from htg).eq_of_nhds
  have hgt : g x ∈ t.target := htg0 ▸ t.map_source ht
  have hgc : ContinuousAt g x :=
    B.productCoordinates.homeomorph.continuous.continuousAt.comp
      (((e.continuousAt hx).comp (f := fun y => (f y).1) hp.1).prodMk
        (hw.1.codRestrict (fun y => mem_univ (w y))))
  have hfc : ContinuousAt f x := by
    apply ((t.symm.continuousAt hgt).comp hgc).congr
    filter_upwards [htg, heq] with y hy hye
    change t.symm (g y) = f y
    rw [← hy]
    apply t.left_inv
    simpa only [t, B.chart_source, TangentBundleData.projection, mem_preimage] using hye.choose
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    R.smoothStructure.property.1 B.manifold.smoothStructure.property.1 f x).mpr
  obtain ⟨d, hd, hxd⟩ := R.smoothStructure.property.1.1 x
  refine ⟨hfc, d, hd, t, chart_mem S B e he, hxd, ht, ?_⟩
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hp.2 d hd e he hxd hx
  obtain ⟨V, hV, hxV, G, hG, hGeq⟩ := hw.2 d hd hxd
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    fun z => B.productCoordinates.linearEquiv (F z, G z),
    B.productCoordinates.linearEquiv.contDiff.comp_contDiffOn
      ((hF.mono inter_subset_left).prodMk (hG.mono inter_subset_right)), ?_⟩
  filter_upwards [hFeq, hGeq, htg] with y hyF hyG hyt
  change B.productCoordinates.linearEquiv (F (d y).val, G (d y).val) = (t (f y)).val
  rw [hyF, hyG, hyt]
  rfl

theorem lift_smooth_iff :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_lift_smooth_iffType.{u,v} := by
  intro n k a c M Q _ _ S B R f
  letI := B.topology
  constructor
  · intro hf
    have hp := manifoldContDiff_comp (⊤ : ℕ∞) R.smoothStructure.val
      B.manifold.smoothStructure.val S.smoothStructure.val
      B.manifold.smoothStructure.property.1.1 f (projection S) hf (projection_smooth S B)
    refine ⟨hp, ?_⟩
    intro x e he hx
    let V := (fun y => (f y).1) ⁻¹' e.source
    have hV : IsOpen V := e.open_source.preimage
      (continuous_iff_continuousAt.mpr fun y => (hp y).1)
    refine ⟨V, hV, hx, fun y hy => hy, fun y => chartFiber B e he (f y), ?_,
      chartFiber_smoothAt S B R f x e he hx (hf x)⟩
    intro y hy
    exact chartFiber_eq S B e he (f y) hy
  · rintro ⟨hp, hw⟩ x
    obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 (f x).1
    obtain ⟨V, hV, hxV, hVe, w, hweq, hws⟩ := hw x e he hx
    apply lift_smoothAt_of_coeff S B R f x e he hx w (hp x) hws
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact ⟨hVe y hy, hweq y hy⟩

theorem euclidean_add_smoothAt {k n : ℕ} {c : ModelKind} {Q : Type*}
    [TopologicalSpace Q] (R : SmoothManifold k c Q) (v w : Q → Euclidean n) (x : Q)
    (hv : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val v x)
    (hw : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val w x) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val (fun y => v y + w y) x := by
  refine ⟨hv.1.add hw.1, ?_⟩
  intro d hd hx
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := hv.2 d hd hx
  obtain ⟨V, hV, hxV, G, hG, heG⟩ := hw.2 d hd hx
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun z => F z + G z,
    (hF.mono inter_subset_left).add (hG.mono inter_subset_right), ?_⟩
  filter_upwards [heF, heG] with y hyF hyG
  rw [hyF, hyG]

theorem euclidean_smul_smoothAt {k n : ℕ} {c : ModelKind} {Q : Type*}
    [TopologicalSpace Q] (R : SmoothManifold k c Q) (v : Q → Euclidean n)
    (s : Q → ℝ) (x : Q)
    (hv : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val v x)
    (hs : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val
      (fun y => fun _ : Fin 1 => s y) x) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val (fun y => s y • v y) x := by
  refine ⟨((continuous_apply 0).continuousAt.comp hs.1).smul hv.1, ?_⟩
  intro d hd hx
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := hv.2 d hd hx
  obtain ⟨V, hV, hxV, G, hG, heG⟩ := hs.2 d hd hx
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun z => G z 0 • F z,
    ((contDiffOn_pi.mp (hG.mono inter_subset_right)) 0).smul (hF.mono inter_subset_left), ?_⟩
  filter_upwards [heF, heG] with y hyF hyG
  rw [hyF, hyG]

theorem operations_smooth :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_operations_smoothType.{u,v} := by
  intro n k a c M Q _ _ S B R p v w s
  letI := B.topology
  constructor
  · intro hv hw x
    have hp := manifoldContDiff_comp (⊤ : ℕ∞) R.smoothStructure.val
      B.manifold.smoothStructure.val S.smoothStructure.val
      B.manifold.smoothStructure.property.1.1 (fun y => ⟨p y, v y⟩) (projection S)
      hv (projection_smooth S B)
    obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 (p x)
    let v' := fun y => chartFiber B e he ⟨p y, v y⟩
    let w' := fun y => chartFiber B e he ⟨p y, w y⟩
    have hv' := chartFiber_smoothAt S B R (fun y => ⟨p y, v y⟩) x e he hx (hv x)
    have hw' := chartFiber_smoothAt S B R (fun y => ⟨p y, w y⟩) x e he hx (hw x)
    apply lift_smoothAt_of_coeff S B R (fun y => ⟨p y, v y + w y⟩) x e he hx
      (fun y => v' y + w' y) (hp x) (euclidean_add_smoothAt R v' w' x hv' hw')
    filter_upwards [(hp x).1.preimage_mem_nhds (e.open_source.mem_nhds hx)] with y hy
    change p y ∈ e.source at hy
    refine ⟨hy, ?_⟩
    change chartFiber B e he ⟨p y, v y⟩ + chartFiber B e he ⟨p y, w y⟩ = _
    simp only [chartFiber_eq S B e he ⟨p y, v y⟩ hy,
      chartFiber_eq S B e he ⟨p y, w y⟩ hy, map_add]
  · intro hv hs x
    have hp := manifoldContDiff_comp (⊤ : ℕ∞) R.smoothStructure.val
      B.manifold.smoothStructure.val S.smoothStructure.val
      B.manifold.smoothStructure.property.1.1 (fun y => ⟨p y, v y⟩) (projection S)
      hv (projection_smooth S B)
    obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 (p x)
    let v' := fun y => chartFiber B e he ⟨p y, v y⟩
    have hv' := chartFiber_smoothAt S B R (fun y => ⟨p y, v y⟩) x e he hx (hv x)
    apply lift_smoothAt_of_coeff S B R (fun y => ⟨p y, s y • v y⟩) x e he hx
      (fun y => s y • v' y) (hp x) (euclidean_smul_smoothAt R v' s x hv' (hs x))
    filter_upwards [(hp x).1.preimage_mem_nhds (e.open_source.mem_nhds hx)] with y hy
    change p y ∈ e.source at hy
    refine ⟨hy, ?_⟩
    change s y • chartFiber B e he ⟨p y, v y⟩ = _
    rw [chartFiber_eq S B e he _ hy, map_smul]

/-- Realizations have the same intrinsic fiber coordinates, regardless of
choices of ambient product rearrangement. -/
theorem identity_smooth {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B D : TangentBundleStructure S) :
    @ManifoldContDiff (n+n) (n+n) a a (TotalSpace S) (TotalSpace S)
      B.topology D.topology (⊤ : ℕ∞) B.smoothAtlas D.smoothAtlas id := by
  letI := B.topology
  apply (@lift_smooth_iff.{u,u} n (n+n) a a M (TotalSpace S) _ B.topology
    S D B.manifold id).mpr
  refine ⟨projection_smooth S B, ?_⟩
  intro z e he hz
  let V := projection S ⁻¹' e.source
  have hp := projection_smooth S B
  have hV : IsOpen V := e.open_source.preimage
    (continuous_iff_continuousAt.mpr fun y => (hp y).1)
  have hid := manifoldContDiff_id (⊤ : ℕ∞) B.manifold.smoothStructure.val
    B.manifold.smoothStructure.property.1
  refine ⟨V, hV, hz, fun y hy => hy, fun y => chartFiber B e he y, ?_,
    chartFiber_smoothAt S B B.manifold id z e he hz (hid z)⟩
  intro y hy
  change y.1 ∈ e.source at hy
  change chartFiber B e he y = D.fiberCoordinates.equiv e he y.1 hy y.2
  rw [chartFiber_eq S B e he y hy]
  have h := chartCoordinates_unique (B.fiberCoordinates.isCoordinates e he y.1 hy)
    (D.fiberCoordinates.isCoordinates e he y.1 hy)
  exact congrArg (fun E : TangentSpace S y.1 ≃ₗ[ℝ] Euclidean n => E y.2) h

theorem canonical :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_canonicalType.{u} := by
  intro n a M _ S B D
  let h : @Diffeomorph (n+n) (n+n) a a (TotalSpace S) (TotalSpace S)
      B.topology D.topology B.smoothAtlas D.smoothAtlas :=
    @ContDiffDiffeomorph.mk (n+n) (n+n) a a (TotalSpace S) (TotalSpace S)
      B.topology D.topology (⊤ : ℕ∞) B.smoothAtlas D.smoothAtlas
      (Equiv.refl _) (identity_smooth S B D) (identity_smooth S D B)
  exact ⟨h, rfl⟩

/-- A single source chart suffices for the Euclidean-valued extension test. -/
theorem euclidean_smoothAt_of_chart {k m : ℕ} {c : ModelKind} {Q : Type*}
    [TopologicalSpace Q] (R : SmoothManifold k c Q) (w : Q → Euclidean m) (x : Q)
    (e : ModelChart k c Q) (he : e ∈ R.smoothStructure.val) (hx : x ∈ e.source)
    (hw : LocalCoordinateExtension (⊤ : ℕ∞) (fun y => (e y).val) w x) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val w x := by
  have hc : ContinuousAt w x := by
    obtain ⟨U, hU, hxU, F, hF, heF⟩ := hw
    exact ((hF.continuousOn.continuousAt (hU.mem_nhds hxU)).comp
      (f := fun y => (e y).val)
      (continuous_subtype_val.continuousAt.comp (f := fun y => e y) (e.continuousAt hx))).congr heF
  refine ⟨hc, ?_⟩
  intro d hd hxd
  exact LocalCoordinateExtension.comp hw
    (chartContDiffAt_of_compatible (R.smoothStructure.property.1.2 d hd e he) hxd hx)

theorem map_smooth :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_totalMap_smoothType.{u} := by
  intro n m a b M N _ _ S T B D f hf
  letI := B.topology
  letI := D.topology
  intro L hL z
  obtain ⟨e, he, hz⟩ := S.smoothStructure.property.1.1 z.1
  obtain ⟨d, hd, hfz⟩ := T.smoothStructure.property.1.1 (f z.1)
  obtain ⟨U, hU, hzU, F, hF, hFeq⟩ := (hf z.1).2 e he d hd hz hfz
  obtain ⟨V, hVeq, hV, hzV⟩ := mem_nhds_iff.mp hFeq
  have hπ := projection_smooth S B
  have hp := manifoldContDiff_comp (⊤ : ℕ∞) B.manifold.smoothStructure.val
    S.smoothStructure.val T.smoothStructure.val S.smoothStructure.property.1.1
    (projection S) f hπ hf
  let w : TotalSpace S → Euclidean m := fun y =>
    fderiv ℝ F (e y.1).val (chartFiber B e he y)
  have htz : z ∈ (B.chart e he).source := by
    simpa only [B.chart_source, TangentBundleData.projection, mem_preimage] using hz
  have hw : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) B.manifold.smoothStructure.val w z := by
    apply euclidean_smoothAt_of_chart B.manifold w z (B.chart e he) (chart_mem S B e he) htz
    let W : Set (Euclidean (n+n)) := B.productCoordinates.linearEquiv.symm ⁻¹' (U ×ˢ univ)
    refine ⟨W, (hU.prod isOpen_univ).preimage B.productCoordinates.linearEquiv.symm.continuous,
      ?_, fun q => fderiv ℝ F (B.productCoordinates.linearEquiv.symm q).1
        (B.productCoordinates.linearEquiv.symm q).2, ?_, ?_⟩
    · change B.productCoordinates.linearEquiv.symm ((B.chart e he) z).val ∈ U ×ˢ univ
      rw [B.chart_apply e he z hz, ContinuousLinearEquiv.symm_apply_apply]
      exact ⟨hzU, mem_univ _⟩
    · exact (ambientLift_contDiffOn hU hF).snd.comp
        B.productCoordinates.linearEquiv.symm.contDiff.contDiffOn (fun _ hq => hq)
    · filter_upwards [(B.chart e he).open_source.mem_nhds htz] with y hy
      have hye : y.1 ∈ e.source := by
        simpa only [B.chart_source, TangentBundleData.projection, mem_preimage] using hy
      change fderiv ℝ F (B.productCoordinates.linearEquiv.symm ((B.chart e he) y).val).1
        (B.productCoordinates.linearEquiv.symm ((B.chart e he) y).val).2 =
          fderiv ℝ F (e y.1).val (chartFiber B e he y)
      rw [B.chart_apply e he y hye, ContinuousLinearEquiv.symm_apply_apply,
        chartFiber_eq S B e he y hye]
  apply lift_smoothAt_of_coeff T D B.manifold (totalMap S T f L) z d hd hfz w (hp z) hw
  have hnear : ∀ᶠ q in 𝓝 z.1,
      q ∈ V ∧ q ∈ e.source ∧ f q ∈ d.source ∧ (e q).val ∈ U := by
    filter_upwards [hV.mem_nhds hzV, e.open_source.mem_nhds hz,
      (hf z.1).1.preimage_mem_nhds (d.open_source.mem_nhds hfz),
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hz)).preimage_mem_nhds
        (hU.mem_nhds hzU)] with q hqV hqe hqd hqU
    exact ⟨hqV, hqe, hqd, hqU⟩
  filter_upwards [Filter.Tendsto.eventually (hπ z).1 hnear] with y hy
  obtain ⟨hyV, hye, hyd, hyU⟩ := hy
  refine ⟨hyd, ?_⟩
  have hrep : (fun q => F (e q).val) =ᶠ[𝓝 y.1] (fun q => (d (f q)).val) :=
    Filter.mem_of_superset (hV.mem_nhds hyV) hVeq
  have hj := differential_jacobian S T f hf y.1 (L y.1) (hL y.1) e d he hd hye hyd
    (B.fiberCoordinates.equiv e he y.1 hye) (D.fiberCoordinates.equiv d hd (f y.1) hyd)
    (B.fiberCoordinates.isCoordinates e he y.1 hye)
    (D.fiberCoordinates.isCoordinates d hd (f y.1) hyd) U F hU hyU hF hrep y.2
  change fderiv ℝ F (e y.1).val (chartFiber B e he y) =
    D.fiberCoordinates.equiv d hd (f y.1) hyd (L y.1 y.2)
  rw [chartFiber_eq S B e he y hye]
  exact hj.symm

section Construction
open scoped Classical
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (K : FiberCoordinates S)
  (C : ProductCoordinates n a n .euclidean a)

noncomputable def rawFiber (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (z : TotalSpace S) : Euclidean n :=
  if hz : z.1 ∈ e.source then K.equiv e he z.1 hz z.2 else 0

noncomputable def rawInverse (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (y : ModelSpace (n+n) a) : TotalSpace S :=
  let p := e.symm (C.homeomorph.symm y).1
  ⟨p, if hp : p ∈ e.source then
    (K.equiv e he p hp).symm (C.homeomorph.symm y).2.val else 0⟩

theorem rawInverse_homeomorph (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (x : ModelSpace n a) (v : ModelSpace n .euclidean) (hx : x ∈ e.target) :
    rawInverse S K C e he (C.homeomorph (x, v)) =
      ⟨e.symm x, (K.equiv e he (e.symm x) (e.map_target hx)).symm v.val⟩ := by
  unfold rawInverse
  generalize hq : C.homeomorph.symm (C.homeomorph (x,v)) = q
  simp only [Homeomorph.symm_apply_apply] at hq
  subst q
  simp only [dite_eq_left (e.map_target hx)]

/-- Set theoretic tangent charts before the topology is constructed. -/
noncomputable def rawChart (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) :
    PartialEquiv (TotalSpace S) (ModelSpace (n+n) a) where
  toFun z := C.homeomorph (e z.1, ⟨rawFiber S K e he z, mem_univ _⟩)
  invFun := rawInverse S K C e he
  source := projection S ⁻¹' e.source
  target := C.homeomorph '' (e.target ×ˢ univ)
  map_source' z hz := ⟨_, ⟨e.map_source hz, mem_univ _⟩, rfl⟩
  map_target' y hy := by
    obtain ⟨⟨x, v⟩, ⟨hx, _⟩, rfl⟩ := hy
    change e.symm (C.homeomorph.symm (C.homeomorph (x, v))).1 ∈ e.source
    simpa only [Homeomorph.symm_apply_apply] using e.map_target hx
  left_inv' z hz := by
    change z.1 ∈ e.source at hz
    change rawInverse S K C e he (C.homeomorph
      (e z.1, ⟨rawFiber S K e he z, mem_univ _⟩)) = z
    rw [rawInverse_homeomorph S K C e he _ _ (e.map_source hz)]
    have hp := e.map_target (e.map_source hz)
    change (⟨e.symm (e z.1), (K.equiv e he (e.symm (e z.1)) hp).symm
      (rawFiber S K e he z)⟩ : TotalSpace S) = z
    generalize hq : e.symm (e z.1) = q at hp ⊢
    simp only [e.left_inv hz] at hq
    subst q
    simp only [rawFiber, dite_eq_left hz, LinearEquiv.symm_apply_apply]
  right_inv' y hy := by
    obtain ⟨⟨x, v⟩, ⟨hx, _⟩, rfl⟩ := hy
    have hp := e.map_target hx
    change C.homeomorph (e (rawInverse S K C e he (C.homeomorph (x, v))).1,
      ⟨rawFiber S K e he (rawInverse S K C e he (C.homeomorph (x, v))), mem_univ _⟩) = _
    rw [rawInverse_homeomorph S K C e he _ _ hx]
    simp only [rawFiber, dite_eq_left hp, e.right_inv hx, LinearEquiv.apply_symm_apply]


 theorem rawChart_apply (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (z : TotalSpace S) (hz : z.1 ∈ e.source) :
    (rawChart S K C e he z).val = C.linearEquiv
      ((e z.1).val, K.equiv e he z.1 hz z.2) := by
  change C.linearEquiv ((e z.1).val, rawFiber S K e he z) = _
  simp only [rawFiber, dif_pos hz]

 theorem rawChart_overlap (e d : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val) :
    ((rawChart S K C e he).symm.trans (rawChart S K C d hd)).source =
      C.homeomorph '' ((e.symm.trans d).source ×ˢ univ) := by
  ext y
  obtain ⟨⟨x,v⟩, rfl⟩ := C.homeomorph.surjective y
  simp [PartialEquiv.trans_source, rawChart, rawInverse, TangentBundleData.projection,
    OpenPartialHomeomorph.trans_source, C.homeomorph.injective.mem_set_image]

 theorem rawChart_overlap_open (e d : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val) :
    IsOpen ((rawChart S K C e he).symm.trans (rawChart S K C d hd)).source := by
  rw [rawChart_overlap]
  exact C.homeomorph.isOpenMap _ ((e.symm.trans d).open_source.prod isOpen_univ)

 theorem rawChart_transition_apply (e d : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (x : ModelSpace n a) (v : ModelSpace n .euclidean)
    (hx : x ∈ e.target) (hxd : e.symm x ∈ d.source) :
    (((rawChart S K C e he).symm.trans (rawChart S K C d hd))
      (C.homeomorph (x,v))).val = C.linearEquiv ((d (e.symm x)).val,
        K.equiv d hd (e.symm x) hxd ((K.equiv e he (e.symm x) (e.map_target hx)).symm v.val)) := by
  have hinv : rawInverse S K C e he (C.homeomorph (x,v)) =
      (⟨e.symm x, (K.equiv e he (e.symm x) (e.map_target hx)).symm v.val⟩ : TotalSpace S) := by
    unfold rawInverse
    generalize hq : C.homeomorph.symm (C.homeomorph (x,v)) = q
    simp only [Homeomorph.symm_apply_apply] at hq
    subst q
    simp only [dite_eq_left (e.map_target hx)]
  change (rawChart S K C d hd (rawInverse S K C e he (C.homeomorph (x,v)))).val = _
  rw [hinv, rawChart_apply S K C d hd _ hxd]
 theorem rawChart_transition_smooth (e d : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val) :
    ContDiffOnModel (⊤ : ℕ∞)
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd))
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd)).source := by
  intro y hy
  obtain ⟨⟨x,v⟩, rfl⟩ := C.homeomorph.surjective y
  have hxs : x ∈ (e.symm.trans d).source := by
    rw [rawChart_overlap] at hy
    simpa only [C.homeomorph.injective.mem_set_image, mem_prod, mem_univ, and_true] using hy
  have hx : x ∈ e.target := hxs.1
  have hxd : e.symm x ∈ d.source := hxs.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := S.smoothStructure.property.1.2 e he d hd |>.1 x hxs
  obtain ⟨V, hV, hxV, A, hA, hAeq⟩ := transition_smooth S K e d he hd
    (e.symm x) (e.map_target hx) hxd
  rw [e.right_inv hx] at hxV
  let W : Set (Euclidean (n+n)) := C.linearEquiv.symm ⁻¹' ((U ∩ V) ×ˢ univ)
  refine ⟨W, ((hU.inter hV).prod isOpen_univ).preimage C.linearEquiv.symm.continuous,
    ?_, fun z => C.linearEquiv (F (C.linearEquiv.symm z).1,
      A (C.linearEquiv.symm z).1 (C.linearEquiv.symm z).2), ?_, ?_⟩
  · change C.linearEquiv.symm (C.linearEquiv (x.val, v.val)) ∈ (U ∩ V) ×ˢ univ
    rw [C.linearEquiv.symm_apply_apply]
    exact ⟨⟨hxU,hxV⟩, mem_univ _⟩
  · exact C.linearEquiv.contDiff.contDiffOn.comp
      ((hF.comp C.linearEquiv.symm.contDiff.fst.contDiffOn (fun _ hz => hz.1.1)).prodMk
        ((hA.comp C.linearEquiv.symm.contDiff.fst.contDiffOn (fun _ hz => hz.1.2)).clm_apply
          C.linearEquiv.symm.contDiff.snd.contDiffOn)) (mapsTo_univ _ _)
  · intro y' hy' hy'W
    obtain ⟨⟨x',v'⟩, rfl⟩ := C.homeomorph.surjective y'
    have hxs' : x' ∈ (e.symm.trans d).source := by
      rw [rawChart_overlap] at hy'
      simpa only [C.homeomorph.injective.mem_set_image, mem_prod, mem_univ, and_true] using hy'
    change C.linearEquiv.symm (C.linearEquiv (x'.val,v'.val)) ∈ (U ∩ V) ×ˢ univ at hy'W
    rw [C.linearEquiv.symm_apply_apply] at hy'W
    change C.linearEquiv (F (C.linearEquiv.symm (C.linearEquiv (x'.val,v'.val))).1,
      A (C.linearEquiv.symm (C.linearEquiv (x'.val,v'.val))).1
        (C.linearEquiv.symm (C.linearEquiv (x'.val,v'.val))).2) = _
    rw [C.linearEquiv.symm_apply_apply,
      rawChart_transition_apply S K C e d he hd x' v' hxs'.1 hxs'.2]
    congr 1
    apply Prod.ext
    · exact hFeq x' hxs' hy'W.1.1
    · have hAe := hAeq (e.symm x') (e.map_target hxs'.1) hxs'.2
        (by simpa only [e.right_inv hxs'.1] using hy'W.1.2) v'.val
      simpa only [e.right_inv hxs'.1] using hAe
 theorem contDiffOnModel_continuousOn {k : ℕ} {b : ModelKind}
    {f : ModelSpace k b → ModelSpace k b} {s : Set (ModelSpace k b)}
    (hf : ContDiffOnModel (⊤ : ℕ∞) f s) : ContinuousOn f s := by
  intro x hx
  obtain ⟨U,hU,hxU,F,hF,heq⟩ := hf x hx
  apply tendsto_subtype_rng.mpr
  have hc : ContinuousAt (fun y : ModelSpace k b => F y.val) x :=
    (hF.continuousOn.continuousAt (hU.mem_nhds hxU)).comp continuous_subtype_val.continuousAt
  exact hc.continuousWithinAt.congr_of_eventuallyEq
    (by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU))] with y hy hyU
      exact (heq y hy hyU).symm)
    (heq x hx hxU).symm

 theorem rawChart_transition_continuousOn (e d : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val) :
    ContinuousOn ((rawChart S K C e he).symm.trans (rawChart S K C d hd))
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd)).source :=
  contDiffOnModel_continuousOn (rawChart_transition_smooth S K C e d he hd)


variable (A : ParametrizationAtlas (n+n) a (TotalSpace S))
    (hA : ∀ e he, rawChart S K C e he ∈ A.atlas)

noncomputable def madeChart (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) :
    @ModelChart (n+n) a (TotalSpace S) (parametrizationTopology A) :=
  A.openPartialHomeomorph (rawChart S K C e he) (hA e he)

theorem madeChart_decode (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (z : TotalSpace S) :
    C.homeomorph.symm (madeChart S K C A hA e he z) =
      (e z.1, ⟨rawFiber S K e he z, mem_univ _⟩) := by
  exact C.homeomorph.symm_apply_apply _

include K C hA in
theorem made_projection_continuous :
    @Continuous (TotalSpace S) M (parametrizationTopology A) _ (projection S) := by
  letI := parametrizationTopology A
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 z.1
  let t := madeChart S K C A hA e he
  have hz : z ∈ t.source := hp
  have htarget : (C.homeomorph.symm (t z)).1 ∈ e.target := by
    rw [madeChart_decode]
    exact e.map_source hp
  have hdec : ContinuousAt
      (fun y : TotalSpace S => (C.homeomorph.symm (t y)).1) z :=
    continuous_fst.continuousAt.comp
      (C.homeomorph.symm.continuous.continuousAt.comp (t.continuousAt hz))
  have hc : ContinuousAt (fun y : TotalSpace S =>
      e.symm ((C.homeomorph.symm (t y)).1)) z :=
    (e.symm.continuousAt htarget).comp
      (f := fun y : TotalSpace S => (C.homeomorph.symm (t y)).1) hdec
  apply hc.congr
  filter_upwards [t.open_source.mem_nhds hz] with y hy
  change e.symm ((C.homeomorph.symm (t y)).1) = y.1
  rw [madeChart_decode]
  exact e.left_inv hy

include K C hA in
theorem made_hausdorff : @T2Space (TotalSpace S) (parametrizationTopology A) := by
  letI := parametrizationTopology A
  letI := S.topologicalManifold.hausdorff
  apply t2Space_iff_disjoint_nhds.mpr
  intro z w hne
  by_cases hbase : z.1 = w.1
  · obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 z.1
    let t := madeChart S K C A hA e he
    have hz : z ∈ t.source := hp
    have hw : w ∈ t.source := by
      change w.1 ∈ e.source
      rw [← hbase]
      exact hp
    have hcoord : t z ≠ t w := fun h => hne (t.injOn hz hw h)
    exact (t.continuousAt hz).disjoint (disjoint_nhds_nhds.mpr hcoord) (t.continuousAt hw)
  · exact (made_projection_continuous S K C A hA).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase)
      (made_projection_continuous S K C A hA).continuousAt


include K C in
theorem bundleOfRawCharts
    (hopen : ∀ e d he hd, IsOpen
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd)).source)
    (hcont : ∀ e d he hd, ContinuousOn
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd))
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd)).source)
    (hsm : ∀ e d he hd, ContDiffOnModel (⊤ : ℕ∞)
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd))
      ((rawChart S K C e he).symm.trans (rawChart S K C d hd)).source) :
    Nonempty (TangentBundleStructure S) := by
  classical
  let D : Set (PartialEquiv (TotalSpace S) (ModelSpace (n+n) a)) :=
    {t | ∃ e he, t = rawChart S K C e he}
  have hcover : ∀ z : TotalSpace S, ∃ t ∈ D, z ∈ t.source := by
    intro z
    obtain ⟨e, he, hz⟩ := S.smoothStructure.property.1.1 z.1
    exact ⟨rawChart S K C e he, ⟨e, he, rfl⟩, hz⟩
  have hDopen : ∀ e ∈ D, ∀ d ∈ D, IsOpen (e.symm.trans d).source := by
    rintro e ⟨e, he, rfl⟩ d ⟨d, hd, rfl⟩
    exact hopen e d he hd
  have hDcont : ∀ e ∈ D, ∀ d ∈ D,
      ContinuousOn (e.symm.trans d) (e.symm.trans d).source := by
    rintro e ⟨e, he, rfl⟩ d ⟨d, hd, rfl⟩
    exact hcont e d he hd
  let A := parametrizationAtlasOfCover D hcover hDopen hDcont
  have hA : ∀ e he, rawChart S K C e he ∈ A.atlas :=
    fun e he => ⟨e, he, rfl⟩
  let T : TopologicalManifold n a M :=
    {S.topologicalManifold with
      atlas := S.smoothStructure.val
      covers := S.smoothStructure.property.1.1}
  obtain ⟨P, hP, hPA, hPc⟩ := T.countable_chart_cover
  letI := hP.to_subtype
  let f : P → PartialEquiv (TotalSpace S) (ModelSpace (n+n) a) :=
    fun e => rawChart S K C e.val (hPA e.property)
  let B := Set.range f
  have hB : B.Countable := Set.countable_range f
  have hBA : B ⊆ A.atlas := by
    rintro t ⟨e, rfl⟩
    exact hA e.val (hPA e.property)
  have hBc : ∀ z : TotalSpace S, ∃ t ∈ B, z ∈ t.source := by
    intro z
    obtain ⟨e, he, hp⟩ := hPc z.1
    exact ⟨f ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, hp⟩
  letI := parametrizationTopology A
  have hcharts : parametrizationCharts A =
      {t | ∃ e he, t = madeChart S K C A hA e he} := by
    ext t
    change (t ∈ ⋃ e : PartialEquiv (TotalSpace S) (ModelSpace (n+n) a),
      ⋃ he : e ∈ A.atlas, {A.openPartialHomeomorph e he}) ↔ _
    simp only [mem_iUnion, mem_singleton_iff, mem_setOf_eq]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨e, he, rfl⟩ := he
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨rawChart S K C e he, hA e he, rfl⟩
  have hcompat : ∀ e ∈ parametrizationCharts A, ∀ d ∈ parametrizationCharts A,
      ContDiffCompatible (⊤ : ℕ∞) e d := by
    rw [hcharts]
    rintro t ⟨e, he, rfl⟩ s ⟨d, hd, rfl⟩
    constructor
    · exact hsm e d he hd
    · change ContDiffOnModel (⊤ : ℕ∞)
        ((rawChart S K C d hd).symm.trans (rawChart S K C e he))
        ((rawChart S K C d hd).symm.trans (rawChart S K C e he)).source
      exact hsm d e hd he
  obtain ⟨R, _, hR⟩ := exists_smoothManifold_from_parametrizations A
    (made_hausdorff S K C A hA) B hB hBA hBc hcompat
  exact ⟨{
    topology := parametrizationTopology A
    productCoordinates := C
    fiberCoordinates := K
    manifold := R
    chart := madeChart S K C A hA
    chart_source := fun _ _ => rfl
    chart_target := fun _ _ => rfl
    chart_apply := fun e he z hz => rawChart_apply S K C e he z hz
    maximalAtlas := hR.trans (congrArg (maximalExtension (⊤ : ℕ∞)) hcharts) }⟩

end Construction

theorem tangentProductCoordinates_exists (n : ℕ) (a : ModelKind) :
    Nonempty (ProductCoordinates n a n .euclidean a) := by
  cases a with
  | euclidean => exact exists_euclidean_productCoordinates n n
  | halfSpace =>
    cases n with
    | zero =>
      exact ⟨⟨appendCoordinates 0 0, fun z => by
        simp [ModelData.modelSet, ModelData.halfSpaceSet]⟩⟩
    | succ n =>
      obtain ⟨C, _⟩ := exists_leftHalfSpace_productCoordinates n (n+1)
      exact ⟨C⟩

noncomputable def tangentProductCoordinates (n : ℕ) (a : ModelKind) :
    ProductCoordinates n a n .euclidean a :=
  Classical.choice (tangentProductCoordinates_exists n a)

/-- Tangent charts equip the disjoint union of the intrinsic derivation spaces
with its canonical Hausdorff, second-countable smooth manifold structure. -/
theorem exists_bundle :
    Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_existsType.{u} := by
  intro n a M _ S
  classical
  obtain ⟨K⟩ := fiberCoordinates_exists S
  obtain ⟨C⟩ := tangentProductCoordinates_exists n a
  exact bundleOfRawCharts S K C (rawChart_overlap_open S K C)
    (rawChart_transition_continuousOn S K C) (rawChart_transition_smooth S K C)

end SmoothManifolds.TangentBundle
