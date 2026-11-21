import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CompleteLocalIsometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CoveringMetricCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricGeodesicCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussLemma

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace P202.Geometry.CompleteLocalIsometry
open Set Filter
open scoped _root_.Topology unitInterval
open SmoothManifolds.AtlasData SmoothManifolds.MapData
  P202.MetricData P202.CompleteLocalIsometryData
universe u v

/-- The converse is the already proved componentwise pullback theorem. -/
theorem covering_complete :
    P202Specs.Geometry.CompleteLocalIsometry.covering_completeType.{u} :=
  P202.Geometry.CoveringMetricCompleteness.covering_complete

section RadialTopology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Unique lifts for a local homeomorphism from a Hausdorff space. Covering
existence is not assumed: only local injectivity and separation are used. -/
theorem path_lift_unique [T2Space X] {f : X → Y} (hf : IsLocalHomeomorph f)
    (a b : C(unitInterval, X))
    (hab : ∀ t, f (a t) = f (b t)) {t₀ : unitInterval} (h₀ : a t₀ = b t₀) :
    a = b := by
  apply DFunLike.ext'
  exact (T2Space.isSeparatedMap f).eq_of_comp_eq hf.isLocallyInjective
    a.continuous b.continuous (funext hab) t₀ h₀

/-- A continuous section of a local homeomorphism over an open set is an
open sheet. The total representative outside the open set is irrelevant. -/
noncomputable def sectionSheet {f : X → Y} (hf : IsLocalHomeomorph f)
    {U : Set Y} (hU : IsOpen U) (s : C(U, X))
    (hs : ∀ z : U, f (s z) = z.val) (x₀ : X) :
    P202Specs.Topology.CoveringSheet f U := by
  classical
  have hcomp : (f ∘ s : U → Y) = Subtype.val := funext hs
  have hemb : _root_.Topology.IsOpenEmbedding (s : U → X) :=
    hf.isOpenEmbedding_of_comp (hcomp ▸ hU.isOpenEmbedding_subtypeVal) s.continuous
  refine ⟨{
    toFun := f
    invFun := fun y => if hy : y ∈ U then s ⟨y, hy⟩ else x₀
    source := range s
    target := U
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := hemb.isOpen_range
    open_target := hU
    continuousOn_toFun := hf.continuous.continuousOn
    continuousOn_invFun := ?_ }, rfl, rfl⟩
  · rintro _ ⟨z, rfl⟩
    simpa only [hs] using z.property
  · intro y hy
    simp only [dite_eq_left hy]
    exact mem_range_self _
  · rintro _ ⟨z, rfl⟩
    simp only [hs, dite_eq_left z.property]
  · intro y hy
    simp only [dite_eq_left hy, hs]
  · apply continuousOn_iff_continuous_domRestrict.mpr
    convert s.continuous using 1
    ext z
    simp only [domRestrict_apply, dite_eq_left z.property, Subtype.coe_eta]

/-- Radial lifts yield every sheet, and reverse lifts ensure exhaustion of
the full preimage. Only the endpoint of each forward family must depend
continuously on the endpoint downstairs. -/
theorem evenlyCovered_of_radialLifts [T2Space X]
    {f : X → Y} (hf : IsLocalHomeomorph f) {y : Y} {U : Set Y}
    (hU : IsOpen U) (r : U → C(unitInterval, Y))
    (hr₀ : ∀ z, r z 0 = y) (hr₁ : ∀ z : U, r z 1 = z.val)
    (L : (f ⁻¹' {y}) → U → C(unitInterval, X))
    (hL : ∀ x z t, f (L x z t) = r z t)
    (hL₀ : ∀ x z, L x z 0 = x.val)
    (hLc : ∀ x, Continuous (fun z : U => L x z 1))
    (hreverse : ∀ e : X, ∀ he : f e ∈ U,
      ∃ a : C(unitInterval, X), a 1 = e ∧ ∀ t, f (a t) = r ⟨f e, he⟩ t) :
    P202Specs.Topology.EvenlyCovered f U := by
  classical
  let s (x : f ⁻¹' {y}) : C(U, X) := ⟨fun z => L x z 1, hLc x⟩
  have hs (x : f ⁻¹' {y}) (z : U) : f (s x z) = z.val :=
    (hL x z 1).trans (hr₁ z)
  let q (x : f ⁻¹' {y}) := sectionSheet hf hU (s x) (hs x) x.val
  refine ⟨hU, range q, ?_, ?_⟩
  · rintro a ⟨x, rfl⟩ b ⟨x', rfl⟩ hne
    apply Set.disjoint_left.mpr
    rintro e ⟨z, hze⟩ ⟨z', hz'e⟩
    have hzz : z = z' := Subtype.ext ((hs x z).symm.trans
      ((congrArg f hze).trans ((congrArg f hz'e).symm.trans (hs x' z'))))
    subst z'
    have heq : L x z = L x' z := path_lift_unique hf (L x z) (L x' z)
      (fun t => (hL x z t).trans (hL x' z t).symm) (hze.trans hz'e.symm)
    have hxx : x = x' := Subtype.ext <|
      (hL₀ x z).symm.trans ((DFunLike.congr_fun heq 0).trans (hL₀ x' z))
    exact hne (congrArg q hxx)
  · ext e
    simp only [mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨a, ⟨x, rfl⟩, z, rfl⟩
      exact (hs x z) ▸ z.property
    · intro he
      obtain ⟨a, ha₁, ha⟩ := hreverse e he
      have ha₀ : f (a 0) = y := (ha 0).trans (hr₀ ⟨f e, he⟩)
      let x : f ⁻¹' {y} := ⟨a 0, ha₀⟩
      have heq : L x ⟨f e, he⟩ = a := path_lift_unique hf _ _
        (fun t => (hL x ⟨f e, he⟩ t).trans (ha t).symm) (hL₀ x ⟨f e, he⟩)
      refine ⟨q x, ⟨x, rfl⟩, ⟨⟨f e, he⟩, ?_⟩⟩
      exact (DFunLike.congr_fun heq 1).trans ha₁

/-- Evenly covered neighborhoods make the image clopen, including at points
with empty fibers. Connectedness of the target and nonemptiness of the source
therefore give surjectivity. -/
theorem surjective_of_evenlyCovered [Nonempty X] [PreconnectedSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f)
    (h : ∀ y : Y, ∃ U : Set Y, y ∈ U ∧ P202Specs.Topology.EvenlyCovered f U) :
    Function.Surjective f := by
  have ho : IsOpen (range f) := by
    simpa only [image_univ] using hf.isOpenMap univ isOpen_univ
  have hc : IsClosed (range f) := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨U, hyU, hU, A, _, hex⟩ := h y
    refine ⟨U, ?_, hU, hyU⟩
    intro z hzU hz
    obtain ⟨x, hx⟩ := hz
    have hxU : x ∈ f ⁻¹' U := by change f x ∈ U; rwa [hx]
    rw [← hex] at hxU
    obtain ⟨a, _, _⟩ := mem_iUnion₂.mp hxU
    have hyt : y ∈ a.chart.target := by rw [a.target_eq]; exact hyU
    apply hy
    refine ⟨a.chart.symm y, ?_⟩
    exact (congrFun a.projection (a.chart.symm y)).symm.trans (a.chart.right_inv hyt)
  have hr : range f = univ := (show IsClopen (range f) from ⟨hc, ho⟩).eq_univ
    (range_nonempty f)
  exact range_eq_univ.mp hr

/-- The geometric data needed at one center. No covering or surjectivity is
included in this predicate. Reverse lifting is expressed as a forward lift
with prescribed terminal point, by reversing the lifted reversed segment. -/
def HasRadialLifts (f : X → Y) (y : Y) : Prop :=
  ∃ U : Set Y, y ∈ U ∧ IsOpen U ∧
    ∃ r : U → C(unitInterval, Y),
      (∀ z, r z 0 = y) ∧ (∀ z : U, r z 1 = z.val) ∧
      ∃ L : (f ⁻¹' {y}) → U → C(unitInterval, X),
        (∀ x z t, f (L x z t) = r z t) ∧
        (∀ x z, L x z 0 = x.val) ∧
        (∀ x, Continuous (fun z : U => L x z 1)) ∧
        ∀ e : X, ∀ he : f e ∈ U,
          ∃ a : C(unitInterval, X), a 1 = e ∧
            ∀ t, f (a t) = r ⟨f e, he⟩ t

/-- Local radial lift families give a surjective covering over a connected
base. Surjectivity is proved, including at initially empty fibers. -/
theorem covering_of_radialLifts [T2Space X] [Nonempty X] [PreconnectedSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) (h : ∀ y, HasRadialLifts f y) :
    P202Specs.Topology.Covering f := by
  have hU : ∀ y, ∃ U : Set Y, y ∈ U ∧ P202Specs.Topology.EvenlyCovered f U := by
    intro y
    obtain ⟨U, hy, ho, r, hr₀, hr₁, L, hL, hL₀, hLc, hrev⟩ := h y
    exact ⟨U, hy, evenlyCovered_of_radialLifts hf ho r hr₀ hr₁ L hL hL₀ hLc hrev⟩
  exact ⟨surjective_of_evenlyCovered hf hU, hU⟩

end RadialTopology
section SmoothSheets
variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold m .euclidean Y)
    (f : X → Y)

/-- Smooth inverse germs suffice for the topological local-homeomorphism
property. This argument needs neither completeness nor a dimension choice. -/
theorem localDiffeomorphism_isLocalHomeomorph
    (hf : SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f) :
    IsLocalHomeomorph f := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf.1 x).1
  have ho : IsOpenMap f := IsOpenMap.of_nhds_le fun x => by
    obtain ⟨g, hg, hgp, _, hfg⟩ := hf.2 x
    have hgt : Tendsto g (𝓝 (f x)) (𝓝 (g (f x))) := hg.1
    exact le_map_of_right_inverse hfg (by simpa only [hgp] using hgt)
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨g, _, _, hgf, _⟩ := hf.2 x
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hgf
  have hUo : IsOpen U := hU
  refine ⟨U, hUo.mem_nhds hxU, .of_continuous_injective_isOpenMap
    (hc.comp continuous_subtype_val) ?_ (ho.comp hUo.isOpenEmbedding_subtypeVal.isOpenMap)⟩
  intro z w hzw
  exact Subtype.ext <| (hUsub z.property).symm.trans
    ((congrArg g hzw).trans (hUsub w.property))

/-- Every topological sheet of a local diffeomorphism is a smooth sheet.
The inverse agrees near each target point with a smooth inverse germ. -/
theorem sheet_smooth
    (hf : SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f)
    (q : OpenPartialHomeomorph X Y) (hq : EqOn q f q.source) :
    ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val q q.source ∧
    ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val q.symm q.target := by
  constructor
  · intro x hx
    apply SmoothManifolds.manifoldContDiffAt_congr (hf.1 x)
    filter_upwards [q.open_source.mem_nhds hx] with z hz
    exact (hq hz).symm
  · intro y hy
    have he := q.map_target hy
    have hfy : f (q.symm y) = y := (hq he).symm.trans (q.right_inv hy)
    obtain ⟨g, hg, hge, hgf, hfg⟩ := hf.2 (q.symm y)
    rw [hfy] at hg hge hfg
    apply SmoothManifolds.manifoldContDiffAt_congr hg
    have hnear := (q.continuousAt_symm hy).preimage_mem_nhds hgf
    filter_upwards [hnear, q.open_target.mem_nhds hy] with z hz hzt
    change g (f (q.symm z)) = q.symm z at hz
    have hfz : f (q.symm z) = z :=
      (hq (q.map_target hzt)).symm.trans (q.right_inv hzt)
    simpa only [hfz] using hz

/-- Upgrade the existing disjoint open decomposition, preserving every sheet
and the exact preimage equality. -/
theorem smoothEvenlyCovered_of_evenlyCovered
    (hf : SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f)
    {U : Set Y} (hU : P202Specs.Topology.EvenlyCovered f U) :
    SmoothEvenlyCovered S T f U := by
  obtain ⟨ho, A, hdis, hex⟩ := hU
  refine ⟨ho, A, hdis, hex, fun s _ => ?_⟩
  exact sheet_smooth S T f hf s.chart (fun z _ => congrFun s.projection z)

/-- Assembly of the topological and smooth conclusions from the actual
radial lift families. Completeness will be used to construct those families. -/
theorem complete_local_isometry_of_radialLifts
    [Nonempty X] [PreconnectedSpace Y]
    (hf : SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f)
    (hr : ∀ y, HasRadialLifts f y) :
    P202Specs.Topology.Covering f ∧
      ∀ y : Y, ∃ U : Set Y, y ∈ U ∧ SmoothEvenlyCovered S T f U := by
  letI : T2Space X := S.topologicalManifold.hausdorff
  have hc := covering_of_radialLifts (localDiffeomorphism_isLocalHomeomorph S T f hf) hr
  refine ⟨hc, fun y => ?_⟩
  obtain ⟨U, hy, hU⟩ := hc.2 y
  exact ⟨U, hy, smoothEvenlyCovered_of_evenlyCovered S T f hf hU⟩

end SmoothSheets

section GeodesicTransport
open SmoothManifolds.ModelData SmoothManifolds.TangentData
  SmoothManifolds.DifferentialData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.LeviCivitaData P202.CurveConnectionData
  P202.GeodesicData P202.ExponentialData
variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold m .euclidean Y}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : X → Y) (hi : IsLocalIsometry g h f)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)

include hC hK in
/-- Connection preservation on smooth fields implies preservation along actual
C¹ curves, by a finite local expansion in smooth fields. -/
theorem localIsometry_curve_derivative
    {c : ℝ → X} {v : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    {D : TangentSpace S (c t)}
    (hD : HasCovariantDerivativeAt C c v t D) :
    HasCovariantDerivativeAt K (f ∘ c)
      (fun s => SmoothManifolds.differential S T f hi.1.1 (c s) (v s)) t
      (SmoothManifolds.differential S T f hi.1.1 (c t) D) := by
  classical
  let L := SmoothManifolds.differential S T f hi.1.1
  have hL := SmoothManifolds.differential_spec S T f hi.1.1
  have hm : IsMetricPreserving g h f L := by
    obtain ⟨A, hA, hmA⟩ := hi.2
    have he : A = L := by
      funext p
      exact (SmoothManifolds.differential_exists S T f hi.1.1 p).unique (hA p) (hL p)
    exact he ▸ hmA
  have hDc := hD
  obtain ⟨V, hV, _⟩ := hDc
  obtain ⟨Z, hZ⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have hVZ : HasVelocityWithinAt S c univ t (Z.val (c t)) := by rwa [hZ]
  obtain ⟨Z', hZ'⟩ := LeviCivita.exists_related_germ f hi.1 L hL Z (c t)
  have hV' : HasVelocityWithinAt T (f ∘ c) univ t (Z'.val (f (c t))) := by
    rw [← hZ'.self_of_nhds]
    exact GaussLemma.velocity_smooth_postcomposition f hi.1.1 (mem_univ t) hVZ
  obtain ⟨a, a', e, ha, hv, hDF⟩ :=
    InducedConnections.curve_derivative_representation C Z (mem_univ t)
      (uniqueDiffWithinAt_univ) hVZ hD
  have he : ∀ i : Fin n, ∃ e' : Field T,
      ∀ᶠ q in 𝓝 (c t), L q ((e i).val q) = e'.val (f q) :=
    fun i => LeviCivita.exists_related_germ f hi.1 L hL (e i) (c t)
  choose e' he' using he
  have hconn (i : Fin n) : L (c t) ((C.cov Z (e i)).val (c t)) =
      (K.cov Z' (e' i)).val (f (c t)) :=
    LeviCivita.connection_related_at TorsionAndMetric.torsion_apply
      f hi.1 L hL g h hm C K hC hK Z (e i) Z' (e' i) (c t) hZ' (he' i)
  have hsum := InducedConnections.curve_derivative_sum K Z' (mem_univ t)
    uniqueDiffWithinAt_univ hV' Finset.univ
    (fun i s => a i s • (e' i).val (f (c s)))
    (fun i => a' i • (e' i).val (f (c t)) + a i t • (K.cov Z' (e' i)).val (f (c t)))
    (fun i _ => CurveCovariantDerivative.derivative_smul K
      (CurveCovariantDerivative.derivative_section_field K (e' i) Z' (mem_univ t) hV') (ha i))
  have hvalue : L (c t) D = ∑ i, (a' i • (e' i).val (f (c t)) +
      a i t • (K.cov Z' (e' i)).val (f (c t))) := by
    rw [hDF, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_add, map_smul, map_smul, (he' i).self_of_nhds, hconn i]
  change HasCovariantDerivativeAt K (f ∘ c) _ t (L (c t) D)
  rw [hvalue]
  apply InducedConnections.curve_derivative_congr K (mem_univ t) hsum
  filter_upwards [hv, hV.1 (Filter.eventually_all.mpr he')] with s hs heq
  change (∑ i, a i s • (e' i).val (f (c s))) = L (c s) (v s)
  rw [hs, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, heq i]

/-- The tangent lift uses the canonical differential on the original fibers. -/
noncomputable def mapPhase (q : ℝ → Phase S) (t : ℝ) : Phase T :=
  ⟨f (q t).1, SmoothManifolds.differential S T f hi.1.1 (q t).1 (q t).2⟩

include hC hK in
/-- A local isometry sends intrinsic geodesics to intrinsic geodesics. -/
theorem localIsometry_geodesic {Jset : Set ℝ} {q : ℝ → Phase S}
    (hq : IsGeodesicOn S C Jset q) :
    IsGeodesicOn T K Jset (mapPhase g h f hi q) := by
  intro t ht
  refine ⟨GaussLemma.velocity_smooth_postcomposition f hi.1.1 (mem_univ t) (hq t ht).1, ?_⟩
  have hd := localIsometry_curve_derivative g h f hi C K hC hK (hq t ht).2
  rw [map_zero] at hd
  exact hd

/-- Completeness gives a continuous position curve on the whole real line. -/
def completeFamilyPosition
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (hfull : ∀ w, (F.interval w).carrier = univ) (w : Phase S) : C(ℝ, X) :=
  ⟨fun t => (F.curve w t).1, continuous_iff_continuousAt.mpr fun t => by
    have ht : t ∈ (F.interval w).carrier := hfull w ▸ mem_univ t
    exact (MetricGeodesicCompleteness.geodesic_hasVelocityAt C (hF w).2.2.1 ht).1⟩

include hC hK in
/-- A global source geodesic projects to every target geodesic with the same
initial phase, on the latter's actual interval. No target completeness is used. -/
theorem project_family_agrees
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (hfull : ∀ w, (F.interval w).carrier = univ) (w : Phase S)
    (J : D13Unified.OpenTimeInterval) (q : ℝ → Phase T)
    (hJ : 0 ∈ J.carrier) (hq : IsGeodesicOn T K J.carrier q)
    (hinit : (⟨f w.1, SmoothManifolds.differential S T f hi.1.1 w.1 w.2⟩ : Phase T) = q 0) :
    EqOn (mapPhase g h f hi (F.curve w)) q J.carrier := by
  have hgeo : IsGeodesicOn S C univ (F.curve w) := by
    rw [← hfull w]
    exact (hF w).2.2.1
  have hproj := localIsometry_geodesic g h f hi C K hC hK hgeo
  have heq := GeodesicIVP.overlap_unique T K D13Unified.OpenTimeInterval.whole J
    (mapPhase g h f hi (F.curve w)) q hproj hq 0 ⟨mem_univ _, hJ⟩ (by
      change (⟨f (F.curve w 0).1,
        SmoothManifolds.differential S T f hi.1.1 (F.curve w 0).1 (F.curve w 0).2⟩ : Phase T) = _
      rw [(hF w).2.1]
      exact hinit)
  exact fun t ht => heq ⟨mem_univ _, ht⟩

/-- The inverse actual differential lifts every tangent phase over an image
point; its dependence on tangent coordinates is linear. -/
theorem lift_initial_linear (x : X) (y : Y) (hx : f x = y)
    (E : TangentSpace T y ≃ₗ[ℝ] Euclidean m) :
    ∃ V : Euclidean m →ₗ[ℝ] TangentSpace S x, ∀ a,
      (⟨f x, SmoothManifolds.differential S T f hi.1.1 x (V a)⟩ : Phase T) =
        ⟨y, E.symm a⟩ := by
  subst y
  let D := SmoothManifolds.Tensors.localDiffeomorphismDifferential S T f hi.1 x
  refine ⟨D.symm.toLinearMap.comp E.symm.toLinearMap, fun a => ?_⟩
  change (⟨f x, D (D.symm (E.symm a))⟩ : Phase T) = _
  rw [D.apply_symm_apply]

include g h hi hC hK in
/-- Every geodesic on an open interval through zero lifts from any point over
its initial point. The resulting source curve exists on all real times. -/
theorem geodesic_path_lift
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (hfull : ∀ w, (F.interval w).carrier = univ)
    (J : D13Unified.OpenTimeInterval) (q : ℝ → Phase T)
    (hJ : 0 ∈ J.carrier) (hq : IsGeodesicOn T K J.carrier q)
    (x : X) (hx : f x = (q 0).1) :
    ∃ a : C(ℝ, X), a 0 = x ∧ ∀ t ∈ J.carrier, f (a t) = (q t).1 := by
  obtain ⟨e, he, hp⟩ := T.smoothStructure.property.1.1 (q 0).1
  let E := (tangentStructure T).fiberCoordinates.equiv e he (q 0).1 hp
  obtain ⟨V, hV⟩ := lift_initial_linear g h f hi x (q 0).1 hx E
  let w : Phase S := ⟨x, V (E (q 0).2)⟩
  have hw : (⟨f w.1, SmoothManifolds.differential S T f hi.1.1 w.1 w.2⟩ : Phase T) = q 0 := by
    rw [hV, E.symm_apply_apply]
  refine ⟨completeFamilyPosition C F hF hfull w, ?_, ?_⟩
  · exact congrArg Sigma.fst (hF w).2.1
  · intro t ht
    exact congrArg Sigma.fst (project_family_agrees g h f hi C K hC hK F hF hfull w J q hJ hq hw ht)

/-- Every linear family in a fixed original tangent fiber is continuous in
the original tangent-bundle topology, also for different displayed dimensions. -/
theorem linear_fiberInclusion_continuous {k : ℕ} (x : X)
    (V : Euclidean k →ₗ[ℝ] TangentSpace S x) :
    Continuous (fun a : Euclidean k => (⟨x, V a⟩ : Phase S)) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 x
  let A := (tangentStructure S).fiberCoordinates.equiv e he x hp
  have hv : Continuous (A.toLinearMap.comp V) :=
    (A.toLinearMap.comp V).continuous_of_finiteDimensional
  have heq : (fun a : Euclidean k => (⟨x, V a⟩ : Phase S)) =
      (fun a : Euclidean n => (⟨x, A.symm a⟩ : Phase S)) ∘ (A.toLinearMap.comp V) := by
    funext a
    exact congrArg (Sigma.mk x) (A.symm_apply_apply (V a)).symm
  rw [heq]
  exact (ExponentialNormalCoordinates.fiberInclusion_continuous_basis x A).comp hv

include g h hi hC hK in
/-- Source completeness constructs forward radial families and lifts of
reversed radial segments, including every point of the full preimage. -/
theorem radialLifts_of_completeFamily
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (hfull : ∀ w, (F.interval w).carrier = univ)
    (G : CurveFamily (Phase T)) (hG : IsMaximalFamily T K G)
    (y : Y) : HasRadialLifts f y := by
  classical
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_exists T h y
  obtain ⟨ρ, c, hρ, hc, hy, hcy, htarget, hnormal⟩ :=
    ExponentialNormalCoordinates.normal_chart_exists T h K hK G hG y E hE
  let U := c.source
  let w (z : U) : Phase T := ⟨y, E.symm (c z.val).val⟩
  have hend (z : U) : (w z) ∈ exponentialDomain G ∧
      (G.curve (w z) 1).1 = z.val := by
    have hz : tangentNorm h y (E.symm (c z.val).val) < ρ := by
      have hz := c.map_source z.property
      rwa [htarget] at hz
    obtain ⟨hd, he⟩ := hnormal (c z.val) hz
    exact ⟨hd, he.trans (c.left_inv z.property)⟩
  have hsub (z : U) : Icc (0 : ℝ) 1 ⊆ (G.interval (w z)).carrier :=
    (G.interval (w z)).ordConnected.out (hG (w z)).1 (hend z).1
  let r (z : U) : C(unitInterval, Y) :=
    ⟨fun t => (G.curve (w z) t.val).1, by
      exact (show ContinuousOn (fun t => (G.curve (w z) t).1) (Icc (0 : ℝ) 1) from
        fun t ht => (MetricGeodesicCompleteness.geodesic_hasVelocityAt K
          (hG (w z)).2.2.1 (hsub z ht)).1.continuousWithinAt).domRestrict⟩
  have hr₀ (z : U) : r z 0 = y := congrArg Sigma.fst (hG (w z)).2.1
  have hr₁ (z : U) : r z 1 = z.val := (hend z).2
  have hV : ∀ x : f ⁻¹' {y}, ∃ V : Euclidean m →ₗ[ℝ] TangentSpace S x.val,
      ∀ a, (⟨f x.val, SmoothManifolds.differential S T f hi.1.1 x.val (V a)⟩ : Phase T) =
        ⟨y, E.symm a⟩ :=
    fun x => lift_initial_linear g h f hi x.val y x.property E
  choose V hV using hV
  let v (x : f ⁻¹' {y}) (z : U) : Phase S := ⟨x.val, V x (c z.val).val⟩
  let L (x : f ⁻¹' {y}) (z : U) : C(unitInterval, X) :=
    (completeFamilyPosition C F hF hfull (v x z)).comp
      ⟨Subtype.val, continuous_subtype_val⟩
  have hL (x : f ⁻¹' {y}) (z : U) (t : unitInterval) :
      f (L x z t) = r z t := by
    exact congrArg Sigma.fst <|
      project_family_agrees g h f hi C K hC hK F hF hfull (v x z)
        (G.interval (w z)) (G.curve (w z)) (hG (w z)).1 (hG (w z)).2.2.1
        ((hV x (c z.val).val).trans (hG (w z)).2.1.symm) (hsub z t.property)
  have hL₀ (x : f ⁻¹' {y}) (z : U) : L x z 0 = x.val :=
    congrArg Sigma.fst (hF (v x z)).2.1
  have hLc (x : f ⁻¹' {y}) : Continuous (fun z : U => L x z 1) := by
    have hv : Continuous (v x) :=
      (linear_fiberInclusion_continuous x.val (V x)).comp
        (continuous_subtype_val.comp
          (c.continuousOn.domRestrict))
    apply continuous_iff_continuousAt.mpr
    intro z
    have hd : v x z ∈ exponentialDomain F := by
      change 1 ∈ (F.interval (v x z)).carrier
      rw [hfull]
      trivial
    exact (ExponentialNormalCoordinates.smooth S C F hF _ hd).1.comp hv.continuousAt
  refine ⟨U, hy, c.open_source, r, hr₀, hr₁, L, hL, hL₀, hLc, ?_⟩
  intro e he
  let z : U := ⟨f e, he⟩
  obtain ⟨J, hJ, hj⟩ := GeodesicIVP.maximal_affine T K (w z)
    (G.interval (w z)) (G.curve (w z)) (hG (w z)) (-1) 1 (by norm_num)
    (hsub z (by constructor <;> norm_num))
  have hzero : 0 ∈ J.carrier := hj.1
  have hstart : f e = (affineCurve T (G.curve (w z)) (-1) 1 0).1 := by
    simpa only [affineCurve, mul_zero, zero_add] using (hend z).2.symm
  obtain ⟨b, hb, hbproj⟩ := geodesic_path_lift g h f hi C K hC hK F hF hfull
    J (affineCurve T (G.curve (w z)) (-1) 1) hzero hj.2.2.1 e hstart
  let a : C(unitInterval, X) := b.comp
    ⟨fun t => 1 - t.val, continuous_const.sub continuous_subtype_val⟩
  refine ⟨a, ?_, fun t => ?_⟩
  · change b (1 - 1) = e
    simpa using hb
  · have ht : 1 - t.val ∈ J.carrier := by
      rw [hJ]
      change -1 * (1 - t.val) + 1 ∈ (G.interval (w z)).carrier
      convert hsub z t.property using 1 <;> ring
    have hp := hbproj (1 - t.val) ht
    change f (b (1 - t.val)) = (G.curve (w z) t.val).1
    simpa only [affineCurve, show -1 * (1 - t.val) + 1 = t.val by ring] using hp

end GeodesicTransport

/-- A complete connected source local isometry is a surjective smooth
covering. The sheets are the endpoint images of lifted normal radial segments. -/
theorem complete_local_isometry :
    P202Specs.Geometry.CompleteLocalIsometry.complete_local_isometryType.{u} := by
  intro n m X Y _ _ _ _ S T g h f hi hc
  obtain ⟨C, hC, _⟩ := LeviCivita.exists_unique g
  obtain ⟨K, hK, _⟩ := LeviCivita.exists_unique h
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨G, hG⟩ := ExponentialNormalCoordinates.family_exists T K
  have hfull : ∀ w, (F.interval w).carrier = univ := fun w =>
    MetricGeodesicCompleteness.metric_complete_geodesically_complete S g C hC hc
      w (F.interval w) (F.curve w) (hF w)
  exact complete_local_isometry_of_radialLifts S T f hi.1
    (radialLifts_of_completeFamily g h f hi C K hC hK F hF hfull G hG)
end P202.Geometry.CompleteLocalIsometry
