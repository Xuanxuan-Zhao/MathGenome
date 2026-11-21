import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.KillingHopf
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HyperbolicHalfSpace
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalSpaceFormDevelopment
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CompleteLocalIsometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.DeckGroup
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Basic.Countable.Small
import Mathlib.Topology.Instances.Shrink

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace P202.Geometry.KillingHopf
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.CurvatureData
  P202.ConstantCurvaturePolarData P202.CompletenessData P202.LocalDevelopmentData
  P202.KillingHopfData P202Specs.Topology
open Set Filter
open scoped _root_.Topology
universe u v w

/-- The on-domain predicate on the entire manifold is the shared global
local-isometry predicate. No regularity or inverse clauses are lost. -/
theorem localIsometryOn_univ_iff {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : X → M) :
    IsLocalIsometryOn g h f univ ↔ IsLocalIsometry g h f := by
  classical
  constructor
  · intro hf
    refine ⟨⟨fun x => (hf.2 x (mem_univ x)).1,
      fun x => (hf.2 x (mem_univ x)).2.1⟩, ?_⟩
    choose L hL using fun x => (hf.2 x (mem_univ x)).2.2
    exact ⟨L, fun x => (hL x).1, fun x => (hL x).2⟩
  · rintro ⟨hf, L, hL, hmetric⟩
    exact ⟨isOpen_univ, fun x _ => ⟨hf.1 x, hf.2 x, L x, hL x, hmetric x⟩⟩

/-- A connected covering has a free deck action on every point. -/
theorem deck_free {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M] [ConnectedSpace X]
    (f : C(X, M)) (hf : Covering f) (F : DeckGroup f) (x : X)
    (hx : F.val x = x) : F = 1 := by
  apply P202.Topology.DeckGroup.determined X M f hf x
  exact hx

/-- An open sheet is disjoint from each nonidentity translate. This uses
only connectedness upstairs, and does not require a regular covering. -/
theorem deck_properlyDiscontinuous {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M] [ConnectedSpace X]
    (f : C(X, M)) (hf : Covering f) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ F : DeckGroup f, F ≠ 1 → Disjoint U (F.val '' U) := by
  obtain ⟨c, hx, hc⟩ := (P202.Topology.covering_to_library hf).isLocalHomeomorph x
  refine ⟨c.source, c.open_source, hx, fun F hF => Set.disjoint_left.mpr ?_⟩
  rintro z hz ⟨y, hy, rfl⟩
  have he : F.val y = y := c.injOn hz hy (by
    rw [← congrFun hc (F.val y), ← congrFun hc y]
    exact congrFun F.property y)
  exact hF (deck_free f hf F y he)

/-- A simply connected source has trivial image subgroup, with the paper's
first-path-first convention retained through the upstream Pi1 definition. -/
theorem induced_range_eq_bot {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M] [SimplyConnectedSpace X]
    {x : X} {m : M} (f : PointedMap X M x m) : f.induced.range = ⊥ := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : b = 1 := Subsingleton.elim _ _
    simp [hb]
  · intro ha
    have ha' : a = 1 := Subgroup.mem_bot.mp ha
    subst a
    exact ⟨1, map_one _⟩

/-- Simple connectivity of two total spaces gives a pointed homeomorphism
over the base, via the actual subgroup classification criterion. -/
theorem universalCoverHomeomorph {X : Type u} {Y : Type v} {M : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] [LocallyPathConnectedSpace M]
    (f : C(X, M)) (p : C(Y, M)) (hf : Covering f) (hp : Covering p)
    (x : X) (y : Y) (he : f x = p y) :
    ∃ e : X ≃ₜ Y, e x = y ∧ ∀ z, p (e z) = f z := by
  let f₀ : PointedMap X M x (f x) := ⟨f, rfl⟩
  let p₀ : PointedMap Y M y (f x) := ⟨p, he.symm⟩
  exact (P202.Topology.CoveringClassification.pointedIsomorphismCriterion
    X Y M x y (f x) f₀ p₀ hf hp).mp
      ((induced_range_eq_bot f₀).trans (induced_range_eq_bot p₀).symm)

/-- Fibers of a universal cover are exactly the actual deck group orbits.
There is no regularity or monodromy assumption. -/
theorem universalCover_fibers {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace M]
    (f : C(X, M)) (hf : Covering f) (x y : X) :
    f x = f y ↔ ∃ F : DeckGroup f, F.val x = y := by
  constructor
  · intro he
    obtain ⟨e, hex, hef⟩ := universalCoverHomeomorph f f hf hf x y he
    exact ⟨⟨e, funext hef⟩, hex⟩
  · rintro ⟨F, rfl⟩
    exact (congrFun F.property x).symm

/-- The natural map of the actual deck orbit space is a homeomorphism. Its
formula on every orbit is part of the conclusion. -/
theorem universalCover_quotient {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace M]
    (f : C(X, M)) (hf : Covering f) :
    ∃ e : Quotient (MulAction.orbitRel (DeckGroup f) X) ≃ₜ M,
      ∀ x, e (Quotient.mk _ x) = f x := by
  have hq : _root_.Topology.IsQuotientMap f :=
    (P202.Topology.covering_to_library hf).isLocalHomeomorph.isOpenMap.isQuotientMap
      f.continuous hf.1
  let e₀ : Quotient (MulAction.orbitRel (DeckGroup f) X) ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight (fun x y => by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact (universalCover_fibers f hf y x).symm.trans eq_comm)
  exact ⟨e₀.trans hq.homeomorph, fun _ => rfl⟩

section SmoothComparison
variable {n : ℕ} {X Y M : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
  {S : SmoothManifold n .euclidean X} {Q : SmoothManifold n .euclidean Y}
  {T : SmoothManifold n .euclidean M}

/-- A continuous lift of a smooth map through a local diffeomorphism is
smooth. This is proved from inverse germs, without adding smooth lifting data. -/
theorem smooth_of_lift {p : Y → M}
    (hp : SmoothManifolds.TensorData.IsLocalDiffeomorphism Q T p)
    {f : X → M} (hf : IsSmoothMap S T f) {L : X → Y}
    (hL : Continuous L) (hover : ∀ x, p (L x) = f x) : IsSmoothMap S Q L := by
  intro x
  obtain ⟨j, hj, _, hjp, _⟩ := hp.2 (L x)
  rw [hover x] at hj
  have hs := SmoothManifolds.manifoldContDiffAt_comp
    T.smoothStructure.property.1.1 (hf x) hj
  apply SmoothManifolds.manifoldContDiffAt_congr hs
  have hnear := hL.continuousAt.preimage_mem_nhds hjp
  filter_upwards [hnear] with z hz
  change j (p (L z)) = L z at hz
  change j (f z) = L z
  rw [← hover]
  exact hz

/-- A homeomorphism over the base of two local Riemannian isometries is
itself a smooth local Riemannian isometry. The differential comparison is the
intrinsic chain rule and its uniqueness, not a new compatibility assumption. -/
theorem localIsometry_of_homeomorph_over
    (g : RiemannianMetric S) (j : RiemannianMetric Q) (h : RiemannianMetric T)
    {f : X → M} {p : Y → M}
    (hf : IsLocalIsometry g h f) (hp : IsLocalIsometry j h p)
    (e : X ≃ₜ Y) (hover : ∀ x, p (e x) = f x) :
    IsLocalIsometry g j e ∧ IsSmoothMap Q S e.symm := by
  have hes : IsSmoothMap S Q e := smooth_of_lift hp.1 hf.1.1 e.continuous hover
  have heis : IsSmoothMap Q S e.symm := smooth_of_lift hf.1 hp.1.1 e.symm.continuous
    (fun y => (hover (e.symm y)).symm.trans (congrArg p (e.apply_symm_apply y)))
  have heLocal : SmoothManifolds.TensorData.IsLocalDiffeomorphism S Q e :=
    ⟨hes, fun x => ⟨e.symm, heis (e x), e.symm_apply_apply x,
      Filter.Eventually.of_forall e.symm_apply_apply,
      Filter.Eventually.of_forall e.apply_symm_apply⟩⟩
  refine ⟨⟨heLocal, ?_⟩, heis⟩
  have heq : f = p ∘ e := funext (fun x => (hover x).symm)
  subst f
  obtain ⟨Lf, hLf, hmetricf⟩ := hf.2
  obtain ⟨Lp, hLp, hmetricp⟩ := hp.2
  let Le := SmoothManifolds.differential S Q e hes
  have hLe := SmoothManifolds.differential_spec S Q e hes
  refine ⟨Le, hLe, fun x v w => ?_⟩
  have hcomp := SmoothManifolds.differential_comp S Q T e p hes hp.1.1
    x (Le x) (Lp (e x)) (hLe x) (hLp (e x))
  have huniq : Lf x = (Lp (e x)).comp (Le x) :=
    (SmoothManifolds.differential_exists S T (p ∘ e) hf.1.1 x).unique (hLf x) hcomp
  calc
    pairing j (e x) (Le x v) (Le x w) =
      pairing h (p (e x)) (Lp (e x) (Le x v)) (Lp (e x) (Le x w)) :=
        (hmetricp (e x) (Le x v) (Le x w)).symm
    _ = pairing g x v w := by
      simpa only [huniq, LinearMap.comp_apply, Function.comp_apply] using hmetricf x v w

/-- A local isometry does not increase the original length distance. This
argument uses the entire upstream curve class, including arbitrary intervals. -/
theorem localIsometry_distance_le [ConnectedSpace X]
    (g : RiemannianMetric S) (h : RiemannianMetric T) {f : X → M}
    (hf : IsLocalIsometry g h f) (x y : X) :
    P202.CompleteExponentialData.lengthDistance h (f x) (f y) ≤
      P202.CompleteExponentialData.lengthDistance g x y := by
  have hne : (P202.DistanceData.pathLengths g x y).Nonempty :=
    (P202.Geometry.LengthDistance.pathLengths_nonempty_iff g x y).mpr
      ((P202.Geometry.LengthDistance.path_exists S x y).mpr (by
        rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial))
  apply le_csInf hne
  rintro r ⟨a, b, c, hc₀, hc₁, rfl⟩
  obtain ⟨d, hd, hlength⟩ := P202.Geometry.MetricFoundation.localIsometry_length_exists
    g h f hf c
  have hbound : P202.CompleteExponentialData.lengthDistance h (d a) (d b) ≤
      P202.CurveData.length h d :=
    csInf_le (P202.Geometry.LengthDistance.pathLengths_bddBelow h _ _)
      ⟨a, b, d, rfl, rfl, rfl⟩
  rw [hd a, hd b, hc₀, hc₁, hlength] at hbound
  exact hbound

/-- The metric tensor and smooth inverse identify the original intrinsic
length distances in both directions. -/
theorem riemannianIsometry_of_homeomorph_over [ConnectedSpace X] [ConnectedSpace Y]
    (g : RiemannianMetric S) (j : RiemannianMetric Q) (h : RiemannianMetric T)
    {f : X → M} {p : Y → M}
    (hf : IsLocalIsometry g h f) (hp : IsLocalIsometry j h p)
    (e : X ≃ₜ Y) (hover : ∀ x, p (e x) = f x) : IsRiemannianIsometry g j e := by
  obtain ⟨he, hei⟩ := localIsometry_of_homeomorph_over g j h hf hp e hover
  obtain ⟨hei', _⟩ := localIsometry_of_homeomorph_over j g h hp hf e.symm
    (fun y => (hover (e.symm y)).symm.trans (congrArg p (e.apply_symm_apply y)))
  refine ⟨he, hei, fun x y => le_antisymm (localIsometry_distance_le g j he x y) ?_⟩
  simpa only [e.symm_apply_apply] using localIsometry_distance_le j g hei' (e x) (e y)

end SmoothComparison

/-- On equal-dimensional tangent spaces the original positive definite
metrics always admit linear metric isometries. -/
theorem tangent_metric_isometry {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) (h : RiemannianMetric T) (x : X) (y : M) :
    ∃ A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y,
      ∀ v w, pairing h y (A v) (A w) = pairing g x v w := by
  classical
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g x
  obtain ⟨J, hJ⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist h y
  let A := E.trans J.symm
  refine ⟨A, fun v w => ?_⟩
  have hg := SmoothMetrics.bilinear_coordinates E (g.form x) v w
  have hh := SmoothMetrics.bilinear_coordinates J (h.form y) (A v) (A w)
  have hcoords (z : TangentSpace S x) : J (A z) = E z := J.apply_symm_apply _
  simp_rw [show ∀ i j, g.form x (E.symm (Pi.single i 1))
    (E.symm (Pi.single j 1)) = if i = j then 1 else 0 from hE] at hg
  simp_rw [show ∀ i j, h.form y (J.symm (Pi.single i 1))
    (J.symm (Pi.single j 1)) = if i = j then 1 else 0 from hJ] at hh
  simp only [hcoords] at hh
  exact hh.trans hg.symm

/-- A homeomorphism is a one-sheeted covering, with the source convention. -/
theorem homeomorph_covering {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M] (e : X ≃ₜ M) : Covering e := by
  let s : CoveringSheet e univ := ⟨e.toOpenPartialHomeomorph, rfl, rfl⟩
  refine ⟨e.surjective, fun x => ⟨univ, mem_univ x, isOpen_univ, {s}, ?_, ?_⟩⟩
  · simp
  · simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left, Set.preimage_univ]
    rfl

/-- The identity map preserves the actual Riemannian metric. -/
theorem localIsometry_id {n : ℕ} {M : Type u} [TopologicalSpace M]
    {T : SmoothManifold n .euclidean M} (h : RiemannianMetric T) :
    IsLocalIsometry h h id := by
  exact ⟨SmoothManifolds.Tensors.isLocalDiffeomorphism_id T,
    fun _ => LinearMap.id, SmoothManifolds.differential_id T, fun _ _ _ => rfl⟩

/-- Composition preserves the intrinsic local-isometry predicate. -/
theorem localIsometry_comp {n : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    {S : SmoothManifold n .euclidean X} {Q : SmoothManifold n .euclidean Y}
    {T : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) (j : RiemannianMetric Q) (h : RiemannianMetric T)
    {f : X → Y} {p : Y → M} (hf : IsLocalIsometry g j f)
    (hp : IsLocalIsometry j h p) : IsLocalIsometry g h (p ∘ f) := by
  obtain ⟨Lf, hLf, hmLf⟩ := hf.2
  obtain ⟨Lp, hLp, hmLp⟩ := hp.2
  refine ⟨SmoothManifolds.Tensors.isLocalDiffeomorphism_comp S Q T f p hf.1 hp.1,
    fun x => (Lp (f x)).comp (Lf x), fun x => ?_, fun x v w => ?_⟩
  · exact SmoothManifolds.differential_comp S Q T f p hf.1.1 hp.1.1
      x (Lf x) (Lp (f x)) (hLf x) (hLp (f x))
  · exact (hmLp (f x) (Lf x v) (Lf x w)).trans (hmLf x v w)

open private transportManifold from
  MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.QuotientBundles

/-- A homeomorphism transports the smooth structure and admits the pullback
metric. Both its directions are smooth for the original topologies. -/
theorem geometry_of_homeomorph {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    (T : SmoothManifold n .euclidean M) (h : RiemannianMetric T) (e : X ≃ₜ M) :
    ∃ Q : SmoothManifold n .euclidean X, ∃ j : RiemannianMetric Q,
      IsLocalIsometry j h e ∧ IsSmoothMap T Q e.symm := by
  let Q := transportManifold T e.symm
  have hmaps := SmoothManifolds.transportAtlas_maps (⊤ : ℕ∞)
    T.smoothStructure.val e.symm T.smoothStructure.property.1
  have he : IsSmoothMap Q T e := by
    simpa only [Q, transportManifold, IsSmoothMap, Homeomorph.symm_symm] using hmaps.2
  have hei : IsSmoothMap T Q e.symm := hmaps.1
  have hl : SmoothManifolds.TensorData.IsLocalDiffeomorphism Q T e :=
    ⟨he, fun x => ⟨e.symm, hei (e x), e.symm_apply_apply x,
      Filter.Eventually.of_forall e.symm_apply_apply,
      Filter.Eventually.of_forall e.apply_symm_apply⟩⟩
  obtain ⟨j, hj, _⟩ := CoveringMetricCompleteness.pullback_metric Q T e
    ⟨homeomorph_covering e, hl⟩ h
  exact ⟨Q, j, hj, hei⟩

/-- Every complete Riemannian universal covering already has all of the
classification's global conclusions. This separates the global topological
and metric argument from the choice of a concrete curvature model. -/
theorem classification_of_covering {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    [SimplyConnectedSpace X] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : X → M)
    (hi : IsLocalIsometry g h f) (hc : Covering f)
    (hh : LengthMetricComplete h) : Classification S T g h f := by
  letI : LocallyPathConnectedSpace M := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace T.topologicalManifold
  let F : C(X, M) := ⟨f, continuous_iff_continuousAt.mpr fun x => (hi.1.1 x).1⟩
  have hF : Covering F := hc
  refine {
    localIsometry := hi
    covering := hc
    canonicalAtlas := ?_
    deckIsometries := ?_
    free := fun D x hx => deck_free F hF D x hx
    properlyDiscontinuous := fun x => deck_properlyDiscontinuous F hF x
    fibers := fun x y => universalCover_fibers F hF x y
    quotient := ?_
    universal := ?_
    simplyConnected := ?_ }
  · obtain ⟨_, _, Q, hQ, _, _, huniq⟩ := CoveringMetricCompleteness.canonical_geometry T h f hc
    exact (congrArg Subtype.val (huniq S ⟨hc, hi.1⟩)).trans hQ
  · intro D
    exact riemannianIsometry_of_homeomorph_over g g h hi hi D.val
      (fun x => congrFun D.property x)
  · obtain ⟨e, he⟩ := universalCover_quotient F hF
    obtain ⟨Q, j, hje, _⟩ := geometry_of_homeomorph T h e
    letI : ConnectedSpace (DeckQuotient f) :=
      e.symm.surjective.connectedSpace e.symm.continuous
    have heiso := riemannianIsometry_of_homeomorph_over j h h hje (localIsometry_id h)
      e (fun _ => rfl)
    have heinv := (localIsometry_of_homeomorph_over h j h (localIsometry_id h) hje
      e.symm (fun y => e.apply_symm_apply y)).1
    refine ⟨e, he, Q, j, heiso, ?_⟩
    have hcompose := localIsometry_comp g h j hi heinv
    have he' : ∀ x, e (Quotient.mk (MulAction.orbitRel (DeckGroup f) X) x) = f x := he
    have heq : e.symm ∘ f = Quotient.mk (MulAction.orbitRel (DeckGroup f) X) := by
      funext x
      exact (congrArg e.symm (he' x)).symm.trans (e.symm_apply_apply _)
    rwa [heq] at hcompose
  · intro U _ _ p hp
    obtain ⟨Q, hQ, _, j, hji, hj⟩ := CoveringMetricCompleteness.canonical_complete_geometry
      T h p hp ((CoveringMetricCompleteness.connected_complete_iff h).mpr hh)
    have hjcomplete : LengthMetricComplete j :=
      (CoveringMetricCompleteness.connected_complete_iff j).mp hj
    let P : C(U, M) := ⟨p, P202.Topology.coveringContinuous U M p hp⟩
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy⟩ := hp.1 (f x)
    obtain ⟨e, _, he⟩ := universalCoverHomeomorph F P hF hp x y hy.symm
    exact ⟨Q, hQ, j, hji, hjcomplete, e, he,
      riemannianIsometry_of_homeomorph_over g j h hi hji e he⟩
  · intro hsimply
    letI := hsimply
    have hid : Covering (ContinuousMap.id M) := homeomorph_covering (Homeomorph.refl M)
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨e, _, he⟩ := universalCoverHomeomorph F (ContinuousMap.id M) hF hid x (f x) rfl
    exact ⟨e, he, riemannianIsometry_of_homeomorph_over g h h hi (localIsometry_id h) e he⟩

/-- Reflexive identification uses the original differential and distance. -/
def crossIsometry_refl {n : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X) (g : RiemannianMetric S) :
    CrossIsometry S S g g where
  homeomorph := Homeomorph.refl X
  smooth := (localIsometry_id g).1.1
  smooth_inverse := (localIsometry_id g).1.1
  linear _ := LinearMap.id
  differential := SmoothManifolds.differential_id S
  preserves _ _ _ := rfl
  distance _ _ := rfl

/-- Choose the literal standard model and develop it into the complete target.
The supplied globalization theorem is specialized only to its actual model sources. -/
theorem literalModel_development {n : ℕ} (hn : 2 ≤ n) {M : Type}
    [TopologicalSpace M] [ConnectedSpace M]
    (T : SmoothManifold n .euclidean M) (h : RiemannianMetric T)
    (D : Connection (tangentBundle T)) (hD : IsLeviCivita h D)
    (Q : CurvatureTensor T) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hk : ConstantSectional h Q k) (hh : LengthMetricComplete h) :
    ∃ (X : Type) (t : TopologicalSpace X) (S : SmoothManifold n .euclidean X)
      (g : RiemannianMetric S), SimplyConnectedSpace X ∧
      LengthMetricComplete g ∧ IsStandardModel S g k ∧
      ∃ f : X → M, IsLocalIsometry g h f := by
  classical
  have develop {X : Type} [TopologicalSpace X] [Nonempty X]
      (S : SmoothManifold n .euclidean X) (g : RiemannianMetric S)
      (hd : P202Specs.Geometry.GlobalSpaceFormDevelopment.developmentFromType S g k) :
      ∃ f : X → M, IsLocalIsometry g h f := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y⟩ := (inferInstance : Nonempty M)
    obtain ⟨A, hA⟩ := tangent_metric_isometry g h x y
    obtain ⟨f, hf, _⟩ := hd T h D hD Q hQ hk hh x y A hA
    exact ⟨f, (localIsometryOn_univ_iff g h f).mp hf⟩
  rcases lt_trichotomy k 0 with hkneg | hkzero | hkpos
  · let a : ℝ := 1 / Real.sqrt (-k)
    have ha : 0 < a := one_div_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr hkneg))
    obtain ⟨S, hchart, g, hg, _, C, hC, _, _, _, _, hcomplete⟩ :=
      HyperboloidModel.intrinsic_model n hn a ha
    have hs : SimplyConnectedSpace (P202.HyperboloidData.Hyperboloid n a) :=
      (HyperboloidModel.topology n a ha).2
    letI := hs
    obtain ⟨c, hc, hsource, htarget, hproj, _⟩ := hchart
    have hchart' : P202.ModelPolarData.HasProjectionChart S :=
      ⟨c, hc, hsource, htarget, hproj⟩
    have hd : P202Specs.Geometry.GlobalSpaceFormDevelopment.developmentFromType S g k :=
      GlobalSpaceFormDevelopment.hyperbolic_development n hn k hkneg S g hchart' hg
    obtain ⟨f, hf⟩ := develop S g hd
    refine ⟨P202.HyperboloidData.Hyperboloid n a, inferInstance, S, g,
      hs, hcomplete, ?_, f, hf⟩
    exact Or.inr (Or.inr ⟨hkneg, S, g, hchart', hg, ⟨crossIsometry_refl S g⟩⟩)
  · subst k
    obtain ⟨G, _, _, hG, _, _⟩ := EuclideanSphericalModels.models n hn 1 zero_lt_one
    letI : SimplyConnectedSpace (P202.SpaceFormData.E n) := hG.2.1
    have hd : P202Specs.Geometry.GlobalSpaceFormDevelopment.developmentFromType
        G.manifold G.metric 0 :=
      GlobalSpaceFormDevelopment.euclidean_development n hn G hG
    obtain ⟨f, hf⟩ := develop G.manifold G.metric hd
    exact ⟨P202.SpaceFormData.E n, inferInstance, G.manifold, G.metric,
      hG.2.1, hG.2.2.1, Or.inl ⟨rfl, G, ⟨crossIsometry_refl G.manifold G.metric⟩⟩,
      f, hf⟩
  · let a : ℝ := 1 / Real.sqrt k
    have ha : 0 < a := one_div_pos.mpr (Real.sqrt_pos.mpr hkpos)
    obtain ⟨_, A, B, _, _, hB⟩ := EuclideanSphericalModels.models n hn a ha
    letI : SimplyConnectedSpace (P202.SpaceFormData.Sphere n a) := hB.2.1
    have hd : P202Specs.Geometry.GlobalSpaceFormDevelopment.developmentFromType
        B.manifold B.metric k :=
      GlobalSpaceFormDevelopment.spherical_development n hn k hkpos A B hB
    obtain ⟨f, hf⟩ := develop B.manifold B.metric hd
    exact ⟨P202.SpaceFormData.Sphere n a, inferInstance, B.manifold, B.metric,
      hB.2.1, hB.2.2.1,
      Or.inr (Or.inl ⟨hkpos, A, B, ⟨crossIsometry_refl B.manifold B.metric⟩⟩), f, hf⟩

set_option maxHeartbeats 2400000 in
/-- Concrete standard models with all input geometry needed by development.
This lemma is at universe zero because the supplied literal models are. It is
not a substitute for transporting them to the arbitrary universe of the target. -/
theorem standardModel_exists (n : ℕ) (hn : 2 ≤ n) (k : ℝ) :
    ∃ (X : Type) (t : TopologicalSpace X) (S : SmoothManifold n .euclidean X)
      (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S),
      SimplyConnectedSpace X ∧ IsLeviCivita g C ∧ RepresentsCurvature C R ∧
      ConstantSectional g R k ∧ LengthMetricComplete g ∧ IsStandardModel S g k := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · let a : ℝ := 1 / Real.sqrt (-k)
    have ha : 0 < a := one_div_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr hk))
    obtain ⟨S, hchart, g, hg, _, C, hC, hformula, _, _, _, hcomplete⟩ :=
      HyperboloidModel.intrinsic_model n hn a ha
    obtain ⟨c, hc, hs, ht, hproj, _⟩ := hchart
    obtain ⟨R, hR, _⟩ := CurvatureAlgebra.tensor_exists_unique C
    have hRfull : ∀ p v w z, R.val p v w z =
        (-(a ^ 2)⁻¹) • (pairing g p w z • v - pairing g p v z • w) := by
      intro p v w z
      have hr := hR (CurvatureAlgebra.fieldLift p v) (CurvatureAlgebra.fieldLift p w)
        (CurvatureAlgebra.fieldLift p z) p
      have hf := hformula (CurvatureAlgebra.fieldLift p v) (CurvatureAlgebra.fieldLift p w)
        (CurvatureAlgebra.fieldLift p z) p
      simpa only [CurvatureAlgebra.fieldLift_value] using hr.trans hf
    have hvalue : -(a ^ 2)⁻¹ = k := by
      simp only [a, one_div, inv_pow, inv_inv, Real.sq_sqrt (le_of_lt (neg_pos.mpr hk)), neg_neg]
    have hconstant : ConstantSectional g R k := by
      intro p v w hi
      exact (EuclideanSphericalModels.sectionalCurvature_of_round_formula g R
        (-(a ^ 2)⁻¹) hRfull p v w hi).trans hvalue
    refine ⟨P202.HyperboloidData.Hyperboloid n a, inferInstance, S, g, C, R,
      (HyperboloidModel.topology n a ha).2, hC, hR, hconstant, hcomplete, ?_⟩
    exact Or.inr (Or.inr ⟨hk, S, g, ⟨c, hc, hs, ht, hproj⟩, hg,
      ⟨crossIsometry_refl S g⟩⟩)
  · subst k
    obtain ⟨G, _, _, hG, _, _⟩ := EuclideanSphericalModels.models n hn 1 zero_lt_one
    obtain ⟨R, hR, hconstant⟩ := hG.2.2.2.1
    exact ⟨P202.SpaceFormData.E n, inferInstance, G.manifold, G.metric, G.connection, R,
      hG.2.1, G.leviCivita, hR, hconstant, hG.2.2.1,
      Or.inl ⟨rfl, G, ⟨crossIsometry_refl G.manifold G.metric⟩⟩⟩
  · let a : ℝ := 1 / Real.sqrt k
    have ha : 0 < a := one_div_pos.mpr (Real.sqrt_pos.mpr hk)
    obtain ⟨_, A, B, _, _, hB⟩ := EuclideanSphericalModels.models n hn a ha
    obtain ⟨R, hR, hsection⟩ := hB.2.2.2.1
    have hvalue : (a ^ 2)⁻¹ = k := by
      simp only [a, one_div, inv_pow, inv_inv, Real.sq_sqrt hk.le]
    have hconstant : ConstantSectional B.metric R k := by
      intro p v w hi
      exact (hsection p v w hi).trans hvalue
    exact ⟨P202.SpaceFormData.Sphere n a, inferInstance, B.manifold, B.metric, B.connection, R,
      hB.2.1, B.leviCivita, hR, hconstant, hB.2.2.1,
      Or.inr (Or.inl ⟨hk, A, B, ⟨crossIsometry_refl B.manifold B.metric⟩⟩)⟩

end P202.Geometry.KillingHopf


/-! Transport of the actual standard models across universes. The germ
construction below extends the shared intrinsic differential to different
universes; all metric, connection, curvature and length laws are proved. -/
namespace P202.Geometry.KillingHopf.Transport
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.PartitionData SmoothManifolds.TangentData
open Set Filter
open scoped _root_.Topology
universe u v

theorem scalar_comp_at {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {f : M → N} {r : N → ℝ} {p : M}
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p)
    (hr : ScalarContDiffAt (⊤ : ℕ∞) T.smoothStructure.val r (f p)) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (r ∘ f) p := by
  refine ⟨hr.1.comp hf.1, ?_⟩
  intro e he hp
  obtain ⟨d, hd, hdp⟩ := T.smoothStructure.property.1.1 (f p)
  exact SmoothManifolds.LocalCoordinateExtension.comp
    (SmoothManifolds.LocalCoordinateExtension.precomp (hr.2 d hd hdp) hf.1 rfl)
    (hf.2 e he d hd hp hdp)

def germPullbackRaw {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (f : M → N) (p : M) (hf : ContinuousAt f p) :
    Germ (𝓝 (f p)) ℝ →ₐ[ℝ] Germ (𝓝 p) ℝ where
  toFun h := h.compTendsto f hf
  map_zero' := rfl
  map_one' := rfl
  map_add' h k := by
    induction h using Germ.inductionOn with | _ r =>
      induction k using Germ.inductionOn with | _ s => rfl
  map_mul' h k := by
    induction h using Germ.inductionOn with | _ r =>
      induction k using Germ.inductionOn with | _ s => rfl
  commutes' _ := rfl

def smoothGermPullback
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    SmoothGerm T (f p) →ₐ[ℝ] SmoothGerm S p where
  toFun h := ⟨germPullbackRaw f p (hf p).1 h.val, by
    obtain ⟨r, hr, he⟩ := (SmoothManifolds.mem_smoothGermAlgebra_iff T (f p) h.val).mp h.property
    rw [he]
    exact Algebra.subset_adjoin ⟨r ∘ f, scalar_comp_at (hf p) hr, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (germPullbackRaw f p (hf p).1))
  map_one' := Subtype.ext (map_one (germPullbackRaw f p (hf p).1))
  map_add' h k := Subtype.ext (map_add (germPullbackRaw f p (hf p).1) h.val k.val)
  map_mul' h k := Subtype.ext (map_mul (germPullbackRaw f p (hf p).1) h.val k.val)
  commutes' r := Subtype.ext ((germPullbackRaw f p (hf p).1).commutes r)

theorem smoothGermPullback_rep
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M)
    (h : SmoothGerm T (f p)) (r : N → ℝ) (hr : Germ.ofFun r = h.val) :
    (smoothGermPullback S T f hf p h).val = Germ.ofFun (r ∘ f) := by
  change germPullbackRaw f p (hf p).1 h.val = _
  rw [← hr]
  rfl

def tangentPush
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    TangentSpace S p →ₗ[ℝ] TangentSpace T (f p) where
  toFun v := ⟨v.val.comp (smoothGermPullback S T f hf p).toLinearMap, by
    intro h k
    change v.val (smoothGermPullback S T f hf p (h * k)) = _
    rw [map_mul, v.property]
    have heval (j : SmoothGerm T (f p)) :
        germEvaluation S p (smoothGermPullback S T f hf p j) =
          germEvaluation T (f p) j := by
      change (germPullbackRaw f p (hf p).1 j.val).value = j.val.value
      induction j.val using Germ.inductionOn with | _ r => rfl
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, heval]⟩
  map_add' v w := by
    apply Subtype.ext
    apply LinearMap.ext
    intro h
    rfl
  map_smul' r v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro h
    rfl

theorem tangentPush_spec
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    ∀ (v : TangentSpace S p) (h : SmoothGerm T (f p)) (k : SmoothGerm S p) (r : N → ℝ),
      Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val →
        (tangentPush S T f hf p v).val h = v.val k := by
  intro v h k r hr hk
  change v.val (smoothGermPullback S T f hf p h) = v.val k
  congr 1
  exact Subtype.ext ((smoothGermPullback_rep S T f hf p h r hr).trans hk)


open SmoothManifolds.DifferentialData
universe w

def CrossDifferential
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (p : M) (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) : Prop :=
  ∀ (v : TangentSpace S p) (h : SmoothGerm T (f p)) (k : SmoothGerm S p)
    (r : N → ℝ), Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val →
      (L v).val h = v.val k

theorem crossDifferential_unique
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M)
    (L K : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : CrossDifferential S T f p L) (hK : CrossDifferential S T f p K) : L = K := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply LinearMap.ext
  intro h
  obtain ⟨r, _, hr⟩ := (SmoothManifolds.mem_smoothGermAlgebra_iff T (f p) h.val).mp h.property
  let k := smoothGermPullback S T f hf p h
  have hk := (smoothGermPullback_rep S T f hf p h r hr.symm).symm
  exact (hL v h k r hr.symm hk).trans (hK v h k r hr.symm hk).symm

theorem crossDifferential_comp
    {n m l : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {Q : Type w}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (U : SmoothManifold l c Q)
    (f : M → N) (g : N → Q) (hf : IsSmoothMap S T f) (hg : IsSmoothMap T U g)
    (p : M) (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (K : TangentSpace T (f p) →ₗ[ℝ] TangentSpace U (g (f p)))
    (hL : CrossDifferential S T f p L) (hK : CrossDifferential T U g (f p) K) :
    CrossDifferential S U (g ∘ f) p (K.comp L) := by
  intro v h k r hr hk
  let j := smoothGermPullback T U g hg (f p) h
  have hj := (smoothGermPullback_rep T U g hg (f p) h r hr).symm
  exact (hK (L v) h j r hr hj).trans (hL v j k (r ∘ g) hj hk)

theorem crossDifferential_jacobian
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : CrossDifferential S T f p L)
    (e : ModelChart n a M) (d : ModelChart m b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ e.source) (hfp : f p ∈ d.source)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (F : TangentSpace T (f p) ≃ₗ[ℝ] Euclidean m)
    (hE : IsChartCoordinates S p e E) (hF : IsChartCoordinates T (f p) d F)
    (V : Set (Euclidean n)) (H : Euclidean n → Euclidean m)
    (hV : IsOpen V) (hpV : (e p).val ∈ V) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H V)
    (heH : (fun y => H (e y).val) =ᶠ[𝓝 p] (fun y => (d (f y)).val))
    (v : TangentSpace S p) : F (L v) = fderiv ℝ H (e p).val (E v) := by
  obtain ⟨xs, bs, ES, hxs, hES, _, hformula⟩ :=
    SmoothManifolds.coordinate_tangent_model S p e he hp
  obtain ⟨xs', hxs', hE⟩ := hE
  obtain ⟨ys, hys, hF⟩ := hF
  have hsame (i : Fin n) : xs i = xs' i :=
    Subtype.ext ((hxs i).trans (hxs' i).symm)
  have hv : E v = ∑ i, (v.val (xs i)) • Pi.single i (1 : ℝ) := by
    ext j
    simp [hE, hsame, Pi.single_apply]
  have hHd : DifferentiableAt ℝ H (e p).val :=
    (hH.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  ext j
  let k := smoothGermPullback S T f hf p (ys j)
  have hk : Germ.ofFun ((fun z => (d z).val j) ∘ f) = k.val :=
    (smoothGermPullback_rep S T f hf p (ys j) _ (hys j).symm).symm
  have hkH : GermChartExtension S p e k (fun z => H z j) := by
    refine ⟨⟨V, hV, hpV, (contDiffOn_pi.mp hH) j⟩, ?_⟩
    exact (Germ.coe_eq.mpr (heH.mono (fun _ hy => congrFun hy j))).trans hk
  calc
    F (L v) j = (L v).val (ys j) := hF _ _
    _ = v.val k := hL v (ys j) k _ (hys j).symm hk
    _ = ∑ i, v.val (xs i) * fderiv ℝ (fun z => H z j) (e p).val (Pi.single i 1) :=
      hformula v k _ hkH
    _ = fderiv ℝ (fun z => H z j) (e p).val (E v) := by
      rw [hv, map_sum]
      simp only [map_smul, smul_eq_mul]
    _ = (fderiv ℝ H (e p).val (E v)) j := by
      rw [fderiv_apply hHd]
      rfl


def germPushRaw {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (p : M) : Germ (𝓝 p) ℝ →ₐ[ℝ] Germ (𝓝 (e p)) ℝ where
  toFun h := h.compTendsto e.symm (by simpa only [e.symm_apply_apply] using (e.symm.continuous.continuousAt (x := e p)).tendsto)
  map_zero' := rfl
  map_one' := rfl
  map_add' h k := by
    induction h using Germ.inductionOn with | _ r =>
      induction k using Germ.inductionOn with | _ s => rfl
  map_mul' h k := by
    induction h using Germ.inductionOn with | _ r =>
      induction k using Germ.inductionOn with | _ s => rfl
  commutes' _ := rfl

def smoothGermPush
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (e : M ≃ₜ N) (he : IsSmoothMap T S e.symm) (p : M) :
    SmoothGerm S p →ₐ[ℝ] SmoothGerm T (e p) where
  toFun h := ⟨germPushRaw e p h.val, by
    obtain ⟨r, hr, hrep⟩ := (SmoothManifolds.mem_smoothGermAlgebra_iff S p h.val).mp h.property
    rw [hrep]
    exact Algebra.subset_adjoin ⟨r ∘ e.symm, scalar_comp_at (he (e p))
      (by simpa only [e.symm_apply_apply] using hr), rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (germPushRaw e p))
  map_one' := Subtype.ext (map_one (germPushRaw e p))
  map_add' h k := Subtype.ext (map_add (germPushRaw e p) h.val k.val)
  map_mul' h k := Subtype.ext (map_mul (germPushRaw e p) h.val k.val)
  commutes' r := Subtype.ext ((germPushRaw e p).commutes r)

def smoothGermEquiv
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (e : M ≃ₜ N) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm) (p : M) :
    SmoothGerm T (e p) ≃ₐ[ℝ] SmoothGerm S p where
  __ := smoothGermPullback S T e he p
  invFun := smoothGermPush S T e hi p
  left_inv h := by
    apply Subtype.ext
    change germPushRaw e p (germPullbackRaw e p _ h.val) = h.val
    induction h.val using Germ.inductionOn with | _ r =>
      change Germ.ofFun ((r ∘ e) ∘ e.symm) = Germ.ofFun r
      congr 1
      funext y
      simp
  right_inv h := by
    apply Subtype.ext
    change germPullbackRaw e p _ (germPushRaw e p h.val) = h.val
    induction h.val using Germ.inductionOn with | _ r =>
      change Germ.ofFun ((r ∘ e.symm) ∘ e) = Germ.ofFun r
      congr 1
      funext y
      simp

def tangentEquiv
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (e : M ≃ₜ N) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm) (p : M) :
    TangentSpace S p ≃ₗ[ℝ] TangentSpace T (e p) where
  __ := tangentPush S T e he p
  invFun w := ⟨w.val.comp (smoothGermEquiv S T e he hi p).symm.toLinearMap, by
    intro h k
    change w.val ((smoothGermEquiv S T e he hi p).symm (h * k)) = _
    rw [map_mul, w.property]
    have heval (j : SmoothGerm S p) :
        germEvaluation T (e p) ((smoothGermEquiv S T e he hi p).symm j) =
          germEvaluation S p j := by
      change (germPushRaw e p j.val).value = j.val.value
      induction j.val using Germ.inductionOn with | _ r =>
        change r (e.symm (e p)) = r p
        rw [e.symm_apply_apply]
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, heval]⟩
  left_inv v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro h
    change v.val ((smoothGermEquiv S T e he hi p) ((smoothGermEquiv S T e he hi p).symm h)) = v.val h
    rw [AlgEquiv.apply_symm_apply]
  right_inv w := by
    apply Subtype.ext
    apply LinearMap.ext
    intro h
    change w.val ((smoothGermEquiv S T e he hi p).symm ((smoothGermEquiv S T e he hi p) h)) = w.val h
    rw [AlgEquiv.symm_apply_apply]

@[simp] theorem tangentEquiv_toLinearMap
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (e : M ≃ₜ N) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm) (p : M) :
    (tangentEquiv S T e he hi p).toLinearMap = tangentPush S T e he p := rfl



open P202.MetricData
open P202.Geometry.PiecewiseCurves

theorem cross_hasVelocityAt_postcomp
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N} {f : M → N}
    (hf : IsSmoothMap S T f) {c : ℝ → M} {t : ℝ}
    {v : TangentSpace S (c t)} (hv : HasVelocityAt S c t v)
    (L : TangentSpace S (c t) →ₗ[ℝ] TangentSpace T (f (c t)))
    (hL : CrossDifferential S T f (c t) L) :
    HasVelocityAt T (f ∘ c) t (L v) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c t)
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f (c t))
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := (hf (c t)).2 e he d hd hp hpd
  have hj := crossDifferential_jacobian S T f hf (c t) L hL
    e d he hd hp hpd
    ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp)
    ((tangentStructure T).fiberCoordinates.equiv d hd (f (c t)) hpd)
    ((tangentStructure S).fiberCoordinates.isCoordinates e he (c t) hp)
    ((tangentStructure T).fiberCoordinates.isCoordinates d hd (f (c t)) hpd)
    U F hU hpU hF hrep v
  refine ⟨(hf (c t)).1.comp hv.1, d, hd, hpd, ?_⟩
  change HasDerivAt (fun s => (d (f (c s))).val)
    (((tangentStructure T).fiberCoordinates.equiv d hd (f (c t)) hpd) (L v)) t
  rw [hj]
  exact ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt t (hasVelocityAt_coordinates hv e he hp)
    |>.congr_of_eventuallyEq (hrep.comp_tendsto hv.1).symm

end P202.Geometry.KillingHopf.Transport

namespace P202.Geometry.KillingHopf.Transport
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData P202.MetricData
open Set Filter
open scoped _root_.Topology
universe u v

def tangentCast
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {p q : M} (hpq : p = q) :
    TangentSpace S p ≃ₗ[ℝ] TangentSpace S q := by
  subst q
  exact LinearEquiv.refl ℝ _

def germCast
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {p q : M} (hpq : p = q) :
    SmoothGerm S p ≃ₐ[ℝ] SmoothGerm S q := by
  subst q
  exact AlgEquiv.refl

theorem tangentCast_val
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {p q : M} (hpq : p = q)
    (v : TangentSpace S p) (a : SmoothGerm S q) :
    (tangentCast S hpq v).val a = v.val (germCast S hpq.symm a) := by
  subst q
  rfl

theorem germCast_rep
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {p q : M} (hpq : p = q)
    (a : SmoothGerm S p) (r : M → ℝ) (hr : Germ.ofFun r = a.val) :
    Germ.ofFun r = (germCast S hpq a).val := by
  subst q
  exact hr

theorem pairing_tangentCast
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) {p q : M} (hpq : p = q)
    (v w : TangentSpace S p) :
    pairing g q (tangentCast S hpq v) (tangentCast S hpq w) = pairing g p v w := by
  subst q
  rfl

theorem cross_forward_inverse
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (e : M ≃ₜ N) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (e p))
    (hL : ∀ p, CrossDifferential S T e p (L p))
    (y : N) (v : TangentSpace T y) :
    tangentCast T (e.apply_symm_apply y)
      (L (e.symm y) (tangentPush T S e.symm hi y v)) = v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro h
  rw [tangentCast_val]
  obtain ⟨r, _, hr⟩ := (SmoothManifolds.mem_smoothGermAlgebra_iff T y h.val).mp h.property
  let h' := germCast T (e.apply_symm_apply y).symm h
  have hr' : Germ.ofFun r = h'.val := germCast_rep T _ h r hr.symm
  let k := smoothGermPullback S T e he (e.symm y) h'
  have hk : Germ.ofFun (r ∘ e) = k.val :=
    (smoothGermPullback_rep S T e he (e.symm y) h' r hr').symm
  have hcomp : Germ.ofFun ((r ∘ e) ∘ e.symm) = h.val := by
    convert hr.symm using 1
    congr 1
    funext z
    simp
  exact (hL (e.symm y) (tangentPush T S e.symm hi y v) h' k r hr' hk).trans
    (tangentPush_spec T S e.symm hi y v k h (r ∘ e) hk hcomp)

theorem cross_inverse_metric_preserving
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (e : M ≃ₜ N) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (e p))
    (hL : ∀ p, CrossDifferential S T e p (L p))
    (hpres : ∀ x v w, pairing h (e x) (L x v) (L x w) = pairing g x v w) :
    ∀ y v w, pairing g (e.symm y) (tangentPush T S e.symm hi y v)
      (tangentPush T S e.symm hi y w) = pairing h y v w := by
  intro y v w
  calc
    pairing g (e.symm y) (tangentPush T S e.symm hi y v) (tangentPush T S e.symm hi y w) =
        pairing h (e (e.symm y))
          (L (e.symm y) (tangentPush T S e.symm hi y v))
          (L (e.symm y) (tangentPush T S e.symm hi y w)) := (hpres _ _ _).symm
    _ = pairing h y
          (tangentCast T (e.apply_symm_apply y) (L (e.symm y) (tangentPush T S e.symm hi y v)))
          (tangentCast T (e.apply_symm_apply y) (L (e.symm y) (tangentPush T S e.symm hi y w))) :=
      (pairing_tangentCast h (e.apply_symm_apply y) _ _).symm
    _ = pairing h y v w := by
      rw [cross_forward_inverse e he hi L hL y v, cross_forward_inverse e he hi L hL y w]
end P202.Geometry.KillingHopf.Transport
namespace P202.Geometry.KillingHopf.Transport
open SmoothManifolds (ModelKind manifoldContDiff_comp)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.ProductData SmoothManifolds.BoundaryData
  SmoothManifolds.TangentBundleData SmoothManifolds.TangentBundle
open Set Filter
open scoped _root_.Topology
universe u v

theorem cross_totalMap_smooth_of_jacobian
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (B : TangentBundleStructure S) (D : TangentBundleStructure T)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ (p : M)
      (e : ModelChart n a M) (d : ModelChart m b N)
      (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
      (hp : p ∈ e.source) (hfp : f p ∈ d.source)
      (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (F : TangentSpace T (f p) ≃ₗ[ℝ] Euclidean m),
      IsChartCoordinates S p e E → IsChartCoordinates T (f p) d F →
      ∀ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean m),
        IsOpen V → (e p).val ∈ V → ContDiffOn ℝ (⊤ : ℕ∞) H V →
        (fun y => H (e y).val) =ᶠ[𝓝 p] (fun y => (d (f y)).val) →
        ∀ v : TangentSpace S p, F (L p v) = fderiv ℝ H (e p).val (E v)) :
    letI := B.topology
    letI := D.topology
    IsSmoothMap B.manifold D.manifold (fun y => ⟨f y.1, L y.1 y.2⟩) := by
  letI := B.topology
  letI := D.topology
  intro z
  obtain ⟨e, he, hz⟩ := S.smoothStructure.property.1.1 z.1
  obtain ⟨d, hd, hfz⟩ := T.smoothStructure.property.1.1 (f z.1)
  obtain ⟨U, hU, hzU, F, hF, hFeq⟩ := (hf z.1).2 e he d hd hz hfz
  obtain ⟨V, hVeq, hV, hzV⟩ := mem_nhds_iff.mp hFeq
  have hπ := projection_smooth S B
  have hp := manifoldContDiff_comp (⊤ : ℕ∞) B.manifold.smoothStructure.val
    S.smoothStructure.val T.smoothStructure.val S.smoothStructure.property.1.1
    (SmoothManifolds.TangentBundleData.projection S) f hπ hf
  let w : TotalSpace S → Euclidean m := fun y =>
    fderiv ℝ F (e y.1).val (chartFiber B e he y)
  have htz : z ∈ (B.chart e he).source := by
    simpa only [B.chart_source, SmoothManifolds.TangentBundleData.projection, mem_preimage] using hz
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
        simpa only [B.chart_source, SmoothManifolds.TangentBundleData.projection, mem_preimage] using hy
      change fderiv ℝ F (B.productCoordinates.linearEquiv.symm ((B.chart e he) y).val).1
        (B.productCoordinates.linearEquiv.symm ((B.chart e he) y).val).2 =
          fderiv ℝ F (e y.1).val (chartFiber B e he y)
      rw [B.chart_apply e he y hye, ContinuousLinearEquiv.symm_apply_apply,
        chartFiber_eq S B e he y hye]
  apply lift_smoothAt_of_coeff T D B.manifold (fun y => ⟨f y.1, L y.1 y.2⟩) z d hd hfz w (hp z) hw
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
  have hj := hL y.1 e d he hd hye hyd
    (B.fiberCoordinates.equiv e he y.1 hye) (D.fiberCoordinates.equiv d hd (f y.1) hyd)
    (B.fiberCoordinates.isCoordinates e he y.1 hye)
    (D.fiberCoordinates.isCoordinates d hd (f y.1) hyd) U F hU hyU hF hrep y.2
  change fderiv ℝ F (e y.1).val (chartFiber B e he y) =
    D.fiberCoordinates.equiv d hd (f y.1) hyd (L y.1 y.2)
  rw [chartFiber_eq S B e he y hye]
  exact hj.symm

 theorem cross_totalMap_smooth
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (B : TangentBundleStructure S) (D : TangentBundleStructure T)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, P202.Geometry.KillingHopf.Transport.CrossDifferential S T f p (L p)) :
    letI := B.topology
    letI := D.topology
    IsSmoothMap B.manifold D.manifold (fun y => ⟨f y.1, L y.1 y.2⟩) := by
  apply cross_totalMap_smooth_of_jacobian S T B D f hf L
  intro p
  exact P202.Geometry.KillingHopf.Transport.crossDifferential_jacobian S T f hf p (L p) (hL p)

end P202.Geometry.KillingHopf.Transport
namespace P202.Geometry.KillingHopf
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  SmoothManifolds.FrameData P202.MetricData
open Set Filter
open scoped _root_.Topology
universe u v

/-- The cross-universe differential acts smoothly on the canonical tangent
realizations of both manifolds. -/
theorem cross_differential_totalMap_smooth
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, P202.Geometry.KillingHopf.Transport.CrossDifferential S T f p (L p)) :
    IsSmoothMap (tangentRealization S).space.bundle.totalManifold
      (tangentRealization T).space.bundle.totalManifold
      (fun q => (⟨f q.proj, L q.proj q.snd⟩ :
        Bundle.TotalSpace (Euclidean m) (TangentSpace T))) := by
  letI := (tangentStructure S).topology
  letI := (tangentStructure T).topology
  have hm := P202.Geometry.KillingHopf.Transport.cross_totalMap_smooth S T
    (tangentStructure S) (tangentStructure T) f hf L hL
  have h1 := SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (tangentStructure S).manifold.smoothStructure.property.1.1 _ _
    (tangentRealization S).smooth_to_original hm
  exact SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (tangentStructure T).manifold.smoothStructure.property.1.1 _ _
    h1 (tangentRealization T).smooth_from_original

/-- Pullback of an actual smooth Riemannian metric by an injective intrinsic
differential; the source and target may lie in different universes. -/
def cross_pullbackMetric
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (h : RiemannianMetric T) (f : M → N) (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, P202.Geometry.KillingHopf.Transport.CrossDifferential S T f p (L p))
    (hinj : ∀ p, Function.Injective (L p)) : RiemannianMetric S where
  form p := (h.form (f p)).compl₁₂ (L p) (L p)
  symmetric p v w := h.symmetric (f p) (L p v) (L p w)
  positive p v hv := h.positive (f p) (L p v) (fun hz => hv (hinj p (by simpa using hz)))
  smooth := by
    intro c j k p hp
    let B := (tangentRealization S).space.bundle
    let v : ∀ q, TangentSpace S q :=
      fun q => (B.trivialization c).symm q (Pi.single j 1)
    let w : ∀ q, TangentSpace S q :=
      fun q => (B.trivialization c).symm q (Pi.single k 1)
    have hm := cross_differential_totalMap_smooth f hf L hL
    have hv := SmoothManifolds.manifoldContDiffAt_comp
      B.totalManifold.smoothStructure.property.1.1
      (SmoothMetrics.localFrame_smoothAt c j p hp) (hm ⟨p, v p⟩)
    have hw := SmoothManifolds.manifoldContDiffAt_comp
      B.totalManifold.smoothStructure.property.1.1
      (SmoothMetrics.localFrame_smoothAt c k p hp) (hm ⟨p, w p⟩)
    exact SmoothMetrics.metric_pairing_smoothAt S (tangentRealization T).space.bundle h f
      (fun q => L q (v q)) (fun q => L q (w q)) p (hf p) hv hw

end P202.Geometry.KillingHopf
namespace P202.Geometry.KillingHopf
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData P202.MetricData P202.ConnectionData
open Set Filter
open scoped _root_.Topology
universe u v

def tangent_cast {n : ℕ} {a : SmoothManifolds.ModelKind} {N : Type v}
    [TopologicalSpace N] (T : SmoothManifold n a N) {p q : N} (h : p = q)
    (v : TangentSpace T p) : TangentSpace T q := h ▸ v

@[simp] theorem tangent_cast_self {n : ℕ} {a : SmoothManifolds.ModelKind} {N : Type v}
    [TopologicalSpace N] (T : SmoothManifold n a N) {p : N} (h : p = p)
    (v : TangentSpace T p) : tangent_cast T h v = v := by cases h; rfl

private theorem totalSpace_cast_eq {n : ℕ} {a : SmoothManifolds.ModelKind} {N : Type v}
    [TopologicalSpace N] (T : SmoothManifold n a N) {p q : N} (h : p = q)
    (v : TangentSpace T p) :
    (⟨q, tangent_cast T h v⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace T)) = ⟨p, v⟩ := by
  cases h
  rfl

/-- Push a smooth vector field through a smooth homeomorphism with its actual
cross-universe differential. -/
def cross_pushField
    {n m : ℕ} {a b : SmoothManifolds.ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (e : M ≃ₜ N) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (e p))
    (hL : ∀ p, P202.Geometry.KillingHopf.Transport.CrossDifferential S T e p (L p))
    (X : Field S) : Field T := by
  let V : (q : N) → TangentSpace T q := fun q =>
    tangent_cast T (e.apply_symm_apply q) (L (e.symm q) (X.val (e.symm q)))
  refine ⟨V, ?_⟩
  have hm := cross_differential_totalMap_smooth e he L hL
  have hx : IsSmoothMap S (tangentBundle S).totalManifold
      (fun p => (⟨p, X.val p⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) := X.property
  have hs := SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (tangentBundle S).totalManifold.smoothStructure.property.1.1 _ _ hx hm
  have hpush := SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    S.smoothStructure.property.1.1 _ _ hi hs
  have heq : (fun q => (⟨q, V q⟩ : Bundle.TotalSpace (Euclidean m) (TangentSpace T))) =
      (fun q => (⟨e (e.symm q), L (e.symm q) (X.val (e.symm q))⟩ :
        Bundle.TotalSpace (Euclidean m) (TangentSpace T))) := by
    funext q
    exact totalSpace_cast_eq T (e.apply_symm_apply q) _
  change IsSmoothMap T (tangentBundle T).totalManifold (fun q => ⟨q, V q⟩)
  rw [heq]
  exact hpush

theorem cross_pushField_apply
    {n m : ℕ} {a b : SmoothManifolds.ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (e : M ≃ₜ N) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (e p))
    (hL : ∀ p, P202.Geometry.KillingHopf.Transport.CrossDifferential S T e p (L p))
    (X : Field S) (p : M) :
    L p (X.val p) = (cross_pushField e he hi L hL X).val (e p) := by
  apply Bundle.TotalSpace.mk_injective (e p)
  change (⟨e p, L p (X.val p)⟩ : Bundle.TotalSpace (Euclidean m) (TangentSpace T)) =
    ⟨e p, tangent_cast T (e.apply_symm_apply (e p))
      (L (e.symm (e p)) (X.val (e.symm (e p))))⟩
  rw [totalSpace_cast_eq]
  rw [e.symm_apply_apply]

end P202.Geometry.KillingHopf

set_option maxHeartbeats 1000000
namespace P202.Geometry.KillingHopf.CurvatureTransport
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.PartitionData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.TorsionMetricData
  P202.CurvatureData P202.ConstantCurvaturePolarData
open Set Filter
open scoped _root_.Topology
universe u v

structure FieldTransport {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n .euclidean M) (T : SmoothManifold n .euclidean N) where
  homeomorph : M ≃ₜ N
  smooth : IsSmoothMap S T homeomorph
  linear : (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace T (homeomorph p)
  differential : ∀ (p : M) (v : TangentSpace S p)
    (a : SmoothGerm T (homeomorph p)) (b : SmoothGerm S p) (r : N → ℝ),
    Germ.ofFun r = a.val → Germ.ofFun (r ∘ homeomorph) = b.val →
      (linear p v).val a = v.val b
  fields : Field S → Field T
  fields_apply : ∀ (X : Field S) (p : M), linear p (X.val p) = (fields X).val (homeomorph p)

section
variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n .euclidean M} {T : SmoothManifold n .euclidean N}
  (E : FieldTransport S T)

private theorem scalar_comp_at {r : N → ℝ} {p : M}
    (hr : ScalarContDiffAt (⊤ : ℕ∞) T.smoothStructure.val r (E.homeomorph p)) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (r ∘ E.homeomorph) p := by
  refine ⟨hr.1.comp (E.smooth p).1, ?_⟩
  intro e he hp
  obtain ⟨d, hd, hdp⟩ := T.smoothStructure.property.1.1 (E.homeomorph p)
  exact SmoothManifolds.LocalCoordinateExtension.comp
    (SmoothManifolds.LocalCoordinateExtension.precomp (hr.2 d hd hdp) (E.smooth p).1 rfl)
    ((E.smooth p).2 e he d hd hp hdp)

def composeGlobal (F : GlobalSmooth T) : GlobalSmooth S :=
  ⟨F.val ∘ E.homeomorph, (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr
    (fun p => scalar_comp_at E ((SmoothManifolds.mem_globalSmoothAlgebra_iff T _).mp F.property _))⟩

theorem act_related_at (X : Field S) (X' : Field T) (p : M)
    (hX : E.linear p (X.val p) = X'.val (E.homeomorph p)) (F : GlobalSmooth T) :
    (act S X (composeGlobal E F)).val p = (act T X' F).val (E.homeomorph p) := by
  rw [ConnectionForms.act_apply, ConnectionForms.act_apply, ← hX]
  exact (E.differential p (X.val p) (SmoothManifolds.globalToGerm T (E.homeomorph p) F)
    (SmoothManifolds.globalToGerm S p (composeGlobal E F)) F.val rfl rfl).symm

theorem act_related (X : Field S) (F : GlobalSmooth T) :
    act S X (composeGlobal E F) = composeGlobal E (act T (E.fields X) F) := by
  apply Subtype.ext
  funext p
  exact act_related_at E X (E.fields X) p (E.fields_apply X p) F

theorem bracket_related (X Y : Field S) (p : M) :
    E.linear p ((bracket X Y).val p) = (bracket (E.fields X) (E.fields Y)).val (E.homeomorph p) := by
  apply SmoothManifolds.LieBrackets.tangent_ext_global (E.homeomorph p)
  intro F
  have hchain := E.differential p ((bracket X Y).val p)
    (SmoothManifolds.globalToGerm T (E.homeomorph p) F)
    (SmoothManifolds.globalToGerm S p (composeGlobal E F)) F.val rfl rfl
  change _ = (act T (bracket (E.fields X) (E.fields Y)) F).val (E.homeomorph p)
  rw [hchain]
  change (act S (bracket X Y) (composeGlobal E F)).val p = _
  rw [LeviCivita.bracket_action, LeviCivita.bracket_action,
    act_related E Y F, act_related E X F,
    act_related E X (act T (E.fields Y) F),
    act_related E Y (act T (E.fields X) F)]
  rfl

theorem fields_bracket (X Y : Field S) :
    E.fields (bracket X Y) = bracket (E.fields X) (E.fields Y) := by
  apply Subtype.ext
  funext q
  obtain ⟨p, rfl⟩ := E.homeomorph.surjective q
  exact (E.fields_apply (bracket X Y) p).symm.trans (bracket_related E X Y p)

theorem koszul_related (g : RiemannianMetric S) (h : RiemannianMetric T)
    (hm : ∀ p v w, pairing h (E.homeomorph p) (E.linear p v) (E.linear p w) = pairing g p v w)
    (X Y Z : Field S) (p : M) :
    (LeviCivita.koszulFunction g X Y Z).val p =
      (LeviCivita.koszulFunction h (E.fields X) (E.fields Y) (E.fields Z)).val (E.homeomorph p) := by
  have hpair (U V : Field S) :
      LeviCivita.fieldPairing g U V = composeGlobal E (LeviCivita.fieldPairing h (E.fields U) (E.fields V)) := by
    apply Subtype.ext
    funext q
    change pairing g q (U.val q) (V.val q) =
      pairing h (E.homeomorph q) ((E.fields U).val (E.homeomorph q)) ((E.fields V).val (E.homeomorph q))
    rw [← E.fields_apply, ← E.fields_apply]
    exact (hm q _ _).symm
  have ha (U V W : Field S) :
      (act S U (LeviCivita.fieldPairing g V W)).val p =
        (act T (E.fields U) (LeviCivita.fieldPairing h (E.fields V) (E.fields W))).val (E.homeomorph p) := by
    rw [hpair]
    exact act_related_at E U (E.fields U) p (E.fields_apply U p) _
  have hb (U V W : Field S) :
      pairing g p (U.val p) ((bracket V W).val p) =
        pairing h (E.homeomorph p) ((E.fields U).val (E.homeomorph p))
          ((bracket (E.fields V) (E.fields W)).val (E.homeomorph p)) := by
    rw [← hm p (U.val p) ((bracket V W).val p), E.fields_apply, bracket_related E V W p]
  change (act S X (LeviCivita.fieldPairing g Y Z)).val p +
      (act S Y (LeviCivita.fieldPairing g Z X)).val p -
      (act S Z (LeviCivita.fieldPairing g X Y)).val p - pairing g p (X.val p) ((bracket Y Z).val p) +
      pairing g p (Y.val p) ((bracket Z X).val p) + pairing g p (Z.val p) ((bracket X Y).val p) =
    (act T (E.fields X) (LeviCivita.fieldPairing h (E.fields Y) (E.fields Z))).val (E.homeomorph p) +
      (act T (E.fields Y) (LeviCivita.fieldPairing h (E.fields Z) (E.fields X))).val (E.homeomorph p) -
      (act T (E.fields Z) (LeviCivita.fieldPairing h (E.fields X) (E.fields Y))).val (E.homeomorph p) -
      pairing h (E.homeomorph p) ((E.fields X).val (E.homeomorph p))
        ((bracket (E.fields Y) (E.fields Z)).val (E.homeomorph p)) +
      pairing h (E.homeomorph p) ((E.fields Y).val (E.homeomorph p))
        ((bracket (E.fields Z) (E.fields X)).val (E.homeomorph p)) +
      pairing h (E.homeomorph p) ((E.fields Z).val (E.homeomorph p))
        ((bracket (E.fields X) (E.fields Y)).val (E.homeomorph p))
  rw [ha X Y Z, ha Y Z X, ha Z X Y, hb X Y Z, hb Y Z X, hb Z X Y]

theorem connection_related (g : RiemannianMetric S) (h : RiemannianMetric T)
    (hm : ∀ p v w, pairing h (E.homeomorph p) (E.linear p v) (E.linear p w) = pairing g p v w)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (X Y : Field S) (p : M) :
    E.linear p ((C.cov X Y).val p) = (K.cov (E.fields X) (E.fields Y)).val (E.homeomorph p) := by
  apply LeviCivita.pairing_ext h (E.homeomorph p)
  intro W
  let v := (E.linear p).symm (W.val (E.homeomorph p))
  obtain ⟨Z, hZp⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  have heval : (E.fields Z).val (E.homeomorph p) = W.val (E.homeomorph p) := by
    rw [← E.fields_apply, hZp]
    exact (E.linear p).apply_symm_apply _
  have hc := LeviCivita.koszul_formula g C hC X Y Z p
  have hk := LeviCivita.koszul_formula h K hK (E.fields X) (E.fields Y) (E.fields Z) (E.homeomorph p)
  have hn := koszul_related E g h hm X Y Z p
  rw [LeviCivita.koszulFunction_apply, LeviCivita.koszulFunction_apply] at hn
  have hp : pairing h (E.homeomorph p) (E.linear p ((C.cov X Y).val p))
      ((E.fields Z).val (E.homeomorph p)) = pairing g p ((C.cov X Y).val p) (Z.val p) := by
    rw [← E.fields_apply]
    exact hm p _ _
  rw [← heval, hp]
  linarith

theorem fields_connection (g : RiemannianMetric S) (h : RiemannianMetric T)
    (hm : ∀ p v w, pairing h (E.homeomorph p) (E.linear p v) (E.linear p w) = pairing g p v w)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K) (X Y : Field S) :
    E.fields (C.cov X Y) = K.cov (E.fields X) (E.fields Y) := by
  apply Subtype.ext
  funext q
  obtain ⟨p, rfl⟩ := E.homeomorph.surjective q
  exact (E.fields_apply (C.cov X Y) p).symm.trans (connection_related E g h hm C K hC hK X Y p)

theorem curvature_related (g : RiemannianMetric S) (h : RiemannianMetric T)
    (hm : ∀ p v w, pairing h (E.homeomorph p) (E.linear p v) (E.linear p w) = pairing g p v w)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K) (X Y Z : Field S) (p : M) :
    E.linear p ((curvature C X Y Z).val p) =
      (curvature K (E.fields X) (E.fields Y) (E.fields Z)).val (E.homeomorph p) := by
  simp only [curvature, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
    map_add, map_smul, connection_related E g h hm C K hC hK,
    fields_connection E g h hm C K hC hK, fields_bracket E]

theorem tensor_related (g : RiemannianMetric S) (h : RiemannianMetric T)
    (hm : ∀ p v w, pairing h (E.homeomorph p) (E.linear p v) (E.linear p w) = pairing g p v w)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature K Q)
    (p : M) (v w z : TangentSpace S p) :
    E.linear p (R.val p v w z) =
      Q.val (E.homeomorph p) (E.linear p v) (E.linear p w) (E.linear p z) := by
  let X := CurvatureAlgebra.fieldLift (S := S) p v
  let Y := CurvatureAlgebra.fieldLift (S := S) p w
  let Z := CurvatureAlgebra.fieldLift (S := S) p z
  have hv : X.val p = v := CurvatureAlgebra.fieldLift_value p v
  have hw : Y.val p = w := CurvatureAlgebra.fieldLift_value p w
  have hz : Z.val p = z := CurvatureAlgebra.fieldLift_value p z
  have hcurv := curvature_related E g h hm C K hC hK X Y Z p
  rw [← hR X Y Z p, ← hQ (E.fields X) (E.fields Y) (E.fields Z) (E.homeomorph p),
    ← E.fields_apply, ← E.fields_apply, ← E.fields_apply, hv, hw, hz] at hcurv
  exact hcurv

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency true in
theorem constantSectional (g : RiemannianMetric S) (h : RiemannianMetric T)
    (hm : ∀ p v w, pairing h (E.homeomorph p) (E.linear p v) (E.linear p w) = pairing g p v w)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature K Q)
    (k : ℝ) (hk : ConstantSectional (S := T) h Q k) : ConstantSectional (S := S) g R k := by
  intro p v w hi
  have hi' : LinearIndependent ℝ ![E.linear p v, E.linear p w] := by
    have hi2 := (linearIndependent_fin2 (K := ℝ) (f := ![v, w])).mp hi
    change w ≠ 0 ∧ (∀ t : ℝ, t • w ≠ v) at hi2
    apply (linearIndependent_fin2 (K := ℝ) (f := ![E.linear p v, E.linear p w])).mpr
    change E.linear p w ≠ 0 ∧ (∀ t : ℝ, t • E.linear p w ≠ E.linear p v)
    constructor
    · intro hz
      apply hi2.1
      apply (E.linear p).injective
      simpa only [map_zero] using hz
    · intro t ht
      apply hi2.2 t
      apply (E.linear p).injective
      simpa only [map_smul] using ht
  have hsec := hk (E.homeomorph p) (E.linear p v) (E.linear p w) hi'
  have hten := tensor_related E g h hm C K hC hK R Q hR hQ p v w w
  have hnum : pairing h (E.homeomorph p)
      (Q.val (E.homeomorph p) (E.linear p v) (E.linear p w) (E.linear p w)) (E.linear p v) =
      pairing g p (R.val p v w w) v :=
    (congrArg (fun z => pairing h (E.homeomorph p) z (E.linear p v)) hten.symm).trans
      (hm p (R.val p v w w) v)
  change pairing h (E.homeomorph p)
      (Q.val (E.homeomorph p) (E.linear p v) (E.linear p w) (E.linear p w)) (E.linear p v) /
      (pairing h (E.homeomorph p) (E.linear p v) (E.linear p v) *
        pairing h (E.homeomorph p) (E.linear p w) (E.linear p w) -
        pairing h (E.homeomorph p) (E.linear p v) (E.linear p w) ^ 2) = k at hsec
  change pairing g p (R.val p v w w) v /
      (pairing g p v v * pairing g p w w - pairing g p v w ^ 2) = k
  rw [hnum, hm p v v, hm p w w, hm p v w] at hsec
  exact hsec
end
end P202.Geometry.KillingHopf.CurvatureTransport

set_option maxHeartbeats 800000
namespace P202.Geometry.KillingHopf
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData P202.MetricData P202.CurveData
  P202.Geometry.KillingHopf.Transport
open Set Filter
open scoped _root_.Topology
universe u v

/-- Smooth maps between arbitrary universes preserve the actual C¹-piece
condition with ambient Euclidean extensions. -/
theorem cross_coordinateC1On_postcomp
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N} {f : M → N}
    (hf : IsSmoothMap S T f) {c : ℝ → M} {J : Set ℝ}
    (hc : ContinuousOn c J) (h : CoordinateC1On S c J) :
    CoordinateC1On T (f ∘ c) J := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := h t ht
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f (c t))
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := (hf (c t)).2 e he d hd hp hpd
  have hxU : x t ∈ U := hxt.symm ▸ hpU
  have hF1 : ContDiffAt ℝ 1 F (x t) :=
    (hF.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)
  refine ⟨d, hd, hpd, F ∘ x, hF1.comp t hx, ?_, ?_⟩
  · exact (congrArg F hxt).trans hrep.eq_of_nhds
  · have hcomp := hrep.comp_tendsto (hc t ht)
    filter_upwards [heq, hcomp] with s hs hsf
    change (d (f (c s))).val = F (x s)
    rw [← hs]
    exact hsf.symm

/-- Postcomposition retains each original piece and its actual nodes. -/
def cross_postcompose
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (f : M → N) (hf : IsSmoothMap S T f)
    {l r : ℝ} (c : PiecewiseC1Curve S l r) : PiecewiseC1Curve T l r where
  ordered := c.ordered
  toFun := f ∘ c
  continuousOn := (continuous_iff_continuousAt.mpr (fun p => (hf p).1)).comp_continuousOn c.continuousOn
  pieces := c.pieces
  node := c.node
  monotone_node := c.monotone_node
  first_node := c.first_node
  last_node := c.last_node
  regular := fun i => cross_coordinateC1On_postcomp hf
    (c.continuousOn.mono (fun _ ht =>
      ⟨(PiecewiseCurves.node_mem c i.castSucc).1.trans ht.1,
        ht.2.trans (PiecewiseCurves.node_mem c i.succ).2⟩)) (c.regular i)

/-- Intrinsic metric preservation gives equality of the original lengths,
independently of the universes containing the two manifolds. -/
theorem cross_metricPreserving_length
    {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, CrossDifferential S T f p (L p))
    (hmetric : ∀ p v w, pairing h (f p) (L p v) (L p w) = pairing g p v w)
    {l r : ℝ} (c : PiecewiseC1Curve S l r) :
    length h (cross_postcompose f hf c) = length g c := by
  unfold length
  apply PiecewiseCurves.integral_eq_of_eqOn_off_finite (breakpoints c)
  intro t ht hcorner
  rw [uIoc_of_le c.ordered] at ht
  change tangentNorm h (f (c t)) (velocity T (f ∘ c) t) = _
  have hv := cross_hasVelocityAt_postcomp hf
    (PiecewiseCurves.hasVelocityAt_off_breakpoints c ⟨ht.1.le, ht.2⟩ hcorner)
    (L (c t)) (hL (c t))
  rw [PiecewiseCurves.velocity_eq hv]
  unfold tangentNorm
  rw [hmetric]
  rfl

/-- The image of each original path bounds the target length distance. -/
theorem cross_metricPreserving_distance_le
    {n m : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] [ConnectedSpace M]
    {S : SmoothManifold n .euclidean M} {T : SmoothManifold m .euclidean N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, CrossDifferential S T f p (L p))
    (hmetric : ∀ p v w, pairing h (f p) (L p v) (L p w) = pairing g p v w)
    (x y : M) :
    P202.CompleteExponentialData.lengthDistance h (f x) (f y) ≤
      P202.CompleteExponentialData.lengthDistance g x y := by
  have hne : (P202.DistanceData.pathLengths g x y).Nonempty :=
    (LengthDistance.pathLengths_nonempty_iff g x y).mpr
      ((LengthDistance.path_exists S x y).mpr (by
        rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial))
  apply le_csInf hne
  rintro r ⟨a, b, c, hc₀, hc₁, rfl⟩
  let d := cross_postcompose f hf c
  have hbound : P202.CompleteExponentialData.lengthDistance h (d a) (d b) ≤ length h d :=
    csInf_le (LengthDistance.pathLengths_bddBelow h _ _) ⟨a, b, d, rfl, rfl, rfl⟩
  have hlength := cross_metricPreserving_length g h f hf L hL hmetric c
  change P202.CompleteExponentialData.lengthDistance h (f (c a)) (f (c b)) ≤ _ at hbound
  rw [hc₀, hc₁, hlength] at hbound
  exact hbound
end P202.Geometry.KillingHopf
namespace P202.Geometry.KillingHopf
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.PartitionData
  P202.MetricData P202.CompletenessData P202.KillingHopfData
open Set Filter
open scoped _root_.Topology
universe u v w

/-- Cross-universe intrinsic isometries compose, including their action on
all smooth scalar germs and the original length distances. -/
def crossIsometry_trans {n : ℕ} {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean Y}
    {U : SmoothManifold n .euclidean Z}
    {g : RiemannianMetric S} {h : RiemannianMetric T} {j : RiemannianMetric U}
    (e : CrossIsometry S T g h) (f : CrossIsometry T U h j) :
    CrossIsometry S U g j where
  homeomorph := e.homeomorph.trans f.homeomorph
  smooth := SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    T.smoothStructure.property.1.1 _ _ e.smooth f.smooth
  smooth_inverse := SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    T.smoothStructure.property.1.1 _ _ f.smooth_inverse e.smooth_inverse
  linear x := (f.linear (e.homeomorph x)).comp (e.linear x)
  differential x := P202.Geometry.KillingHopf.Transport.crossDifferential_comp S T U
    e.homeomorph f.homeomorph e.smooth f.smooth x (e.linear x)
    (f.linear (e.homeomorph x)) (e.differential x) (f.differential (e.homeomorph x))
  preserves x v w := (f.preserves _ _ _).trans (e.preserves x v w)
  distance x y := (f.distance _ _).trans (e.distance x y)

/-- Transport a complete metric between arbitrary universes, retaining the
specified topologies and the exact distance. -/
theorem complete_metric_of_homeomorph {X : Type u} {Y : Type v}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (e : X ≃ₜ Y) (d : MetricSpace Y)
    (htop : d.toUniformSpace.toTopologicalSpace = tY)
    (hc : @CompleteSpace Y d.toUniformSpace) :
    ∃ dX : MetricSpace X, dX.toUniformSpace.toTopologicalSpace = tX ∧
      (∀ x y, @dist X dX.toDist x y = @dist Y d.toDist (e x) (e y)) ∧
      @CompleteSpace X dX.toUniformSpace := by
  let dY := d.replaceTopology htop.symm
  have hdY : dY = d := MetricSpace.replaceTopology_eq d htop.symm
  letI : MetricSpace Y := dY
  have hcy : @CompleteSpace Y dY.toUniformSpace := by rw [hdY]; exact hc
  letI : CompleteSpace Y := hcy
  let dX : MetricSpace X := e.isEmbedding.comapMetricSpace e
  letI : MetricSpace X := dX
  have hi : Isometry e := Isometry.of_dist_eq fun _ _ => rfl
  exact ⟨dX, rfl, fun _ _ => rfl,
    (hi.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance⟩

/-- Completeness of the original length metric is invariant under an
intrinsic Riemannian isometry, even across universes. -/
theorem crossIsometry_complete {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean Y}
    {g : RiemannianMetric S} {h : RiemannianMetric T}
    (e : CrossIsometry S T g h) (hh : LengthMetricComplete h) :
    LengthMetricComplete g := by
  obtain ⟨d, ht, hd, hc⟩ := hh
  obtain ⟨dX, htX, hdX, hcX⟩ := complete_metric_of_homeomorph e.homeomorph d ht hc
  exact ⟨dX, htX, fun x y => (hdX x y).trans ((hd _ _).trans (e.distance x y)), hcX⟩

/-- Identification of an arbitrary realization with a literal standard model
is preserved under an intrinsic isometry. -/
theorem isStandardModel_of_crossIsometry {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean Y}
    {g : RiemannianMetric S} {h : RiemannianMetric T}
    (e : CrossIsometry S T g h) {k : ℝ} (hk : IsStandardModel T h k) :
    IsStandardModel S g k := by
  rcases hk with ⟨hk, G, ⟨f⟩⟩ | ⟨hk, A, B, ⟨f⟩⟩ | ⟨hk, U, j, hU, hj, ⟨f⟩⟩
  · exact Or.inl ⟨hk, G, ⟨crossIsometry_trans e f⟩⟩
  · exact Or.inr (Or.inl ⟨hk, A, B, ⟨crossIsometry_trans e f⟩⟩)
  · exact Or.inr (Or.inr ⟨hk, U, j, hU, hj, ⟨crossIsometry_trans e f⟩⟩)
end P202.Geometry.KillingHopf
namespace P202.Geometry.KillingHopf
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.CurvatureData P202.ConstantCurvaturePolarData
  P202.CompletenessData P202.KillingHopfData P202.Geometry.KillingHopf.Transport
open Set Filter
open scoped _root_.Topology
universe u v

/-- Smooth metric transported through a cross-universe diffeomorphism. -/
def diffeomorphMetric
    {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean Y)
    (h : RiemannianMetric T) (e : X ≃ₜ Y)
    (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm) : RiemannianMetric S :=
  cross_pullbackMetric h e he (fun p => (tangentEquiv S T e he hi p).toLinearMap)
    (tangentPush_spec S T e he) (fun p => (tangentEquiv S T e he hi p).injective)

/-- The smooth pullback through a diffeomorphism gives an intrinsic
Riemannian isometry, with no additional distance certificate. -/
def diffeomorphIsometry
    {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [ConnectedSpace Y]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean Y)
    (h : RiemannianMetric T) (e : X ≃ₜ Y)
    (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm) :
    CrossIsometry S T (diffeomorphMetric S T h e he hi) h := by
  let E := tangentEquiv S T e he hi
  let L := fun p => (E p).toLinearMap
  have hL : ∀ p, CrossDifferential S T e p (L p) := tangentPush_spec S T e he
  let g := diffeomorphMetric S T h e he hi
  have hm : ∀ p v w, pairing h (e p) (L p v) (L p w) = pairing g p v w :=
    fun _ _ _ => rfl
  have hmi := cross_inverse_metric_preserving g h e he hi L hL hm
  refine ⟨e, he, hi, L, hL, hm, fun x y => ?_⟩
  apply le_antisymm (cross_metricPreserving_distance_le g h e he L hL hm x y)
  have hbound := cross_metricPreserving_distance_le h g e.symm hi
    (tangentPush T S e.symm hi) (tangentPush_spec T S e.symm hi) hmi (e x) (e y)
  simpa only [e.symm_apply_apply] using hbound

/-- Completeness and constant curvature transport through a smooth
homeomorphism, with curvature invariance proved by Koszul naturality. -/
theorem complete_curvature_geometry_of_diffeomorph
    {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [ConnectedSpace Y]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean Y)
    (h : RiemannianMetric T) (K : Connection (tangentBundle T))
    (hK : IsLeviCivita h K) (Q : CurvatureTensor T) (hQ : RepresentsCurvature K Q)
    (k : ℝ) (hk : ConstantSectional h Q k) (hh : LengthMetricComplete h)
    (e : X ≃ₜ Y) (he : IsSmoothMap S T e) (hi : IsSmoothMap T S e.symm) :
    ∃ (g : RiemannianMetric S) (C : Connection (tangentBundle S))
      (R : CurvatureTensor S), IsLeviCivita g C ∧ RepresentsCurvature C R ∧
      ConstantSectional g R k ∧ LengthMetricComplete g ∧
      Nonempty (CrossIsometry S T g h) := by
  let g := diffeomorphMetric S T h e he hi
  let F := diffeomorphIsometry S T h e he hi
  let E := tangentEquiv S T e he hi
  have hE : ∀ p, CrossDifferential S T e p (E p).toLinearMap := tangentPush_spec S T e he
  have hm : ∀ p v w, pairing h (e p) (E p v) (E p w) = pairing g p v w :=
    fun _ _ _ => rfl
  let J : P202.Geometry.KillingHopf.CurvatureTransport.FieldTransport S T := {
    homeomorph := e
    smooth := he
    linear := E
    differential := hE
    fields := cross_pushField e he hi (fun p => (E p).toLinearMap) hE
    fields_apply := cross_pushField_apply e he hi (fun p => (E p).toLinearMap) hE }
  obtain ⟨C, hC, _⟩ := LeviCivita.exists_unique g
  obtain ⟨R, hR, _⟩ := CurvatureAlgebra.tensor_exists_unique C
  exact ⟨g, C, R, hC, hR,
    P202.Geometry.KillingHopf.CurvatureTransport.constantSectional J g h hm C K hC hK R Q hR hQ k hk,
    crossIsometry_complete F hh, ⟨F⟩⟩
end P202.Geometry.KillingHopf
namespace P202.Geometry.KillingHopf
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.CurvatureData P202.ConstantCurvaturePolarData
  P202.CompletenessData P202.KillingHopfData
open Set Filter
open scoped _root_.Topology
universe u
open private transportManifold from
  MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.QuotientBundles

/-- The literal models admit complete, simply connected realizations in every
universe, with their original metric, differential, and length distance. -/
theorem standardModel_exists_universe (n : ℕ) (hn : 2 ≤ n) (k : ℝ) :
    ∃ (X : Type u) (t : TopologicalSpace X) (S : SmoothManifold n .euclidean X)
      (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S),
      SimplyConnectedSpace X ∧ IsLeviCivita g C ∧ RepresentsCurvature C R ∧
      ConstantSectional g R k ∧ LengthMetricComplete g ∧ IsStandardModel S g k := by
  obtain ⟨Y, tY, T, h, K, Q, hsimply, hK, hQ, hk, hh, hmodel⟩ :=
    standardModel_exists n hn k
  letI := tY
  letI := hsimply
  let e : ULift.{u} Y ≃ₜ Y := Homeomorph.ulift
  let S := transportManifold T e.symm
  have hmaps := SmoothManifolds.transportAtlas_maps (⊤ : ℕ∞)
    T.smoothStructure.val e.symm T.smoothStructure.property.1
  have he : IsSmoothMap S T e := by
    simpa only [S, transportManifold, IsSmoothMap, Homeomorph.symm_symm] using hmaps.2
  have hi : IsSmoothMap T S e.symm := hmaps.1
  letI : SimplyConnectedSpace (ULift.{u} Y) := e.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨g, C, R, hC, hR, hconstant, hcomplete, ⟨F⟩⟩ :=
    complete_curvature_geometry_of_diffeomorph S T h K hK Q hQ k hk hh e he hi
  exact ⟨ULift.{u} Y, inferInstance, S, g, C, R, inferInstance, hC, hR,
    hconstant, hcomplete, isStandardModel_of_crossIsometry F hmodel⟩

universe v

/-- Transport a local isometry between realizations in different universes. -/
theorem localIsometry_conjugateCross {n : ℕ} {X M : Type u} {X0 M0 : Type v}
    [TopologicalSpace X] [TopologicalSpace M]
    [TopologicalSpace X0] [TopologicalSpace M0]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean M}
    {S0 : SmoothManifold n .euclidean X0} {T0 : SmoothManifold n .euclidean M0}
    {g : RiemannianMetric S} {h : RiemannianMetric T}
    {g0 : RiemannianMetric S0} {h0 : RiemannianMetric T0}
    (e : CrossIsometry S S0 g g0) (j : CrossIsometry T0 T h0 h)
    {f0 : X0 → M0} (hf : IsLocalIsometry g0 h0 f0) :
    IsLocalIsometry g h (j.homeomorph ∘ f0 ∘ e.homeomorph) := by
  let f : X → M := j.homeomorph ∘ f0 ∘ e.homeomorph
  have hefs : IsSmoothMap S T0 (f0 ∘ e.homeomorph) :=
    SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      S0.smoothStructure.property.1.1 _ _ e.smooth hf.1.1
  have hfs : IsSmoothMap S T f :=
    SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      T0.smoothStructure.property.1.1 _ _ hefs j.smooth
  obtain ⟨L0, hL0, hm0⟩ := hf.2
  refine ⟨⟨hfs, fun x => ?_⟩,
    fun x => (j.linear (f0 (e.homeomorph x))).comp ((L0 (e.homeomorph x)).comp (e.linear x)),
    fun x => ?_, fun x v w => ?_⟩
  · obtain ⟨q, hq, hqx, hqf, hfq⟩ := hf.1.2 (e.homeomorph x)
    let q' : M → X := e.homeomorph.symm ∘ q ∘ j.homeomorph.symm
    have hqs : ManifoldSmoothAt T0.smoothStructure.val S.smoothStructure.val
        (e.homeomorph.symm ∘ q) (f0 (e.homeomorph x)) :=
      SmoothManifolds.manifoldContDiffAt_comp S0.smoothStructure.property.1.1
        hq (e.smooth_inverse _)
    have hq's : ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val q' (f x) := by
      have hq's := SmoothManifolds.manifoldContDiffAt_comp T0.smoothStructure.property.1.1
        (j.smooth_inverse (f x))
        (show ManifoldSmoothAt T0.smoothStructure.val S.smoothStructure.val
          (e.homeomorph.symm ∘ q) (j.homeomorph.symm (f x)) by
          simpa only [f, Function.comp_apply, j.homeomorph.symm_apply_apply] using hqs)
      exact hq's
    refine ⟨q', hq's, ?_, ?_, ?_⟩
    · simp only [q', f, Function.comp_apply, j.homeomorph.symm_apply_apply,
        hqx, e.homeomorph.symm_apply_apply]
    · have hnear : ∀ᶠ z in 𝓝 x,
          q (f0 (e.homeomorph z)) = e.homeomorph z :=
        e.homeomorph.continuous.continuousAt.eventually hqf
      filter_upwards [hnear] with z hz
      simpa only [q', f, Function.comp_apply, j.homeomorph.symm_apply_apply,
        hz, e.homeomorph.symm_apply_apply, id_eq]
    · have hjnear : Tendsto j.homeomorph.symm (𝓝 (f x))
          (𝓝 (f0 (e.homeomorph x))) := by
        simpa only [f, Function.comp_apply, j.homeomorph.symm_apply_apply] using
          (j.homeomorph.symm.continuous.continuousAt (x := f x)).tendsto
      have hnear : ∀ᶠ z in 𝓝 (f x),
          f0 (q (j.homeomorph.symm z)) = j.homeomorph.symm z := hjnear.eventually hfq
      filter_upwards [hnear] with z hz
      simpa only [q', f, Function.comp_apply, e.homeomorph.apply_symm_apply,
        hz, j.homeomorph.apply_symm_apply, id_eq]
  · have hLe := Transport.crossDifferential_comp S S0 T0 e.homeomorph f0
      e.smooth hf.1.1 x (e.linear x) (L0 (e.homeomorph x))
      (e.differential x) (hL0 (e.homeomorph x))
    exact Transport.crossDifferential_comp S T0 T (f0 ∘ e.homeomorph) j.homeomorph
      hefs j.smooth x ((L0 (e.homeomorph x)).comp (e.linear x))
      (j.linear (f0 (e.homeomorph x))) hLe (j.differential (f0 (e.homeomorph x)))
  · exact (j.preserves _ _ _).trans ((hm0 _ _ _).trans (e.preserves x v w))

/-- Every manifold in the paper's category admits a realization in `Type`.
Second countability and separation distinguish points by a countable basis. -/
private theorem manifold_small {n : ℕ} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold n .euclidean M) : Small.{0} M := by
  classical
  letI := T.topologicalManifold.hausdorff
  letI := T.topologicalManifold.secondCountable
  let f : M → Set (TopologicalSpace.countableBasis M) := fun x => {s | x ∈ s.val}
  apply small_of_injective.{0} (f := f)
  intro x y h
  apply (TopologicalSpace.isBasis_countableBasis M).eq_iff.mpr
  intro s hs
  exact Set.ext_iff.mp h ⟨s, hs⟩

/-- Killing–Hopf classification for every complete connected manifold of
constant sectional curvature, including its Riemannian universal cover,
isometric deck action, and smooth Riemannian orbit quotient. -/
theorem killingHopf : P202Specs.Geometry.KillingHopf.killingHopfType.{u} := by
  intro n hn M _ _ T h D hD Q hQ k hk hh
  letI : Small.{0} M := manifold_small T
  let e : Shrink.{0} M ≃ₜ M := (Shrink.homeomorph M).symm
  let T0 := transportManifold T e.symm
  have hmaps := SmoothManifolds.transportAtlas_maps (⊤ : ℕ∞)
    T.smoothStructure.val e.symm T.smoothStructure.property.1
  have he : IsSmoothMap T0 T e := by
    simpa only [T0, transportManifold, IsSmoothMap, Homeomorph.symm_symm] using hmaps.2
  have hei : IsSmoothMap T T0 e.symm := hmaps.1
  letI : ConnectedSpace (Shrink.{0} M) := e.symm.surjective.connectedSpace e.symm.continuous
  obtain ⟨h0, D0, Q0, hD0, hQ0, hk0, hh0, ⟨J⟩⟩ :=
    complete_curvature_geometry_of_diffeomorph T0 T h D hD Q hQ k hk hh e he hei
  obtain ⟨X0, t0, S0, g0, hs0, hg0, hmodel0, f0, hf0⟩ :=
    literalModel_development hn T0 h0 D0 hD0 Q0 hQ0 k hk0 hh0
  letI := t0
  letI := hs0
  let a : ULift.{u} X0 ≃ₜ X0 := Homeomorph.ulift
  let S := transportManifold S0 a.symm
  have hamaps := SmoothManifolds.transportAtlas_maps (⊤ : ℕ∞)
    S0.smoothStructure.val a.symm S0.smoothStructure.property.1
  have ha : IsSmoothMap S S0 a := by
    simpa only [S, transportManifold, IsSmoothMap, Homeomorph.symm_symm] using hamaps.2
  have hai : IsSmoothMap S0 S a.symm := hamaps.1
  letI : SimplyConnectedSpace (ULift.{u} X0) := a.toHomotopyEquiv.simplyConnectedSpace
  let g := diffeomorphMetric S S0 g0 a ha hai
  let A : CrossIsometry S S0 g g0 := diffeomorphIsometry S S0 g0 a ha hai
  let f : ULift.{u} X0 → M := J.homeomorph ∘ f0 ∘ A.homeomorph
  have hf : IsLocalIsometry g h f := localIsometry_conjugateCross A J hf0
  have hcover : P202Specs.Topology.Covering f :=
    (CompleteLocalIsometry.complete_local_isometry S T g h f hf
      (crossIsometry_complete A hg0)).1
  exact ⟨ULift.{u} X0, inferInstance, S, g, inferInstance,
    isStandardModel_of_crossIsometry A hmodel0,
    f, classification_of_covering S T g h f hf hcover hh⟩

end P202.Geometry.KillingHopf
