import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalSpaceFormDevelopment
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LocalSpaceFormDevelopment
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ModelPolarDomains
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.PathConnected

/-! Work on the globalization step of Killing–Hopf.

The construction uses ordinary germs of actual local isometries and the
proved local development, extension and uniqueness theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace P202.Geometry.GlobalSpaceFormDevelopment
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.MaximalFlowData P202.ConnectionData P202.MetricData
  P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
  P202.CurvatureData P202.ConstantCurvaturePolarData P202.CompletenessData
  P202.LocalDevelopmentData P202.ExponentialJacobiData
  P202.ModelPolarData P202.SpaceFormData P202.DistanceData P202.CompleteExponentialData
open Set Filter
open scoped _root_.Topology
universe u

section Locality
variable {n : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
  {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean M}
  {g : RiemannianMetric S} {h : RiemannianMetric T}

theorem isLocalIsometryOn_restrict {f : X → M} {U V : Set X}
    (hf : IsLocalIsometryOn g h f U) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsLocalIsometryOn g h f V :=
  ⟨hV, fun p hp => hf.2 p (hVU hp)⟩

theorem isLocalIsometryOn_continuousOn {f : X → M} {U : Set X}
    (hf : IsLocalIsometryOn g h f U) : ContinuousOn f U :=
  fun p hp => (hf.2 p hp).1.1.continuousWithinAt

/-- The intrinsic differential depends only on the neighborhood germ, with
transport in the target fiber made explicit. -/
theorem isDifferential_congr_germ {f k : X → M} {p : X}
    (heq : f =ᶠ[𝓝 p] k)
    {L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)}
    (hL : IsDifferential S T f p L) :
    IsDifferential S T k p
      ((castTangent T heq.eq_of_nhds).toLinearMap.comp L) := by
  have aux (y : M) (e : f p = y) :
      ∀ (v : TangentSpace S p) (a : SmoothGerm T y) (b : SmoothGerm S p)
        (r : M → ℝ), Germ.ofFun r = a.val → Germ.ofFun (r ∘ k) = b.val →
        ((castTangent T e) (L v)).val a = v.val b := by
    subst y
    intro v a b r hr hb
    apply hL v a b r hr
    exact (Germ.coe_eq.mpr (heq.fun_comp r)).trans hb
  exact aux (k p) heq.eq_of_nhds

/-- All clauses of local isometry are local in the map, including its
actual inverse germs and intrinsic metric differential. -/
theorem localIsometryAt_congr_germ {f k : X → M} {p : X}
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p ∧
      (∃ j : M → X,
        ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val j (f p) ∧
        j (f p) = p ∧ (j ∘ f) =ᶠ[𝓝 p] id ∧ (f ∘ j) =ᶠ[𝓝 (f p)] id) ∧
      ∃ L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p),
        IsDifferential S T f p L ∧
        ∀ v w, pairing h (f p) (L v) (L w) = pairing g p v w)
    (heq : f =ᶠ[𝓝 p] k) :
    ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val k p ∧
      (∃ j : M → X,
        ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val j (k p) ∧
        j (k p) = p ∧ (j ∘ k) =ᶠ[𝓝 p] id ∧ (k ∘ j) =ᶠ[𝓝 (k p)] id) ∧
      ∃ L : TangentSpace S p →ₗ[ℝ] TangentSpace T (k p),
        IsDifferential S T k p L ∧
        ∀ v w, pairing h (k p) (L v) (L w) = pairing g p v w := by
  have hp := heq.eq_of_nhds
  rcases hf with ⟨hsm, ⟨j, hj, hjp, hjf, hfj⟩, L, hL, hmetric⟩
  refine ⟨SmoothManifolds.manifoldContDiffAt_congr hsm heq, ?_,
    (castTangent T hp).toLinearMap.comp L, isDifferential_congr_germ heq hL, ?_⟩
  · have ht : Tendsto j (𝓝 (f p)) (𝓝 p) := by
      simpa only [ContinuousAt, hjp] using hj.1
    have hkj : (k ∘ j) =ᶠ[𝓝 (f p)] id :=
      (heq.comp_tendsto ht).symm.trans hfj
    exact ⟨j, hp ▸ hj, hp ▸ hjp, (heq.fun_comp j).symm.trans hjf, hp ▸ hkj⟩
  · have transport (y : M) (e : f p = y) :
        ∀ v w, pairing h y ((castTangent T e) (L v)) ((castTangent T e) (L w)) =
          pairing g p v w := by
      subst y
      exact hmetric
    exact transport (k p) hp

/-- Gluing is valid for the original local-isometry predicate, rather than
only for continuity of the glued map. -/
theorem isLocalIsometryOn_of_locally_represented {f : X → M} {U : Set X}
    (hU : IsOpen U)
    (hf : ∀ p ∈ U, ∃ (k : X → M) (V : Set X),
      IsLocalIsometryOn g h k V ∧ p ∈ V ∧ f =ᶠ[𝓝 p] k) :
    IsLocalIsometryOn g h f U := by
  refine ⟨hU, fun p hp => ?_⟩
  rcases hf p hp with ⟨k, V, hk, hpV, heq⟩
  exact localIsometryAt_congr_germ (hk.2 p hpV) heq.symm

/-- Prescribed center data is also a property of the neighborhood germ. -/
theorem hasCenterData_congr_germ {f k : X → M} {p : X} {y : M}
    {A : TangentSpace S p ≃ₗ[ℝ] TangentSpace T y}
    (hf : HasCenterData f p y A) (heq : f =ᶠ[𝓝 p] k) :
    HasCenterData k p y A := by
  rcases hf with ⟨e, hA⟩
  refine ⟨heq.eq_of_nhds.symm.trans e, ?_⟩
  have hd := isDifferential_congr_germ heq hA
  have compose_transport (z w : M) (a : z = w) (b : z = y)
      (B : TangentSpace S p ≃ₗ[ℝ] TangentSpace T y) :
      (castTangent T a).toLinearMap.comp
          ((castTangent T b).symm.toLinearMap.comp B.toLinearMap) =
        (castTangent T (a.symm.trans b)).symm.toLinearMap.comp B.toLinearMap := by
    subst w
    subst y
    rfl
  rwa [compose_transport (f p) (k p) heq.eq_of_nhds e A] at hd

/-- Actual local isometries representing a germ. Total representatives are
used only to avoid arbitrary extension choices outside the open domain. -/
structure LocalRepresentative (g : RiemannianMetric S) (h : RiemannianMetric T) where
  toFun : X → M
  domain : Set X
  isLocalIsometry : IsLocalIsometryOn g h toFun domain

/-- The fiber consists of precisely those neighborhood germs that have a
local-isometry representative. This is a quotient, not a space of chosen jets. -/
def IsometryGerm (g : RiemannianMetric S) (h : RiemannianMetric T) (x : X) :=
  {a : Filter.Germ (𝓝 x) M //
    ∃ f : LocalRepresentative g h, x ∈ f.domain ∧ Germ.ofFun f.toFun = a}

def GermSpace (g : RiemannianMetric S) (h : RiemannianMetric T) :=
  (x : X) × IsometryGerm g h x

def LocalRepresentative.germ (f : LocalRepresentative g h) (x : X) (hx : x ∈ f.domain) :
    IsometryGerm g h x :=
  ⟨Germ.ofFun f.toFun, f, hx, rfl⟩

def LocalRepresentative.sectionMap (f : LocalRepresentative g h) : f.domain → GermSpace g h :=
  fun x => ⟨x.val, f.germ x.val x.property⟩

def germProjection : GermSpace g h → X := Sigma.fst

@[simp] theorem projection_section (f : LocalRepresentative g h) (x : f.domain) :
    germProjection (f.sectionMap x) = x.val := rfl

theorem section_injective (f : LocalRepresentative g h) : Function.Injective f.sectionMap := by
  intro x y heq
  exact Subtype.ext (congrArg Sigma.fst heq)

theorem germ_eq_iff (f k : LocalRepresentative g h) (x : X)
    (hf : x ∈ f.domain) (hk : x ∈ k.domain) :
    f.germ x hf = k.germ x hk ↔ f.toFun =ᶠ[𝓝 x] k.toFun := by
  change (⟨Germ.ofFun f.toFun, _⟩ : IsometryGerm g h x) = ⟨Germ.ofFun k.toFun, _⟩ ↔ _
  rw [Subtype.mk.injEq, Germ.coe_eq]

/-- Neighborhood germs have a well-defined value even without a separated
target: eventual equality at a neighborhood implies equality at its center. -/
def germValue (a : GermSpace g h) : M :=
  Quotient.liftOn a.2.val (fun f : X → M => f a.1)
    (fun _ _ heq => Filter.EventuallyEq.eq_of_nhds heq)

@[simp] theorem value_section (f : LocalRepresentative g h) (x : f.domain) :
    germValue (f.sectionMap x) = f.toFun x.val := rfl

/-- The sets of germs of individual representatives form the intended basis. -/
def germBasicOpens (g : RiemannianMetric S) (h : RiemannianMetric T) :
    Set (Set (GermSpace g h)) :=
  Set.range (fun f : LocalRepresentative g h => Set.range f.sectionMap)

instance germTopology : TopologicalSpace (GermSpace g h) :=
  TopologicalSpace.generateFrom (germBasicOpens g h)

theorem section_range_open (f : LocalRepresentative g h) :
    IsOpen (Set.range f.sectionMap) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨f, rfl⟩

theorem germ_has_representative (a : GermSpace g h) :
    ∃ f : LocalRepresentative g h, a ∈ Set.range f.sectionMap := by
  rcases a with ⟨x, a, f, hx, heq⟩
  refine ⟨f, ⟨x, hx⟩, ?_⟩
  apply Sigma.mk.inj_iff.mpr
  exact ⟨rfl, heq_of_eq (Subtype.ext heq)⟩

theorem section_mem_range_iff (f k : LocalRepresentative g h) (x : f.domain) :
    f.sectionMap x ∈ Set.range k.sectionMap ↔
      x.val ∈ k.domain ∧ f.toFun =ᶠ[𝓝 x.val] k.toFun := by
  constructor
  · rintro ⟨y, heq⟩
    have hy : y.val = x.val := congrArg Sigma.fst heq
    have hy' : y = ⟨x.val, hy ▸ y.property⟩ := Subtype.ext hy
    rw [hy'] at heq
    refine ⟨hy ▸ y.property, ?_⟩
    have heq' : k.germ x.val (hy ▸ y.property) = f.germ x.val x.property := by
      exact eq_of_heq (Sigma.mk.inj heq).2
    exact ((germ_eq_iff k f x.val (hy ▸ y.property) x.property).mp heq').symm
  · rintro ⟨hx, heq⟩
    refine ⟨⟨x.val, hx⟩, ?_⟩
    exact congrArg (Sigma.mk x.val) ((germ_eq_iff k f x.val _ _).mpr heq.symm)

theorem section_continuous (f : LocalRepresentative g h) : Continuous f.sectionMap := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨k, rfl⟩
  have heq : f.sectionMap ⁻¹' Set.range k.sectionMap =
      Subtype.val ⁻¹' (k.domain ∩ {x | f.toFun =ᶠ[𝓝 x] k.toFun}) := by
    ext x
    exact section_mem_range_iff f k x
  rw [heq]
  exact (k.isLocalIsometry.1.inter isOpen_setOfPred_eventually_nhds).preimage continuous_subtype_val

def LocalRepresentative.restrict (f : LocalRepresentative g h) (V : Set X)
    (hV : IsOpen V) (hVU : V ⊆ f.domain) : LocalRepresentative g h :=
  ⟨f.toFun, V, isLocalIsometryOn_restrict f.isLocalIsometry hV hVU⟩

theorem section_isOpenMap (f : LocalRepresentative g h) : IsOpenMap f.sectionMap := by
  intro V hV
  let W : Set X := Subtype.val '' V
  have hW : IsOpen W := f.isLocalIsometry.1.isOpenMap_subtype_val V hV
  have hWsub : W ⊆ f.domain := by rintro _ ⟨x, _, rfl⟩; exact x.property
  let k := f.restrict W hW hWsub
  have heq : f.sectionMap '' V = Set.range k.sectionMap := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, ⟨x, hx, rfl⟩⟩, rfl⟩
    · rintro _ ⟨x, rfl⟩
      rcases x.property with ⟨y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      rcases x with ⟨x, hx⟩
      rcases y with ⟨y, hy'⟩
      dsimp only at hxy
      subst y
      rfl
  rw [heq]
  exact section_range_open k

theorem section_isOpenEmbedding (f : LocalRepresentative g h) :
    Topology.IsOpenEmbedding f.sectionMap :=
  Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨section_continuous f, section_injective f, section_isOpenMap f⟩

theorem projection_continuous : Continuous (germProjection (g := g) (h := h)) := by
  rw [continuous_def]
  intro W hW
  rw [isOpen_iff_mem_nhds]
  intro a ha
  rcases germ_has_representative a with ⟨f, x, rfl⟩
  let k := f.restrict (f.domain ∩ W) (f.isLocalIsometry.1.inter hW) inter_subset_left
  have hk : f.sectionMap x ∈ Set.range k.sectionMap :=
    ⟨⟨x.val, x.property, ha⟩, rfl⟩
  apply mem_of_superset ((section_range_open k).mem_nhds hk)
  rintro _ ⟨z, rfl⟩
  exact z.property.2

/-- The basic sets really are sheets for a local homeomorphism. Covering
is stronger and still requires continuation over a common base neighborhood. -/
theorem projection_isLocalHomeomorph :
    IsLocalHomeomorph (germProjection (g := g) (h := h)) := by
  intro a
  rcases germ_has_representative a with ⟨f, x, rfl⟩
  have hcomp : IsLocalHomeomorph (germProjection ∘ f.sectionMap) :=
    f.isLocalIsometry.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hloc := hcomp.isLocalHomeomorphOn (s := Set.univ) |>.of_comp_right
    ((section_isOpenEmbedding f).isLocalHomeomorph.isLocalHomeomorphOn)
  exact hloc (f.sectionMap x) ⟨x, Set.mem_univ _, rfl⟩

theorem value_continuous : Continuous (germValue (g := g) (h := h)) := by
  rw [continuous_iff_continuousAt]
  intro a
  rcases germ_has_representative a with ⟨f, x, rfl⟩
  have hcont : ContinuousAt (f.toFun ∘ germProjection) (f.sectionMap x) :=
    ContinuousAt.comp (f := germProjection) (x := f.sectionMap x)
      (f.isLocalIsometry.2 x.val x.property).1.1 projection_continuous.continuousAt
  apply hcont.congr
  apply mem_of_superset ((section_range_open f).mem_nhds (Set.mem_range_self x))
  rintro _ ⟨z, rfl⟩
  rfl

/-- On a connected common domain the usual closed first-jet locus,
once established geometrically, gives equality of all germs. Ordinary germ
coincidence is open by definition; its closedness is an explicit obligation. -/
theorem germ_rigidity_on_connected (f k : LocalRepresentative g h) (U : Set X)
    (hconnected : IsPreconnected U)
    (hclosed : IsClosed {z : U | f.toFun =ᶠ[𝓝 z.val] k.toFun})
    (x z : U) (hx : f.toFun =ᶠ[𝓝 x.val] k.toFun) :
    f.toFun =ᶠ[𝓝 z.val] k.toFun := by
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconnected
  have hopen : IsOpen {w : U | f.toFun =ᶠ[𝓝 w.val] k.toFun} :=
    isOpen_setOfPred_eventually_nhds.preimage continuous_subtype_val
  have hall := (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x, hx⟩)
  exact Set.eq_univ_iff_forall.mp hall z

/-- A common neighborhood of continuation and uniqueness gives an evenly
covered neighborhood. Both hypotheses concern actual representatives on that
neighborhood; neither is inferred merely from local homeomorphism. -/
theorem projection_evenlyCovered_of_continuation (x : X) (U : Set X)
    (hx : x ∈ U) (hU : IsOpen U)
    (hcontinue : ∀ a : GermSpace g h, germProjection a ∈ U →
      ∃ f : LocalRepresentative g h, f.domain = U ∧
        ∃ ha : a.1 ∈ f.domain, f.sectionMap ⟨a.1, ha⟩ = a)
    (hrigid : ∀ f k : LocalRepresentative g h, f.domain = U → k.domain = U →
      ∀ z w : U, f.toFun =ᶠ[𝓝 z.val] k.toFun → f.toFun =ᶠ[𝓝 w.val] k.toFun) :
    IsEvenlyCovered (germProjection (g := g) (h := h)) x
      ((germProjection (g := g) (h := h)) ⁻¹' {x}) := by
  classical
  let ι := IsometryGerm g h x
  by_cases hnonempty : Nonempty ι
  · letI : Nonempty ι := hnonempty
    letI : TopologicalSpace ι := ⊥
    letI : DiscreteTopology ι := ⟨rfl⟩
    letI : Nonempty (X → GermSpace g h) := ⟨fun _ => ⟨x, Classical.choice hnonempty⟩⟩
    have hext (i : ι) := hcontinue ⟨x, i⟩ hx
    choose F hdom hxi hsect using hext
    let sheets (i : ι) : Set (GermSpace g h) := Set.range (F i).sectionMap
    have hsurj (i : ι) : (sheets i).SurjOn germProjection U := by
      intro z hz
      exact ⟨(F i).sectionMap ⟨z, (hdom i).symm ▸ hz⟩,
        Set.mem_range_self _, rfl⟩
    have hinj (i : ι) : (sheets i).InjOn germProjection := by
      rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩ heq
      exact congrArg (F i).sectionMap (Subtype.ext heq)
    have hopen (i : ι) {W : Set X} (hWU : W ⊆ U) :
        IsOpen W ↔ IsOpen (germProjection ⁻¹' W ∩ sheets i) := by
      constructor
      · intro hW
        exact (hW.preimage projection_continuous).inter (section_range_open (F i))
      · intro hW
        have himage : germProjection '' (germProjection ⁻¹' W ∩ sheets i) = W := by
          apply Set.Subset.antisymm
          · rintro _ ⟨a, ⟨ha, _⟩, rfl⟩
            exact ha
          · intro z hz
            rcases hsurj i (hWU hz) with ⟨a, ha, heq⟩
            exact ⟨a, ⟨by change germProjection a ∈ W; rwa [heq], ha⟩, heq⟩
        rw [← himage]
        exact projection_isLocalHomeomorph.isOpenMap _ hW
    have hdisjoint : Pairwise (Function.onFun Disjoint sheets) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro a ⟨z, hz⟩ ⟨w, hw⟩
      have heq : (F i).toFun =ᶠ[𝓝 z.val] (F j).toFun := by
        apply (section_mem_range_iff (F i) (F j) z).mp
          ⟨w, hw.trans hz.symm⟩ |>.2
      have hcenter := hrigid (F i) (F j) (hdom i) (hdom j)
        ⟨z.val, hdom i ▸ z.property⟩ ⟨x, hx⟩ heq
      have hcenter' : (F i).sectionMap ⟨x, hxi i⟩ = (F j).sectionMap ⟨x, hxi j⟩ :=
        congrArg (Sigma.mk x) ((germ_eq_iff (F i) (F j) x _ _).mpr hcenter)
      have heqij : (⟨x, i⟩ : GermSpace g h) = ⟨x, j⟩ :=
        (hsect i).symm.trans (hcenter'.trans (hsect j))
      exact hij (eq_of_heq (Sigma.mk.inj heqij).2)
    have hexhaust : germProjection ⁻¹' U ⊆ ⋃ i, sheets i := by
      intro a ha
      rcases hcontinue a ha with ⟨f, hfdom, hfa, hfaeq⟩
      let hfx : x ∈ f.domain := hfdom.symm ▸ hx
      let i : ι := f.germ x hfx
      have hicenter : (F i).germ x (hxi i) = f.germ x hfx :=
        eq_of_heq (Sigma.mk.inj (hsect i)).2
      have heqcenter := (germ_eq_iff (F i) f x _ _).mp hicenter
      have heqa := hrigid (F i) f (hdom i) hfdom ⟨x, hx⟩ ⟨a.1, ha⟩ heqcenter
      apply Set.mem_iUnion.mpr
      refine ⟨i, ⟨⟨a.1, (hdom i).symm ▸ ha⟩, ?_⟩⟩
      have heqgerm := (germ_eq_iff (F i) f a.1 ((hdom i).symm ▸ ha) hfa).mpr heqa
      exact (congrArg (Sigma.mk a.1) heqgerm).trans hfaeq
    let t := IsOpen.trivializationDiscrete (f := germProjection) sheets U hU
      (fun i _ hWU => hopen i hWU) hinj hsurj hdisjoint hexhaust
    have heven : IsEvenlyCovered germProjection x ι :=
      IsEvenlyCovered.of_trivialization (t := t) hx
    exact heven.to_isEvenlyCovered_preimage
  · have hempty : germProjection ⁻¹' U = (∅ : Set (GermSpace g h)) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      rcases hcontinue a ha with ⟨f, hfdom, _⟩
      exact hnonempty ⟨f.germ x (hfdom.symm ▸ hx)⟩
    have heven : IsEvenlyCovered germProjection x Empty :=
      IsEvenlyCovered.of_preimage_eq_empty Empty (hU.mem_nhds hx) hempty
    exact heven.to_isEvenlyCovered_preimage

/-- A convenient global reduction of the covering obligation to uniform
local continuation and closedness of germ coincidence. The geometric proofs
of these hypotheses are supplied below for the actual models. -/
theorem projection_covering_of_continuation
    (hlocal : ∀ x : X, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsPreconnected U ∧
      (∀ a : GermSpace g h, germProjection a ∈ U →
        ∃ f : LocalRepresentative g h, f.domain = U ∧
          ∃ ha : a.1 ∈ f.domain, f.sectionMap ⟨a.1, ha⟩ = a) ∧
      (∀ f k : LocalRepresentative g h, f.domain = U → k.domain = U →
        IsClosed {z : U | f.toFun =ᶠ[𝓝 z.val] k.toFun})) :
    IsCoveringMap (germProjection (g := g) (h := h)) := by
  intro x
  rcases hlocal x with ⟨U, hx, hU, hconn, hcont, hclosed⟩
  apply projection_evenlyCovered_of_continuation x U hx hU hcont
  intro f k hf hk z w heq
  exact germ_rigidity_on_connected f k U hconn (hclosed f k hf hk) z w heq

/-- A continuous section of the germ projection is locally represented by
one of the actual local isometries used to construct the space. -/
theorem section_locally_represented (s : X → GermSpace g h) (hs : Continuous s)
    (hover : ∀ x, germProjection (s x) = x) (x : X) :
    ∃ f : LocalRepresentative g h,
      x ∈ f.domain ∧ (germValue ∘ s) =ᶠ[𝓝 x] f.toFun := by
  rcases germ_has_representative (s x) with ⟨f, y, hy⟩
  have hxy : y.val = x := (congrArg Sigma.fst hy).trans (hover x)
  refine ⟨f, hxy ▸ y.property, ?_⟩
  have hmem : s x ∈ Set.range f.sectionMap := ⟨y, hy⟩
  have hev : ∀ᶠ z in 𝓝 x, s z ∈ Set.range f.sectionMap :=
    hs.continuousAt.preimage_mem_nhds ((section_range_open f).mem_nhds hmem)
  filter_upwards [hev] with z hz
  rcases hz with ⟨w, hw⟩
  have hwz : w.val = z := (congrArg Sigma.fst hw).trans (hover z)
  change germValue (s z) = f.toFun z
  rw [← hw, value_section, hwz]

/-- The purely topological end of the monodromy argument. Its covering
premise is a separate obligation, and is not a hypothesis of the main Spec. -/
theorem section_of_covering [SimplyConnectedSpace X]
    (hcover : IsCoveringMap (germProjection (g := g) (h := h)))
    (a : GermSpace g h) :
    ∃ s : C(X, GermSpace g h), s a.1 = a ∧
      (∀ x, germProjection (s x) = x) ∧
      ∀ x, ∃ f : LocalRepresentative g h,
        x ∈ f.domain ∧ (germValue ∘ s) =ᶠ[𝓝 x] f.toFun := by
  let : LocallyPathConnectedSpace X :=
    SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  obtain ⟨s, ⟨hsa, hs⟩, _⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) a.1 a rfl
  have hover : ∀ x, germProjection (s x) = x := congrFun hs
  exact ⟨s, hsa, hover, section_locally_represented s s.continuous hover⟩

/-- Evaluation of a continuous germ section is a global smooth local
isometry, with the literal differential and inverse clauses. -/
theorem isLocalIsometry_section_value (s : X → GermSpace g h) (hs : Continuous s)
    (hover : ∀ x, germProjection (s x) = x) :
    IsLocalIsometryOn g h (germValue ∘ s) Set.univ := by
  apply isLocalIsometryOn_of_locally_represented isOpen_univ
  intro p _
  rcases section_locally_represented s hs hover p with ⟨f, hp, heq⟩
  exact ⟨f.toFun, f.domain, f.isLocalIsometry, hp, heq⟩

/-- A section through a prescribed initial germ retains all the prescribed
first-order data, including the tangent-fiber transport. -/
theorem section_value_hasCenterData (s : X → GermSpace g h) (hs : Continuous s)
    (hover : ∀ x, germProjection (s x) = x)
    (f : LocalRepresentative g h) (x : f.domain)
    (hinitial : s x.val = f.sectionMap x) (y : M)
    (A : TangentSpace S x.val ≃ₗ[ℝ] TangentSpace T y)
    (hcenter : HasCenterData f.toFun x.val y A) :
    HasCenterData (germValue ∘ s) x.val y A := by
  have hnear : ∀ᶠ z in 𝓝 x.val, s z ∈ Set.range f.sectionMap :=
    hs.continuousAt.preimage_mem_nhds
      ((section_range_open f).mem_nhds (hinitial ▸ Set.mem_range_self x))
  apply hasCenterData_congr_germ hcenter
  filter_upwards [hnear] with z hz
  rcases hz with ⟨w, hw⟩
  have hwz : w.val = z := (congrArg Sigma.fst hw).trans (hover z)
  change f.toFun z = germValue (s z)
  rw [← hw, value_section, hwz]

/-- Once the covering-of-germs obligation has been proved, this supplies the
entire prescribed global development conclusion. The covering premise occurs
only in this reduction lemma, never in the independent target specification. -/
theorem development_of_germ_covering [SimplyConnectedSpace X]
    (hcover : IsCoveringMap (germProjection (g := g) (h := h)))
    (f : LocalRepresentative g h) (x : f.domain) (y : M)
    (A : TangentSpace S x.val ≃ₗ[ℝ] TangentSpace T y)
    (hcenter : HasCenterData f.toFun x.val y A) :
    ∃ F : X → M, IsLocalIsometryOn g h F Set.univ ∧ HasCenterData F x.val y A := by
  obtain ⟨s, hs, hover, _⟩ := section_of_covering hcover (f.sectionMap x)
  exact ⟨germValue ∘ s, isLocalIsometry_section_value s s.continuous hover,
    section_value_hasCenterData s s.continuous hover f x hs y A hcenter⟩

/-- Closedness of the coincidence locus follows from continuity of the actual
tangent maps; local uniqueness identifies that closed first-jet locus with the
ordinary germ-coincidence locus. -/
theorem totalMap_eq_of_germ {f k : X → M} {p : X}
    (hf : IsSmoothMap S T f) (hk : IsSmoothMap S T k)
    (L : (q : X) → TangentSpace S q →ₗ[ℝ] TangentSpace T (f q))
    (K : (q : X) → TangentSpace S q →ₗ[ℝ] TangentSpace T (k q))
    (hL : ∀ q, IsDifferential S T f q (L q))
    (hK : ∀ q, IsDifferential S T k q (K q))
    (he : f =ᶠ[𝓝 p] k) (v : TangentSpace S p) :
    (⟨f p, L p v⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace T)) =
      ⟨k p, K p v⟩ := by
  have hh : (castTangent T he.eq_of_nhds).toLinearMap.comp (L p) = K p :=
    (SmoothManifolds.differential_exists S T k hk p).unique
      (isDifferential_congr_germ he (hL p)) (hK p)
  rw [← hh]
  have aux (z w : M) (e : z = w) (v : TangentSpace T z) :
      (⟨z, v⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace T)) =
        ⟨w, castTangent T e v⟩ := by subst w; rfl
  exact aux (f p) (k p) he.eq_of_nhds (L p v)

theorem global_germ_closed
    (huniq : P202Specs.Geometry.LocalSpaceFormDevelopment.germUniquenessType.{u})
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f k : X → M) (hf : IsLocalIsometry g h f) (hk : IsLocalIsometry g h k) :
    IsClosed {p : X | f =ᶠ[𝓝 p] k} := by
  obtain ⟨L, hL, hmL⟩ := hf.2
  obtain ⟨K, hK, hmK⟩ := hk.2
  let E := Bundle.TotalSpace (Euclidean n) (TangentSpace T)
  letI : T2Space E := (tangentRealization T).space.bundle.totalManifold.topologicalManifold.hausdorff
  let F (Y : Field S) (p : X) : E := ⟨f p, L p (Y.val p)⟩
  let G (Y : Field S) (p : X) : E := ⟨k p, K p (Y.val p)⟩
  have hF (Y : Field S) : Continuous (F Y) := by
    have hh := P202.Geometry.SmoothMetrics.differential_totalMap_smooth f hf.1.1 L hL
    have hc : Continuous (fun q : Bundle.TotalSpace (Euclidean n) (TangentSpace S) =>
        (⟨f q.proj, L q.proj q.snd⟩ : E)) :=
      continuous_iff_continuousAt.mpr (fun q => (hh q).1)
    have hy : Continuous (fun p : X =>
        (⟨p, Y.val p⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) :=
      continuous_iff_continuousAt.mpr (fun p => (Y.property p).1)
    exact hc.comp hy
  have hG (Y : Field S) : Continuous (G Y) := by
    have hh := P202.Geometry.SmoothMetrics.differential_totalMap_smooth k hk.1.1 K hK
    have hc : Continuous (fun q : Bundle.TotalSpace (Euclidean n) (TangentSpace S) =>
        (⟨k q.proj, K q.proj q.snd⟩ : E)) :=
      continuous_iff_continuousAt.mpr (fun q => (hh q).1)
    have hy : Continuous (fun p : X =>
        (⟨p, Y.val p⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) :=
      continuous_iff_continuousAt.mpr (fun p => (Y.property p).1)
    exact hc.comp hy
  have hclosed : IsClosed {p : X | ∀ Y : Field S, F Y p = G Y p} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun Y => isClosed_eq (hF Y) (hG Y))
  convert hclosed using 1
  ext p
  constructor
  · intro hp Y
    exact totalMap_eq_of_germ hf.1.1 hk.1.1 L K hL hK hp (Y.val p)
  · intro hp
    have hpoint : f p = k p := congrArg Bundle.TotalSpace.proj (hp 0)
    have htotal (v : TangentSpace S p) :
        (⟨f p, L p v⟩ : E) = ⟨k p, K p v⟩ := by
      obtain ⟨Y, hY⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective
        (tangentBundle S) p v
      simpa only [F, G, hY] using hp Y
    have hcast : (castTangent T hpoint).toLinearMap.comp (L p) = K p := by
      have aux (z w : M) (e : z = w)
          (A : TangentSpace S p →ₗ[ℝ] TangentSpace T z)
          (B : TangentSpace S p →ₗ[ℝ] TangentSpace T w)
          (he : ∀ v, (⟨z, A v⟩ : E) = ⟨w, B v⟩) :
          (castTangent T e).toLinearMap.comp A = B := by
        subst w
        apply LinearMap.ext
        intro v
        change A v = B v
        exact Bundle.TotalSpace.mk_injective z (he v)
      exact aux (f p) (k p) hpoint (L p) (K p) htotal
    letI := (SmoothManifolds.tangent_dimension S p).1
    letI := (SmoothManifolds.tangent_dimension T (f p)).1
    have hdim : Module.finrank ℝ (TangentSpace S p) =
        Module.finrank ℝ (TangentSpace T (f p)) :=
      (SmoothManifolds.tangent_dimension S p).2.trans
        (SmoothManifolds.tangent_dimension T (f p)).2.symm
    let A := LinearEquiv.ofBijective (L p)
      (P202.Geometry.LocalSpaceFormDevelopment.metric_linearMap_bijective
        (V := TangentSpace S p) (W := TangentSpace T (f p))
        (pairing g p) (pairing h (f p)) (g.positive p) (L p) (hmL p) hdim)
    have hcF : HasCenterData f p (f p) A := ⟨rfl, hL p⟩
    have hcG : HasCenterData k p (f p) A := by
      refine ⟨hpoint.symm, ?_⟩
      have hh (z w : M) (e : z = w) :
          (castTangent T e.symm).symm = castTangent T e := by subst w; rfl
      rw [hh]
      change IsDifferential S T k p ((castTangent T hpoint).toLinearMap.comp (L p))
      rw [hcast]
      exact hK p
    have hfOn : IsLocalIsometryOn g h f univ :=
      ⟨isOpen_univ, fun q _ => ⟨hf.1.1 q, hf.1.2 q, L q, hL q, hmL q⟩⟩
    have hkOn : IsLocalIsometryOn g h k univ :=
      ⟨isOpen_univ, fun q _ => ⟨hk.1.1 q, hk.1.2 q, K q, hK q, hmK q⟩⟩
    exact huniq S T g h f k univ univ hfOn hkOn p trivial trivial (f p) A hcF hcG

theorem local_germ_closed
    (huniq : P202Specs.Geometry.LocalSpaceFormDevelopment.germUniquenessType.{u})
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f k : X → M) (U : Set X)
    (hf : IsLocalIsometryOn g h f U) (hk : IsLocalIsometryOn g h k U) :
    IsClosed {p : U | f =ᶠ[𝓝 p.val] k} := by
  obtain ⟨R, E, gR, hE, hgR, hrestrict⟩ :=
    P202.Geometry.LocalSpaceFormDevelopment.Localization.open_metric_localization S T g h U hf.1
  have hc := global_germ_closed huniq gR h (f ∘ Subtype.val) (k ∘ Subtype.val)
    (hrestrict f hf) (hrestrict k hk)
  convert hc using 1
  ext p
  change (f =ᶠ[𝓝 p.val] k) ↔ ((f ∘ Subtype.val) =ᶠ[𝓝 p] (k ∘ Subtype.val))
  rw [← hf.1.isOpenEmbedding_subtypeVal.map_nhds_eq p]
  rfl

end Locality

section NormalCharts
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {S : SmoothManifold n .euclidean X}

/-- Restriction preserves membership in the given maximal smooth atlas. -/
theorem chart_restrict_mem (c : ModelChart n .euclidean X)
    (hc : c ∈ S.smoothStructure.val) (W : Set X) (hW : IsOpen W) :
    c.restrOpen W hW ∈ S.smoothStructure.val := by
  have hm : c.restrOpen W hW ∈ maximalExtension (⊤ : ℕ∞) S.smoothStructure.val := by
    intro d hd
    apply SmoothManifolds.contDiffCompatible_of_germs
    · intro p hp hpd
      exact SmoothManifolds.chartContDiffAt_of_compatible
        (S.smoothStructure.property.1.2 c hc d hd) hp.1 hpd
    · intro p hpd hp
      exact SmoothManifolds.chartContDiffAt_of_compatible
        (S.smoothStructure.property.1.2 d hd c hc) hpd hp.1
  have hmax := S.smoothStructure.property.2 _
    (SmoothManifolds.maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
    (SmoothManifolds.subset_maximalExtension S.smoothStructure.property.1)
  change c.restrOpen W hW ∈ SmoothManifolds.maximalExtension (⊤ : ℕ∞) S.smoothStructure.val at hm
  rwa [hmax] at hm

/-- A supplied normal chart can be shrunk to any smaller positive radius,
while retaining the original smooth atlas and literal exponential formula. -/
theorem normal_chart_shrink (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : X) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hE : IsOrthonormalCoordinates g p E)
    (R : ℝ) (c : ModelChart n .euclidean X) (hc : IsNormalChart g F p E R c)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ d : ModelChart n .euclidean X, IsNormalChart g F p E r d ∧ d.source ⊆ c.source := by
  rcases hc with ⟨hR, hcm, hps, hcp, htarget, hformula⟩
  let W : Set X := c.source ∩ {z | tangentNorm g p (E.symm (c z).val) < r}
  have hcoord : ContinuousOn (fun z => (c z).val) c.source :=
    continuous_subtype_val.comp_continuousOn c.continuousOn
  have hnorm :=
    (ExponentialNormalCoordinates.orthonormal_norm_continuous g p E hE).comp_continuousOn hcoord
  have hW : IsOpen W := hnorm.isOpen_inter_preimage c.open_source isOpen_Iio
  let d := c.restrOpen W hW
  have hpW : p ∈ W := by
    refine ⟨hps, ?_⟩
    change tangentNorm g p (E.symm (c p).val) < r
    simpa only [hcp, map_zero, SmoothMetrics.tangentNorm_zero] using hr
  refine ⟨d, ⟨hr, chart_restrict_mem c hcm W hW, ⟨hps, hpW⟩, hcp, ?_, ?_⟩, ?_⟩
  · ext z
    change (z ∈ c.target ∧ c.symm z ∈ W) ↔ tangentNorm g p (E.symm z.val) < r
    constructor
    · rintro ⟨hzt, _, hz⟩
      change tangentNorm g p (E.symm (c (c.symm z)).val) < r at hz
      simpa only [c.right_inv hzt] using hz
    · intro hz
      have hzt : z ∈ c.target := by rw [htarget]; exact lt_of_lt_of_le hz hrR
      exact ⟨hzt, c.map_target hzt, by
        change tangentNorm g p (E.symm (c (c.symm z)).val) < r
        rwa [c.right_inv hzt]⟩
  · intro z hz
    exact hformula z (lt_of_lt_of_le hz hrR)
  · exact fun _ hz => hz.1

/-- The model-radius bound imposes no obstruction to choosing a sufficiently
small positive normal radius, for any real curvature. -/
theorem belowModelRadius_exists_lt (k R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, r < R ∧ BelowModelRadius k r := by
  by_cases hk : 0 < k
  · have hb : 0 < Real.pi / Real.sqrt k := div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)
    obtain ⟨r, hr, hbound⟩ := exists_between (lt_min hR hb)
    exact ⟨r, (lt_min_iff.mp hbound).1, hr, fun _ => (lt_min_iff.mp hbound).2⟩
  · obtain ⟨r, hr, hrR⟩ := exists_between hR
    exact ⟨r, hrR, hr, fun h => False.elim (hk h)⟩

/-- Normal charts below the curvature-model radius are consequences of the
accepted normal-coordinate theorem; no extra chart assumption is needed. -/
theorem normal_chart_exists_below (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : X) (k : ℝ) :
    ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r : ℝ)
      (d : ModelChart n .euclidean X),
      IsOrthonormalCoordinates g p E ∧ BelowModelRadius k r ∧ IsNormalChart g F p E r d := by
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_exists S g p
  obtain ⟨R, c, hc⟩ := ExponentialNormalCoordinates.normal_chart_exists S g C hC F hF p E hE
  obtain ⟨r, hrR, hr⟩ := belowModelRadius_exists_lt k R hc.1
  obtain ⟨d, hd, _⟩ := normal_chart_shrink g F p E hE R c hc r hr.1 hrR.le
  exact ⟨E, r, d, hE, hr, hd⟩

end NormalCharts

section InitialGerm
variable {n : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
  [ConnectedSpace M]

/-- The initial germ with its prescribed differential is supplied by the
local development premise, with the complete original quantifiers on that
premise. The normal chart is explicit here; the global Spec assumes none. -/
theorem prescribed_germ
    (hdevelopment : P202Specs.Geometry.LocalSpaceFormDevelopment.developmentType.{u})
    (hn : 2 ≤ n)
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hg : ConstantSectional g R k) (hh : ConstantSectional h Q k)
    (hcomplete : LengthMetricComplete h)
    (F : CurveFamily (Phase S)) (G : CurveFamily (Phase T))
    (hF : IsMaximalFamily S C F) (hG : IsMaximalFamily T D G)
    (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hA : ∀ v w, pairing h y (A v) (A w) = pairing g x v w)
    (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g x E)
    (r : ℝ) (d : ModelChart n .euclidean X)
    (hr : BelowModelRadius k r) (hd : IsNormalChart g F x E r d) :
    ∃ a : GermSpace g h, germProjection a = x ∧ germValue a = y ∧
      ∃ (f : LocalRepresentative g h) (hx : x ∈ f.domain),
        a = f.sectionMap ⟨x, hx⟩ ∧ f.domain = d.source ∧ HasCenterData f.toFun x y A := by
  obtain ⟨hloc, hcenter⟩ := hdevelopment hn S T g h C D hC hD R Q hR hQ
    k hg hh hcomplete F G hF hG x y A hA E hE r d hr hd
  let f : LocalRepresentative g h := ⟨development G x y A E d, d.source, hloc⟩
  let hx : x ∈ f.domain := hd.2.2.1
  refine ⟨f.sectionMap ⟨x, hx⟩, rfl, hcenter.choose, f, hx, rfl, rfl, hcenter⟩

/-- An actual representative with arbitrary prescribed metric first-order
data exists under the original geometric hypotheses and the local development
premise. Families, orthonormal coordinates and the normal chart are derived. -/
theorem prescribed_representative_exists
    (hdevelopment : P202Specs.Geometry.LocalSpaceFormDevelopment.developmentType.{u})
    (hn : 2 ≤ n)
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hg : ConstantSectional g R k) (hh : ConstantSectional h Q k)
    (hcomplete : LengthMetricComplete h)
    (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hA : ∀ v w, pairing h y (A v) (A w) = pairing g x v w) :
    ∃ (f : LocalRepresentative g h), x ∈ f.domain ∧ HasCenterData f.toFun x y A := by
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨G, hG⟩ := ExponentialNormalCoordinates.family_exists T D
  obtain ⟨E, r, d, hE, hr, hd⟩ := normal_chart_exists_below g C hC F hF x k
  obtain ⟨a, _, _, f, hx, _, _, hcenter⟩ := prescribed_germ hdevelopment hn S T g h C D hC hD
    R Q hR hQ k hg hh hcomplete F G hF hG x y A hA E hE r d hr hd
  exact ⟨f, hx, hcenter⟩

/-- The full germ-extension premise gives extension of any actual germ,
not only of germs whose center differential has already been chosen. -/
theorem extend_germ_on_normal_chart
    (hextension : P202Specs.Geometry.LocalSpaceFormDevelopment.germExtensionType.{u})
    (hn : 2 ≤ n)
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hg : ConstantSectional g R k) (hh : ConstantSectional h Q k)
    (hcomplete : LengthMetricComplete h)
    (F : CurveFamily (Phase S)) (G : CurveFamily (Phase T))
    (hF : IsMaximalFamily S C F) (hG : IsMaximalFamily T D G)
    (a : GermSpace g h)
    (E : TangentSpace S a.1 ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g a.1 E)
    (r : ℝ) (d : ModelChart n .euclidean X)
    (hr : BelowModelRadius k r) (hd : IsNormalChart g F a.1 E r d) :
    ∃ f : LocalRepresentative g h, f.domain = d.source ∧
      ∃ ha : a.1 ∈ f.domain, f.sectionMap ⟨a.1, ha⟩ = a := by
  rcases germ_has_representative a with ⟨f, z, hz⟩
  have hza : z.val = a.1 := congrArg germProjection hz
  have ha : a.1 ∈ f.domain := hza ▸ z.property
  have hfa : f.sectionMap ⟨a.1, ha⟩ = a := by
    have hzz : (⟨a.1, ha⟩ : f.domain) = z := Subtype.ext hza.symm
    rw [hzz]
    exact hz
  obtain ⟨A, _, _, hloc, heq⟩ := hextension hn S T g h C D hC hD R Q hR hQ
    k hg hh hcomplete F G hF hG a.1 f.toFun f.domain f.isLocalIsometry ha E hE r d hr hd
  let e : LocalRepresentative g h := ⟨development G a.1 (f.toFun a.1) A E d, d.source, hloc⟩
  refine ⟨e, rfl, hd.2.2.1, ?_⟩
  have hgerm := (germ_eq_iff e f a.1 hd.2.2.1 ha).mpr heq.symm
  exact (congrArg (Sigma.mk a.1) hgerm).trans hfa

/-- The source proof's common-ball construction can be supplied as a family
of normal charts containing one fixed open set. Restricting the extensions
then gives exactly the common-domain continuation used in the covering lemma. -/
theorem continuation_on_common_normal_neighborhood
    (hextension : P202Specs.Geometry.LocalSpaceFormDevelopment.germExtensionType.{u})
    (hn : 2 ≤ n)
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hg : ConstantSectional g R k) (hh : ConstantSectional h Q k)
    (hcomplete : LengthMetricComplete h)
    (F : CurveFamily (Phase S)) (G : CurveFamily (Phase T))
    (hF : IsMaximalFamily S C F) (hG : IsMaximalFamily T D G)
    (U : Set X) (hU : IsOpen U)
    (hcharts : ∀ z ∈ U, ∃ (E : TangentSpace S z ≃ₗ[ℝ] Euclidean n)
      (r : ℝ) (d : ModelChart n .euclidean X),
      IsOrthonormalCoordinates g z E ∧ BelowModelRadius k r ∧
      IsNormalChart g F z E r d ∧ U ⊆ d.source) :
    ∀ a : GermSpace g h, germProjection a ∈ U →
      ∃ f : LocalRepresentative g h, f.domain = U ∧
        ∃ ha : a.1 ∈ f.domain, f.sectionMap ⟨a.1, ha⟩ = a := by
  intro a haU
  obtain ⟨E, r, d, hE, hr, hd, hUd⟩ := hcharts a.1 haU
  obtain ⟨f, hfdom, hfa, hfeq⟩ := extend_germ_on_normal_chart hextension hn S T g h C D
    hC hD R Q hR hQ k hg hh hcomplete F G hF hG a E hE r d hr hd
  have hUf : U ⊆ f.domain := hfdom.symm ▸ hUd
  let e := f.restrict U hU hUf
  refine ⟨e, rfl, haU, ?_⟩
  exact hfeq

end InitialGerm

section CommonNormalBalls
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {S : SmoothManifold n .euclidean X}

theorem normal_chart_source_preconnected (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : X)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (r : ℝ) (d : ModelChart n .euclidean X)
    (hd : IsNormalChart g F p E r d) : IsPreconnected d.source := by
  let B : Set (Euclidean n) := {z | tangentNorm g p (E.symm z) < r}
  have hstar : StarConvex ℝ 0 B := by
    rw [starConvex_zero_iff]
    intro z hz a ha ha1
    change tangentNorm g p (E.symm (a • z)) < r
    rw [map_smul, SmoothMetrics.tangentNorm_smul, abs_of_nonneg ha]
    exact (mul_le_of_le_one_left (SmoothMetrics.tangentNorm_nonneg g p (E.symm z)) ha1).trans_lt hz
  have hz : (0 : Euclidean n) ∈ B := by
    simpa only [B, mem_ofPred_eq, map_zero, SmoothMetrics.tangentNorm_zero] using hd.1
  have hB : IsPreconnected B := (hstar.isPathConnected hz).isConnected.isPreconnected
  let incl : Euclidean n → ModelSpace n .euclidean := fun z => ⟨z, mem_univ _⟩
  have hincl : Continuous incl := continuous_id.subtype_mk _
  have htarget : incl '' B = d.target := by
    rw [hd.2.2.2.2.1]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨z.val, hz, by apply Subtype.ext; rfl⟩
  have ht : IsPreconnected d.target := htarget ▸ hB.image incl hincl.continuousOn
  rw [← d.symm_image_target_eq_source]
  exact ht.image d.symm d.symm.continuousOn

theorem normal_chart_distance_lt (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : X) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (r : ℝ) (d : ModelChart n .euclidean X)
    (hd : IsNormalChart g F p E r d) (q : X) (hq : q ∈ d.source) :
    lengthDistance g p q < r := by
  obtain ⟨hv, heq⟩ := NormalMinimality.normal_chart_inverse g F p E r d hd q hq
  obtain ⟨γ, h0, h1, _, _, _, hL⟩ :=
    NormalMinimality.radial_segment_exists S g C hC F hF p E r d hd _ hv
  have hbound := CompleteExponentialMinimizers.lengthDistance_le_length g γ
  rw [h0, h1, heq, hL] at hbound
  exact hbound.trans_lt hv

theorem common_normal_neighborhood_of_uniform [PreconnectedSpace X]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (k : ℝ)
    (huniform : ∃ R : ℝ, BelowModelRadius k R ∧ ∀ p : X,
      ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (c : ModelChart n .euclidean X),
        IsOrthonormalCoordinates g p E ∧ IsNormalChart g F p E R c ∧
        c.source = {q : X | lengthDistance g p q < R})
    (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsPreconnected U ∧
      ∀ z ∈ U, ∃ (E : TangentSpace S z ≃ₗ[ℝ] Euclidean n)
        (r : ℝ) (d : ModelChart n .euclidean X),
        IsOrthonormalCoordinates g z E ∧ BelowModelRadius k r ∧
        IsNormalChart g F z E r d ∧ U ⊆ d.source := by
  obtain ⟨R, hR, hcharts⟩ := huniform
  obtain ⟨E, c, hE, hc, hsource⟩ := hcharts x
  obtain ⟨d, hd, _⟩ := normal_chart_shrink g F x E hE R c hc (R / 3)
    (by linarith [hR.1]) (by linarith [hR.1])
  refine ⟨d.source, hd.2.2.1, d.open_source,
    normal_chart_source_preconnected g F x E (R / 3) d hd, ?_⟩
  intro z hz
  obtain ⟨E', c', hE', hc', hsource'⟩ := hcharts z
  refine ⟨E', R, c', hE', hR, hc', ?_⟩
  intro y hy
  rw [hsource']
  have hzR := normal_chart_distance_lt g C hC F hF x E (R / 3) d hd z hz
  have hyR := normal_chart_distance_lt g C hC F hF x E (R / 3) d hd y hy
  have htri := CompleteExponentialMinimizers.lengthDistance_triangle g z x y
  rw [CompleteExponentialMinimizers.lengthDistance_comm g z x] at htri
  change lengthDistance g z y < R
  linarith [hR.1]


end CommonNormalBalls

theorem positive_model_radius_pos {k : ℝ} (hk : 0 < k) : 0 < 1 / Real.sqrt k :=
  one_div_pos.mpr (Real.sqrt_pos.mpr hk)

theorem positive_model_radius_curvature {k : ℝ} (hk : 0 < k) :
    ((1 / Real.sqrt k) ^ 2)⁻¹ = k := by
  rw [one_div, inv_pow, inv_inv, Real.sq_sqrt hk.le]

theorem negative_model_radius_pos {k : ℝ} (hk : k < 0) : 0 < 1 / Real.sqrt (-k) :=
  positive_model_radius_pos (neg_pos.mpr hk)

theorem negative_model_radius_curvature {k : ℝ} (hk : k < 0) :
    -((1 / Real.sqrt (-k)) ^ 2)⁻¹ = k := by
  rw [positive_model_radius_curvature (neg_pos.mpr hk), neg_neg]


/-- The proved model charts supply a single positive normal radius,
uniformly at every center. -/
theorem uniform_normal_balls_of_global {n : ℕ} {X : Type u} [TopologicalSpace X]
    {S : SmoothManifold n .euclidean X} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hgeometry : GlobalNormalGeometry g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (k : ℝ) :
    ∃ r : ℝ, BelowModelRadius k r ∧ ∀ p : X,
      ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (c : ModelChart n .euclidean X),
        IsOrthonormalCoordinates g p E ∧ IsNormalChart g F p E r c ∧
        c.source = {q : X | modelDistance g p q < r} := by
  obtain ⟨r, _, hr⟩ := belowModelRadius_exists_lt k 1 (by norm_num)
  refine ⟨r, hr, ?_⟩
  intro p
  obtain ⟨E, c, hE, _, _, _, _, _, _, hballs⟩ := hgeometry F hF p
  obtain ⟨d, hd, hsource⟩ := hballs r hr.1
  exact ⟨E, d, hE, hd, hsource⟩

theorem uniform_normal_balls_of_spherical {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A) (ha : 0 < a)
    (hgeometry : SphericalNormalGeometry B)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (k : ℝ) :
    ∃ r : ℝ, BelowModelRadius k r ∧ ∀ p : Sphere n a,
      ∃ (E : TangentSpace B.manifold p ≃ₗ[ℝ] Euclidean n)
        (c : ModelChart n .euclidean (Sphere n a)),
        IsOrthonormalCoordinates B.metric p E ∧ IsNormalChart B.metric F p E r c ∧
        c.source = {q | modelDistance B.metric p q < r} := by
  obtain ⟨r, hra, hr⟩ := belowModelRadius_exists_lt k (Real.pi * a) (mul_pos Real.pi_pos ha)
  refine ⟨r, hr, ?_⟩
  intro p
  obtain ⟨E, c, hE, _, _, _, _, _, _, _, _, hballs⟩ := hgeometry F hF p
  obtain ⟨d, hd, hsource⟩ := hballs r hr.1 hra
  exact ⟨E, d, hE, hd, hsource⟩

/-- The complete continuation argument on a source with the proved model
normal balls. This is an internal reduction; its geometric premise is discharged
by the three actual model theorems in the public result. -/
theorem development_of_uniform_normal_balls {n : ℕ} (hn : 2 ≤ n)
    {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
    [SimplyConnectedSpace X] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hg : ConstantSectional g R k) (hh : ConstantSectional h Q k)
    (hcomplete : LengthMetricComplete h)
    (huniform : ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
      ∃ r : ℝ, BelowModelRadius k r ∧ ∀ p : X,
        ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (c : ModelChart n .euclidean X),
          IsOrthonormalCoordinates g p E ∧ IsNormalChart g F p E r c ∧
          c.source = {q : X | modelDistance g p q < r})
    (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hA : ∀ v w, pairing h y (A v) (A w) = pairing g x v w) :
    ∃ f : X → M, IsLocalIsometryOn g h f univ ∧ HasCenterData f x y A := by
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨G, hG⟩ := ExponentialNormalCoordinates.family_exists T D
  have hcover : IsCoveringMap (germProjection (g := g) (h := h)) := by
    apply projection_covering_of_continuation
    intro p
    obtain ⟨U, hpU, hU, hconnected, hcharts⟩ :=
      common_normal_neighborhood_of_uniform g C hC F hF k (huniform F hF) p
    refine ⟨U, hpU, hU, hconnected, ?_, ?_⟩
    · exact continuation_on_common_normal_neighborhood
        P202.Geometry.LocalSpaceFormDevelopment.germ_extension hn S T g h C D
        hC hD R Q hR hQ k hg hh hcomplete F G hF hG U hU hcharts
    · intro f j hf hj
      have hf' : IsLocalIsometryOn g h f.toFun U := hf ▸ f.isLocalIsometry
      have hj' : IsLocalIsometryOn g h j.toFun U := hj ▸ j.isLocalIsometry
      exact local_germ_closed
        P202.Geometry.LocalSpaceFormDevelopment.germ_uniqueness g h f.toFun j.toFun U hf' hj'
  obtain ⟨f, hx, hcenter⟩ := prescribed_representative_exists
    P202.Geometry.LocalSpaceFormDevelopment.development hn S T g h C D hC hD
    R Q hR hQ k hg hh hcomplete x y A hA
  exact development_of_germ_covering hcover f ⟨x, hx⟩ y A hcenter


theorem hyperbolic_source_curvature {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (P202.HyperboloidData.Hyperboloid n a))
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hS : HasProjectionChart S) (hg : P202.HyperboloidData.IsInduced g) (hC : IsLeviCivita g C) :
    ∃ R : CurvatureTensor S, RepresentsCurvature C R ∧ ConstantSectional g R (-(a^2)⁻¹) := by
  obtain ⟨c, hc, hs, ht, hproj⟩ := hS
  obtain ⟨R, hR, _⟩ := CurvatureAlgebra.tensor_exists_unique C
  refine ⟨R, hR, ?_⟩
  intro p x y hxy
  have hden : pairing g p x x * pairing g p y y - pairing g p x y ^ 2 ≠ 0 :=
    ne_of_gt (SectionalRecovery.gram_pos (pairing g p) (g.symmetric p) (g.positive p) x y hxy)
  have hfield := HyperboloidModel.constant_sectional_curvature ha S c hc hs hproj g hg C hC
    (CurvatureAlgebra.fieldLift p x) (CurvatureAlgebra.fieldLift p y) p
    (by simpa only [CurvatureAlgebra.fieldLift_value] using hden)
  have hrep := hR (CurvatureAlgebra.fieldLift p x) (CurvatureAlgebra.fieldLift p y)
    (CurvatureAlgebra.fieldLift p y) p
  simp only [CurvatureAlgebra.fieldLift_value] at hfield hrep
  unfold sectionalCurvature curvatureForm
  rw [hrep]
  exact hfield


theorem euclidean_development :
    P202Specs.Geometry.GlobalSpaceFormDevelopment.euclideanDevelopmentType := by
  intro n hn G hG M _ _ T h D hD Q hQ hh hc x y A hA
  letI : SimplyConnectedSpace (E n) := hG.2.1
  obtain ⟨R, hR, hg⟩ := hG.2.2.2.1
  have hgeometry := (ModelPolarDomains.euclidean_geometry n hn G hG).1
  exact development_of_uniform_normal_balls hn G.manifold T G.metric h G.connection D
    G.leviCivita hD R Q hR hQ 0 hg hh hc
    (fun F hF => uniform_normal_balls_of_global G.metric G.connection hgeometry F hF 0)
    x y A hA

theorem spherical_development :
    P202Specs.Geometry.GlobalSpaceFormDevelopment.sphericalDevelopmentType := by
  intro n hn k hk A B hB M _ _ T h D hD Q hQ hh hc x y L hL
  have ha := positive_model_radius_pos hk
  letI : SimplyConnectedSpace (Sphere n (1 / Real.sqrt k)) := hB.2.1
  obtain ⟨R, hR, hg⟩ := hB.2.2.2.1
  have hcurv : ConstantSectional B.metric R k := by
    simpa only [ConstantSectional, positive_model_radius_curvature hk] using hg
  have hgeometry := (ModelPolarDomains.spherical_geometry n hn _ ha A B hB).1
  exact development_of_uniform_normal_balls hn B.manifold T B.metric h B.connection D
    B.leviCivita hD R Q hR hQ k hcurv hh hc
    (fun F hF => uniform_normal_balls_of_spherical B ha hgeometry F hF k)
    x y L hL

theorem hyperbolic_development :
    P202Specs.Geometry.GlobalSpaceFormDevelopment.hyperbolicDevelopmentType := by
  intro n hn k hk S g hS hg M _ _ T h D hD Q hQ hh hc x y A hA
  have ha := negative_model_radius_pos hk
  letI : SimplyConnectedSpace (P202.HyperboloidData.Hyperboloid n (1 / Real.sqrt (-k))) :=
    (HyperboloidModel.topology n _ ha).2
  obtain ⟨C, hC, _⟩ := LeviCivita.exists_unique g
  obtain ⟨R, hR, hcurv⟩ := hyperbolic_source_curvature ha S g C hS hg hC
  have hcurv' : ConstantSectional g R k := by
    simpa only [negative_model_radius_curvature hk] using hcurv
  have hgeometry := (ModelPolarDomains.hyperbolic_geometry n hn _ ha S g C hS hg hC).1
  exact development_of_uniform_normal_balls hn S T g h C D hC hD R Q hR hQ k hcurv' hh hc
    (fun F hF => uniform_normal_balls_of_global g C hgeometry F hF k) x y A hA

/-- Global local-isometry development from each actual simply connected model,
with every prescribed value and metric differential. -/
theorem development :
    P202Specs.Geometry.GlobalSpaceFormDevelopment.developmentType :=
  ⟨euclidean_development, spherical_development, hyperbolic_development⟩


end P202.Geometry.GlobalSpaceFormDevelopment
