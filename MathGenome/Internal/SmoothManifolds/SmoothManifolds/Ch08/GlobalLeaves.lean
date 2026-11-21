import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.GlobalLeaves
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.Clopen

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.LeafStructures
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SmoothManifolds.GlobalLeaves
open ModelData AtlasData MapData MapClassData TangentData DifferentialData
  BundleOperationsData CovectorData DistributionData FrobeniusData LeafData
  GlobalLeafData BoundaryData FiniteRegularityData Set Filter
open scoped Topology
universe u

/-- The longitudinal projection associated to the shared plaque coordinates. -/
def longitudinalLinear {n k : ℕ} (hk : k ≤ n) : Euclidean n →L[ℝ] Euclidean k :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

/-- The transverse projection associated to the shared adapted coordinates. -/
def transverseLinear {n : ℕ} (k : ℕ) : Euclidean n →L[ℝ] Euclidean (n-k) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj ⟨k+j.val, by omega⟩

/-- Euclidean vectors as points of the shared boundaryless model. -/
def euclideanPoint {k : ℕ} (x : Euclidean k) : ModelSpace k .euclidean := ⟨x, mem_univ x⟩

theorem continuous_euclideanPoint (k : ℕ) : Continuous (euclideanPoint (k := k)) :=
  continuous_id.subtype_mk _

/-- The differential of an immersion is injective also in the intrinsic
(real derivation) realization of the tangent spaces. -/
theorem differential_injective {m n : ℕ} {a b : ModelKind} {N M : Type u}
    [TopologicalSpace N] [TopologicalSpace M]
    (R : SmoothManifold m a N) (S : SmoothManifold n b M) (f : N → M)
    (hf : IsSmoothMap R S f) (hi : IsImmersion R S f) (x : N)
    (L : TangentSpace R x →ₗ[ℝ] TangentSpace S (f x))
    (hL : IsDifferential R S f x L) : Function.Injective L := by
  obtain ⟨F, G, K, hK, hKi⟩ := (hi x).2
  letI := F.group
  letI := F.module
  letI := G.group
  letI := G.module
  obtain ⟨E, hE⟩ := FiniteRegularity.smooth_compatibility R x F
  obtain ⟨H, hH⟩ := FiniteRegularity.smooth_compatibility S (f x) G
  have hcomp := FiniteRegularity.smooth_differential_compatibility R S f hf x
    F G E H hE hH K L hK hL
  intro v w hvw
  apply E.symm.injective
  apply hKi
  apply H.injective
  simpa only [hcomp, LinearEquiv.apply_symm_apply] using hvw

/-- Every plaque is contained in the class of each of its points. -/
theorem plaque_subset_leaf {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (A : Set (ModelChart n .euclidean M)) (p : M)
    (e : ModelChart n .euclidean M) (he : e ∈ A) (z : Euclidean (n-k))
    (x : M) (hx : x ∈ leafSet A k p) (hxe : x ∈ coordinateSlice e k z) :
    coordinateSlice e k z ⊆ leafSet A k p := by
  intro y hy
  exact Relation.EqvGen.trans _ _ _ hx
    (Relation.EqvGen.rel _ _ ⟨e, he, z, hxe, hy⟩)

/-- The permitted source models are convex, including dimension zero. -/
theorem convex_modelSet (m : ℕ) (a : ModelKind) : Convex ℝ (modelSet m a) := by
  cases a with
  | euclidean => exact convex_univ
  | halfSpace =>
    cases m with
    | zero => exact convex_univ
    | succ m =>
      exact (convex_Ici (0 : ℝ)).linear_preimage
        (LinearMap.proj (Fin.last m) : Euclidean (m+1) →ₗ[ℝ] ℝ)

/-- An integral immersion has locally constant transverse coordinates in any
adapted target chart. The convex source neighborhood may be a half-ball. -/
theorem integral_immersion_locally_in_plaque
    {n k : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) {a : ModelKind} (R : SmoothManifold k a N)
    (f : N → M) (hf : IsIntegralImmersion D R f)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (had : IsAdaptedChart D d hd) (p : N) (hpd : f p ∈ d.source) :
    ∃ V : Set N, IsOpen V ∧ p ∈ V ∧
      ∀ q ∈ V, f q ∈ coordinateSlice d k (transverseCoordinates k (d (f p)).val) := by
  obtain ⟨e, he, hp⟩ := R.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hepU, F, hF, hrep⟩ := (hf.1 p).2 e he d hd hp hpd
  have hcoord : ContinuousAt (fun q => (e q).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hgood : ∀ᶠ q in 𝓝 p, F (e q).val = (d (f q)).val ∧ q ∈ e.source ∧
      f q ∈ d.source ∧ (e q).val ∈ U := by
    filter_upwards [hrep, e.open_source.mem_nhds hp,
      (hf.1 p).1.preimage_mem_nhds (d.open_source.mem_nhds hpd),
      hcoord.preimage_mem_nhds (hU.mem_nhds hepU)] with q hq hqe hqd hqU
    exact ⟨hq, hqe, hqd, hqU⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hgood
  have hVe : V ⊆ e.source := fun q hq => (hVsub hq).2.1
  have hopen := e.isOpen_image_of_subset_source hV hVe
  obtain ⟨W, hW, hWrep⟩ := hopen.image_val
  have hepW : (e p).val ∈ W := by
    have h : (e p).val ∈ Subtype.val '' (e '' V) := ⟨e p, ⟨p, hpV, rfl⟩, rfl⟩
    rw [hWrep] at h
    exact h.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.inter hW) (e p).val ⟨hepU, hepW⟩
  let B := Metric.ball (e p).val r ∩ modelSet k a
  let H := fun x => transverseCoordinates k (F x)
  have hBq (x : Euclidean k) (hx : x ∈ B) :
      ∃ q ∈ V, (e q).val = x := by
    have h : x ∈ Subtype.val '' (e '' V) := by
      rw [hWrep]
      exact ⟨(hball hx.1).2, hx.2⟩
    obtain ⟨y, ⟨q, hq, rfl⟩, hy⟩ := h
    exact ⟨q, hq, hy⟩
  obtain ⟨L, hL, hrange⟩ := hf.2.2
  have hzero (x : Euclidean k) (hx : x ∈ B) : fderiv ℝ H x = 0 := by
    obtain ⟨q, hq, heq⟩ := hBq x hx
    have hqe := hVe hq
    have hqd := (hVsub hq).2.2.1
    obtain ⟨E, hE⟩ := FiniteRegularity.exists_smooth_chart_coordinates R q e he hqe
    let G := C.tangent.fiberCoordinates.equiv d hd (f q) hqd
    have hrepq : (fun y => F (e y).val) =ᶠ[𝓝 q] (fun y => (d (f y)).val) := by
      filter_upwards [hV.mem_nhds hq] with y hy
      exact (hVsub hy).1
    have hsquare (v : TangentSpace R q) :
        G (L q v) = fderiv ℝ F x (E v) := by
      simpa only [heq] using differential_jacobian R S f hf.1 q (L q) (hL q)
        e d he hd hqe hqd E G hE (C.tangent.fiberCoordinates.isCoordinates d hd (f q) hqd)
        U F hU ((hVsub hq).2.2.2) hF hrepq v
    have hdF := ((hF.contDiffAt (hU.mem_nhds (hball hx.1).1)).differentiableAt
      (by simp)).hasFDerivAt
    have hdH := (transverseLinear k).hasFDerivAt.comp x hdF
    change fderiv ℝ (⇑(transverseLinear k) ∘ F) x = 0
    rw [hdH.fderiv]
    ext v j
    change transverseCoordinates k (fderiv ℝ F x v) j = 0
    have hmem : L q (E.symm v) ∈ D.fiber (f q) := by
      rw [← hrange q]
      exact LinearMap.mem_range_self _ _
    have hplane := (had (f q) hqd _).mp hmem
    rw [hsquare, LinearEquiv.apply_symm_apply] at hplane
    exact hplane ⟨k+j.val, by omega⟩ (by change k ≤ k+j.val; omega)
  have hHdiff : ∀ x ∈ B, DifferentiableAt ℝ H x := by
    intro x hx
    exact (transverseLinear k).differentiableAt.comp x
      ((hF.contDiffAt (hU.mem_nhds (hball hx.1).1)).differentiableAt (by simp))
  have hconst (x y : Euclidean k) (hx : x ∈ B) (hy : y ∈ B) : H x = H y := by
    have bound := ((convex_ball (e p).val r).inter (convex_modelSet k a)).norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0)
      (fun z hz => (hHdiff z hz).hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => by simp [hzero z hz]) hx hy
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, eq_comm] using bound
  let V' := V ∩ (fun q => (e q).val) ⁻¹' Metric.ball (e p).val r
  refine ⟨V', ?_, ⟨hpV, Metric.mem_ball_self hr⟩, ?_⟩
  · exact (continuous_subtype_val.comp_continuousOn (e.continuousOn.mono hVe)).isOpen_inter_preimage hV Metric.isOpen_ball
  · intro q hq
    refine ⟨(hVsub hq.1).2.2.1, ?_⟩
    have hh := hconst (e q).val (e p).val ⟨hq.2, (e q).property⟩
      ⟨Metric.mem_ball_self hr, (e p).property⟩
    change transverseCoordinates k (F (e q).val) = transverseCoordinates k (F (e p).val) at hh
    rwa [(hVsub hq.1).1, (hVsub hpV).1] at hh

/-- A connected integral immersion through one point of a class remains in
that class. This uses local plaque containment, not ambient embeddedness. -/
theorem integral_immersion_image_subset_leaf
    {n k : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ConnectedSpace N]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (A : Set (ModelChart n .euclidean M))
    (hA : IsCountableAdaptedAtlas D A) {a : ModelKind}
    (R : SmoothManifold k a N) (f : N → M) (hf : IsIntegralImmersion D R f)
    (p : M) (x₀ : N) (hx₀ : f x₀ ∈ leafSet A k p) :
    ∀ x, f x ∈ leafSet A k p := by
  have hloc (x : N) : ∃ V : Set N, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, SamePlaque A k (f x) (f y) := by
    obtain ⟨e, he, hxe⟩ := hA.2.1 (f x)
    obtain ⟨heS, had, _⟩ := hA.2.2 e he
    obtain ⟨V, hV, hxV, hpl⟩ := integral_immersion_locally_in_plaque D R f hf e heS had x hxe
    refine ⟨V, hV, hxV, fun y hy => ⟨e, he, _, ⟨hxe, rfl⟩, hpl y hy⟩⟩
  let Q := {x : N | f x ∈ leafSet A k p}
  have hopen : IsOpen Q := isOpen_iff_mem_nhds.mpr (by
    intro x hx
    obtain ⟨V, hV, hxV, hpl⟩ := hloc x
    apply mem_of_superset (hV.mem_nhds hxV)
    intro y hy
    exact Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ (hpl y hy)))
  have hcopen : IsOpen Qᶜ := isOpen_iff_mem_nhds.mpr (by
    intro x hx
    obtain ⟨V, hV, hxV, hpl⟩ := hloc x
    apply mem_of_superset (hV.mem_nhds hxV)
    intro y hy hpy
    exact hx (Relation.EqvGen.trans _ _ _ hpy
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hpl y hy)))))
  have hQ : Q = univ := (IsClopen.eq_univ ⟨by simpa only [compl_compl] using hcopen.isClosed_compl, hopen⟩ ⟨x₀, hx₀⟩)
  intro x
  change x ∈ Q
  rw [hQ]
  exact mem_univ x

/-- Plaque charts give smoothness of the set-theoretic lift. The proof also
establishes continuity for the prescribed, possibly finer, leaf topology. -/
theorem integral_immersion_lift_smooth
    {n k : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (A : Set (ModelChart n .euclidean M))
    (hA : IsCountableAdaptedAtlas D A) (p : M)
    (T : @SmoothManifold k .euclidean (leafSet A k p) (leafTopology A k p))
    (hcharts : HasPlaqueCharts A p T) {a : ModelKind}
    (R : SmoothManifold k a N) (f : N → M) (hf : IsIntegralImmersion D R f)
    (himage : ∀ x, f x ∈ leafSet A k p) :
    letI := leafTopology A k p
    IsSmoothMap R T (fun x => (⟨f x, himage x⟩ : leafSet A k p)) := by
  letI := leafTopology A k p
  let g : N → leafSet A k p := fun x => ⟨f x, himage x⟩
  intro x
  obtain ⟨d, hd, hxd⟩ := hA.2.1 (f x)
  obtain ⟨hdS, had, _⟩ := hA.2.2 d hd
  obtain ⟨V, hV, hxV, hpl⟩ := integral_immersion_locally_in_plaque D R f hf d hdS had x hxd
  let z := transverseCoordinates k (d (f x)).val
  have hsub : coordinateSlice d k z ⊆ leafSet A k p :=
    plaque_subset_leaf A p d hd z (f x) (himage x) ⟨hxd, rfl⟩
  obtain ⟨hk, c, hc, hsrc, hcoords⟩ := hcharts d hd z hsub
  have hgc (y : N) (hy : y ∈ V) : g y ∈ c.source := by
    rw [hsrc]
    exact hpl y hy
  have hcoord (y : N) (hy : y ∈ V) :
      (c (g y)).val = longitudinalLinear hk (d (f y)).val :=
    hcoords (g y) (hgc y hy)
  let u : N → ModelSpace k .euclidean := fun y =>
    euclideanPoint (longitudinalLinear hk (d (f y)).val)
  have hux : u x = c (g x) := Subtype.ext (hcoord x hxV).symm
  have hu : ContinuousAt u x := (continuous_euclideanPoint k).continuousAt.comp
    ((longitudinalLinear hk).continuous.continuousAt.comp
      (continuous_subtype_val.continuousAt.comp ((d.continuousAt hxd).comp (hf.1 x).1)))
  have heq : (fun y => c.symm (u y)) =ᶠ[𝓝 x] g := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    have huy : u y = c (g y) := Subtype.ext (hcoord y hy).symm
    rw [huy, c.left_inv (hgc y hy)]
  have hcont : ContinuousAt g x :=
    (((c.symm.continuousAt (hux.symm ▸ c.map_source (hgc x hxV))).comp hu).congr heq)
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    R.smoothStructure.property.1 T.smoothStructure.property.1 g x).mpr
  obtain ⟨e, he, hxe⟩ := R.smoothStructure.property.1.1 x
  obtain ⟨U, hU, hxU, F, hF, hrep⟩ := (hf.1 x).2 e he d hdS hxe hxd
  refine ⟨hcont, e, he, c, hc, hxe, hgc x hxV, U, hU, hxU,
    fun y => longitudinalLinear hk (F y),
    (longitudinalLinear hk).contDiff.comp_contDiffOn hF, ?_⟩
  filter_upwards [hrep, hV.mem_nhds hxV] with y hy hyV
  change longitudinalLinear hk (F (e y).val) = (c (g y)).val
  rw [hy, hcoord y hyV]

/-- Intrinsic differential isomorphisms give local inverses at interior points,
using the supplied inverse theorem for the coordinate-quotient realization. -/
theorem local_inverse_of_differential_equiv
    {k : ℕ} {N P : Type u} [TopologicalSpace N] [TopologicalSpace P]
    {a : ModelKind} (R : SmoothManifold k a N) (T : SmoothManifold k .euclidean P)
    (g : N → P) (hg : IsSmoothMap R T g) (x : N) (hx : x ∈ manifoldInterior R)
    (E : TangentSpace R x ≃ₗ[ℝ] TangentSpace T (g x))
    (hE : IsDifferential R T g x E.toLinearMap) : HasLocalSmoothInverse R T g x := by
  have hg1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ g (by simp) hg
  obtain ⟨F, G, L, hL⟩ := MapClasses.exists_differential_model R T g hg1 x
  letI := F.group
  letI := F.module
  letI := G.group
  letI := G.module
  obtain ⟨ER, hER⟩ := FiniteRegularity.smooth_compatibility R x F
  obtain ⟨ET, hET⟩ := FiniteRegularity.smooth_compatibility T (g x) G
  have hcomp := FiniteRegularity.smooth_differential_compatibility R T g hg x
    F G ER ET hER hET L E.toLinearMap hL hE
  have hcomp' (v : CoordinateTangent R.smoothStructure.val x) :
      ET (L v) = E (ER v) := hcomp v
  have hbij : Function.Bijective L := by
    constructor
    · intro v w hvw
      apply ER.injective
      apply E.injective
      rw [← hcomp', ← hcomp', hvw]
    · intro w
      refine ⟨ER.symm (E.symm (ET w)), ET.injective ?_⟩
      rw [hcomp', ER.apply_symm_apply, E.apply_symm_apply]
  have htarget : g x ∈ manifoldInterior T := by
    obtain ⟨d, hd, hxd⟩ := T.smoothStructure.property.1.1 (g x)
    exact ⟨d, hd, hxd, by simp [ModelData.modelSet]⟩
  obtain ⟨h, hxh, hsrc, _htgt, heq, hforward, hback⟩ :=
    InteriorInverse.interior_inverse (⊤ : ℕ∞) (by simp) R T g hg x hx htarget F G L hL hbij
  exact ⟨h, hxh, hsrc, heq, hforward, hback⟩

/-- The complete universal property for any constructed intrinsic leaf. -/
theorem universal_integral_leaf
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (A : Set (ModelChart n .euclidean M))
    (hA : IsCountableAdaptedAtlas D A) (p : M)
    (T : @SmoothManifold k .euclidean (leafSet A k p) (leafTopology A k p))
    (hcharts : HasPlaqueCharts A p T) (hIntegral : IsIntegralLeaf D A p T) :
    UniversalIntegralLeaf D A p T := by
  letI := leafTopology A k p
  intro N _ _ a R f hf x₀ hx₀
  have himage := integral_immersion_image_subset_leaf D A hA R f hf p x₀ hx₀
  let g : N → leafSet A k p := fun x => ⟨f x, himage x⟩
  have hg : IsSmoothMap R T g := integral_immersion_lift_smooth D A hA p T hcharts R f hf himage
  obtain ⟨J, hJ, hrJ⟩ := hIntegral.2.2.2
  obtain ⟨K, hK, hrK⟩ := hf.2.2
  have hiso (x : N) : ∃ E : TangentSpace R x ≃ₗ[ℝ] TangentSpace T (g x),
      IsDifferential R T g x E.toLinearMap := by
    obtain ⟨L, hL, _⟩ := differential_exists R T g hg x
    have hcompDiff := differential_comp R T S g Subtype.val hg hIntegral.1 x L (J (g x)) hL (hJ (g x))
    have hcomp : (J (g x)).comp L = K x :=
      (differential_exists R S f hf.1 x).unique hcompDiff (hK x)
    have hJi := differential_injective T S Subtype.val hIntegral.1 hIntegral.2.1 (g x) _ (hJ (g x))
    have hKi := differential_injective R S f hf.1 hf.2.1 x _ (hK x)
    have hbij : Function.Bijective L := by
      constructor
      · intro v w hvw
        apply hKi
        rw [← hcomp]
        exact congrArg (J (g x)) hvw
      · intro y
        have hy : J (g x) y ∈ LinearMap.range (K x) := by
          rw [hrK x, ← hrJ (g x)]
          exact LinearMap.mem_range_self _ y
        obtain ⟨v, hv⟩ := hy
        refine ⟨v, hJi ?_⟩
        change ((J (g x)).comp L) v = J (g x) y
        rwa [hcomp]
    exact ⟨LinearEquiv.ofBijective L hbij, hL⟩
  have hinverse (x : N) (hx : x ∈ manifoldInterior R) : HasLocalSmoothInverse R T g x := by
    obtain ⟨E, hE⟩ := hiso x
    exact local_inverse_of_differential_equiv R T g hg x hx E hE
  refine ⟨g, ⟨hg, fun _ => rfl, hiso, hinverse, ?_⟩, ?_⟩
  · intro ha
    subst a
    intro x
    apply hinverse
    obtain ⟨e, he, hxe⟩ := R.smoothStructure.property.1.1 x
    refine ⟨e, he, hxe, ?_⟩
    simp [ModelData.modelSet]
  · intro j hj
    funext x
    exact Subtype.ext (hj.2.1 x)

/-- Conditional assembly only. The original target is intentionally left
undefined until the owner closes all six upstream obligations. -/
theorem global_leaves_conditional
    (_hBasis : Specs.SmoothManifolds.Ch08.LeafStructures.basis_from_open_overlapsType.{u})
    (_hConnected : Specs.SmoothManifolds.Ch08.LeafStructures.connectedType.{u})
    (hCountable : Specs.SmoothManifolds.Ch08.LeafStructures.countable_adapted_atlasType.{u})
    (_hHausdorff : Specs.SmoothManifolds.Ch08.LeafStructures.hausdorffType.{u})
    (hStructures : Specs.SmoothManifolds.Ch08.LeafStructures.leaf_structuresType.{u})
    (hPartition : Specs.SmoothManifolds.Ch08.LeafStructures.partitionType.{u}) :
    Specs.SmoothManifolds.Ch08.GlobalLeaves.global_leavesType.{u} := by
  intro n k M _ S C D hD
  obtain ⟨A, hA⟩ := hCountable D hD
  obtain ⟨hcover, hdisj⟩ := hPartition A k
  refine ⟨A, hA, hcover, hdisj, ?_⟩
  intro p
  obtain ⟨T, hconn, hbasis, hcharts, hint⟩ := hStructures D A hA p
  exact ⟨T, hconn, hbasis, hcharts, hint, universal_integral_leaf D A hA p T hcharts hint⟩

end SmoothManifolds.GlobalLeaves

universe v8_closure_2622ea0a5ea3aaf1_u0
theorem _root_.«SmoothManifolds».«GlobalLeaves».«global_leaves» : _root_.«Specs».«SmoothManifolds».«Ch08».«GlobalLeaves».«global_leavesType».{v8_closure_2622ea0a5ea3aaf1_u0} :=
  @_root_.«SmoothManifolds».«GlobalLeaves».«global_leaves_conditional».{v8_closure_2622ea0a5ea3aaf1_u0} (@_root_.«SmoothManifolds».«LeafStructures».«basis_from_open_overlaps».{v8_closure_2622ea0a5ea3aaf1_u0}) (@_root_.«SmoothManifolds».«LeafStructures».«connected_leaves».{v8_closure_2622ea0a5ea3aaf1_u0}) (@_root_.«SmoothManifolds».«LeafStructures».«countable_adapted_atlas».{v8_closure_2622ea0a5ea3aaf1_u0}) (@_root_.«SmoothManifolds».«LeafStructures».«hausdorff_leaves».{v8_closure_2622ea0a5ea3aaf1_u0}) (@_root_.«SmoothManifolds».«LeafStructures».«leaf_structures».{v8_closure_2622ea0a5ea3aaf1_u0}) (@_root_.«SmoothManifolds».«LeafStructures».«partition».{v8_closure_2622ea0a5ea3aaf1_u0})
