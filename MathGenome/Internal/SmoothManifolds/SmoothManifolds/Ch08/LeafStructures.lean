import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.LeafStructures
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.Frobenius
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.PlaqueOverlap
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.PlaqueChainCountability
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

/-! Intrinsic leaf manifolds from finite plaque chains (paper.tex 1657--1662).
The final plaque topology has a compatible smooth atlas; countable plaque-chain
covers prove second countability. The inclusion has injective differential with
image equal to the distribution, without imposing the ambient subspace topology.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SmoothManifolds.LeafStructures
open ModelData AtlasData FrobeniusData LeafData Set
  DistributionData BundleOperationsData CovectorData MapData Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [tM : TopologicalSpace M]
  (A : Set (ModelChart n .euclidean M)) (k : ℕ)

/-- The generated relation is an equivalence even for an empty chart family. -/
theorem leafRelation_equivalence : Equivalence (LeafRelation A k) :=
  Relation.EqvGen.is_equivalence _

theorem mem_leafSet_self (p : M) : p ∈ leafSet A k p :=
  Relation.EqvGen.refl p

theorem leafSet_eq_of_related {p q : M} (h : LeafRelation A k p q) :
    leafSet A k p = leafSet A k q := by
  ext r
  constructor
  · intro hr
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hr
  · intro hr
    exact Relation.EqvGen.trans _ _ _ h hr

theorem leafSet_eq_or_disjoint (p q : M) :
    leafSet A k p = leafSet A k q ∨ Disjoint (leafSet A k p) (leafSet A k q) := by
  classical
  by_cases h : LeafRelation A k p q
  · exact Or.inl (leafSet_eq_of_related A k h)
  · right
    rw [Set.disjoint_left]
    intro r hpr hqr
    exact h (Relation.EqvGen.trans _ _ _ hpr (Relation.EqvGen.symm _ _ hqr))

/-- Any plaque meeting a class is wholly contained in it. -/
theorem plaque_subset_leafSet {p q : M} (h : q ∈ leafSet A k p)
    (e : ModelChart n .euclidean M) (he : e ∈ A) (z : Euclidean (n-k))
    (hq : q ∈ coordinateSlice e k z) : coordinateSlice e k z ⊆ leafSet A k p := by
  intro r hr
  exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ ⟨e, he, z, hq, hr⟩)

/-- The entire ambient space is partitioned by the classes. -/
theorem partition : Specs.SmoothManifolds.Ch08.LeafStructures.partitionType.{u} := by
  intro n M _ A k
  exact ⟨mem_leafSet_self A k, leafSet_eq_or_disjoint A k⟩

/-- Every ambient open set is plaque-open. No equality of the two topologies
is claimed. -/
theorem ambient_open_is_plaque_open {U : Set M} (hU : IsOpen U) :
    @IsOpen M (plaqueTopology A k) U := by
  intro e he z
  exact hU.preimage continuous_subtype_val

/-- The identity to the ambient manifold is continuous. -/
theorem continuous_plaque_to_ambient :
    @Continuous M M (plaqueTopology A k) tM id := by
  rw [continuous_def]
  intro U hU
  exact ambient_open_is_plaque_open A k hU

/-- An individual plaque retains its original subspace topology in this map. -/
theorem continuous_plaque_inclusion (e : ModelChart n .euclidean M) (he : e ∈ A)
    (z : Euclidean (n-k)) :
    @Continuous (coordinateSlice e k z) M inferInstance (plaqueTopology A k)
      Subtype.val := by
  rw [continuous_def]
  exact fun U hU => hU e he z

/-- Each class is open in the topology of all plaques. -/
theorem leafSet_isOpen (p : M) : @IsOpen M (plaqueTopology A k) (leafSet A k p) := by
  classical
  intro e he z
  by_cases h : ∃ q ∈ coordinateSlice e k z, q ∈ leafSet A k p
  · obtain ⟨q, hq, hpq⟩ := h
    have hsub := plaque_subset_leafSet A k hpq e he z hq
    have hEq : (Subtype.val ⁻¹' leafSet A k p : Set (coordinateSlice e k z)) = univ := by
      ext r
      simp only [mem_preimage, mem_univ, iff_true]
      exact hsub r.property
    rw [hEq]
    exact isOpen_univ
  · have hEq : (Subtype.val ⁻¹' leafSet A k p : Set (coordinateSlice e k z)) = ∅ := by
      ext r
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hr
      exact h ⟨r.val, r.property, hr⟩
    rw [hEq]
    exact isOpen_empty

/-- Complements of classes are also open. -/
theorem leafSet_isClosed (p : M) : @IsClosed M (plaqueTopology A k) (leafSet A k p) := by
  classical
  apply (@isOpen_compl_iff M (leafSet A k p) (plaqueTopology A k)).mp
  have hEq : (leafSet A k p)ᶜ = ⋃ q : {q // q ∉ leafSet A k p}, leafSet A k q.val := by
    ext r
    constructor
    · intro hr
      exact mem_iUnion.mpr ⟨⟨r, hr⟩, mem_leafSet_self A k r⟩
    · intro hr
      obtain ⟨q, hqr⟩ := mem_iUnion.mp hr
      intro hpr
      exact q.property (Relation.EqvGen.trans _ _ _ hpr (Relation.EqvGen.symm _ _ hqr))
  rw [hEq]
  exact @isOpen_iUnion M {q // q ∉ leafSet A k p} (plaqueTopology A k)
    (fun q => leafSet A k q.val) (fun q => leafSet_isOpen A k q.val)

/-- Inclusion of a class in the original manifold is continuous. -/
theorem continuous_leaf_inclusion (p : M) :
    @Continuous (leafSet A k p) M (leafTopology A k p) tM Subtype.val := by
  exact @Continuous.comp _ _ _ (leafTopology A k p) (plaqueTopology A k) tM
    Subtype.val id (continuous_plaque_to_ambient A k)
    (@continuous_subtype_val M (plaqueTopology A k) (leafSet A k p))

/-- Hausdorffness is inherited through the continuous injective inclusion;
it does not require the leaf to be embedded. -/
theorem leaf_t2Space [T2Space M] (p : M) :
    @T2Space (leafSet A k p) (leafTopology A k p) := by
  exact @T2Space.of_injective_continuous _ M (leafTopology A k p) tM
    inferInstance Subtype.val Subtype.val_injective (continuous_leaf_inclusion A k p)

/-- A finite plaque chain gives a preconnected set in the plaque topology.
This is purely topological; the geometric application must still establish
connectedness of the selected plaques. -/
theorem related_has_preconnected_subset
    (hP : ∀ e ∈ A, ∀ z : Euclidean (n-k), IsPreconnected (coordinateSlice e k z))
    {p q : M} (hpq : LeafRelation A k p q) :
    ∃ K : Set M, K ⊆ leafSet A k p ∧ p ∈ K ∧ q ∈ K ∧
      @IsPreconnected M (plaqueTopology A k) K := by
  induction hpq with
  | rel p q h =>
    obtain ⟨e, he, z, hp, hq⟩ := h
    refine ⟨coordinateSlice e k z,
      plaque_subset_leafSet A k (mem_leafSet_self A k p) e he z hp, hp, hq, ?_⟩
    letI := Subtype.preconnectedSpace (hP e he z)
    have hc := @IsPreconnected.image (coordinateSlice e k z) M inferInstance
      (plaqueTopology A k) univ isPreconnected_univ Subtype.val
      (@Continuous.continuousOn _ M inferInstance (plaqueTopology A k)
        Subtype.val univ (continuous_plaque_inclusion A k e he z))
    simpa only [Set.image_univ, Subtype.range_val] using hc
  | refl p =>
    exact ⟨{p}, singleton_subset_iff.mpr (mem_leafSet_self A k p),
      mem_singleton p, mem_singleton p, @isPreconnected_singleton M (plaqueTopology A k) p⟩
  | symm p q hpq ih =>
    obtain ⟨K, hK, hpK, hqK, hc⟩ := ih
    refine ⟨K, ?_, hqK, hpK, hc⟩
    rw [← leafSet_eq_of_related A k hpq]
    exact hK
  | trans p q r hpq hqr ih₁ ih₂ =>
    obtain ⟨K, hK, hpK, hqK, hcK⟩ := ih₁
    obtain ⟨L, hL, hqL, hrL, hcL⟩ := ih₂
    refine ⟨K ∪ L, ?_, Or.inl hpK, Or.inr hrL, @IsPreconnected.union M (plaqueTopology A k) q K L hqK hqL hcK hcL⟩
    apply union_subset hK
    rw [leafSet_eq_of_related A k hpq]
    exact hL

/-- Connectedness of a class follows from connectedness of its plaques;
no global embedding or closedness in the ambient manifold is used. -/
theorem leaf_connectedSpace
    (hP : ∀ e ∈ A, ∀ z : Euclidean (n-k), IsPreconnected (coordinateSlice e k z))
    (p : M) : @ConnectedSpace (leafSet A k p) (leafTopology A k p) := by
  have hc : @IsConnected M (plaqueTopology A k) (leafSet A k p) := by
    refine ⟨⟨p, mem_leafSet_self A k p⟩, ?_⟩
    exact @isPreconnected_of_forall M (plaqueTopology A k) (leafSet A k p) p
      (fun q hq => related_has_preconnected_subset A k hP hq)
  exact (@isConnected_iff_connectedSpace M (plaqueTopology A k) (leafSet A k p)).mp hc

/-- In the finite product norm, a ball splits into the two coordinate balls.
Positive radii handle zero-dimensional factors without exceptions. -/
theorem mem_ball_iff_split {k : ℕ} (hk : k ≤ n) (x a : Euclidean n)
    {r : ℝ} (hr : 0 < r) :
    x ∈ Metric.ball a r ↔
      longitudinalCoordinates hk x ∈ Metric.ball (longitudinalCoordinates hk a) r ∧
      transverseCoordinates k x ∈ Metric.ball (transverseCoordinates k a) r := by
  simp only [Metric.mem_ball, dist_pi_lt_iff hr]
  constructor
  · intro h
    exact ⟨fun i => h ⟨i.val, lt_of_lt_of_le i.isLt hk⟩,
      fun j => h ⟨k+j.val, by omega⟩⟩
  · rintro ⟨h₁, h₂⟩ j
    by_cases hj : j.val < k
    · exact h₁ ⟨j.val, hj⟩
    · have h := h₂ ⟨j.val-k, by omega⟩
      simpa only [transverseCoordinates, Nat.add_sub_cancel' (by omega : k ≤ j.val)] using h

/-- Restrict an adapted chart to a coordinate ball around the chosen point. -/
theorem exists_productBall_adapted_chart
    {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (p : M)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) (hadapt : IsAdaptedChart D e he) :
    ∃ (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val),
      p ∈ d.source ∧ IsAdaptedChart D d hd ∧ IsProductBallChart k d := by
  have hk : k ≤ n := (D.smooth p).1
  have hopen : IsOpen (Subtype.val '' e.target : Set (Euclidean n)) := by
    exact (isOpen_univ.isOpenEmbedding_subtypeVal).isOpenMap _ e.open_target
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (e p).val
    ⟨e p, e.map_source hp, rfl⟩
  let B : Set (ModelSpace n .euclidean) := Subtype.val ⁻¹' Metric.ball (e p).val r
  have hB : IsOpen B := Metric.isOpen_ball.preimage continuous_subtype_val
  have hBt : B ⊆ e.target := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hball hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  let U : Set M := e.source ∩ e ⁻¹' B
  have hU : IsOpen U := e.isOpen_inter_preimage hB
  let d : ModelChart n .euclidean M := e.restr U
  have hd := Frobenius.chart_restr_mem S e he U
  have hdtarget : d.target = B := by
    change e.target ∩ e.symm ⁻¹' interior U = B
    rw [hU.interior_eq]
    ext x
    constructor
    · rintro ⟨hx, hxs, hxB⟩
      change e (e.symm x) ∈ B at hxB
      rwa [e.right_inv hx] at hxB
    · intro hx
      have hxt := hBt hx
      refine ⟨hxt, e.map_target hxt, ?_⟩
      change e (e.symm x) ∈ B
      rwa [e.right_inv hxt]
  refine ⟨d, hd, ⟨hp, ?_⟩, ?_, hk, longitudinalCoordinates hk (e p).val,
    transverseCoordinates k (e p).val, r, r, hr, hr, ?_⟩
  · rw [hU.interior_eq]
    exact ⟨hp, Metric.mem_ball_self hr⟩
  · intro q hq v
    rw [Frobenius.fiberCoordinates_restr C.tangent e he U q hq]
    exact hadapt q hq.1 v
  · rw [hdtarget]
    ext x
    exact mem_ball_iff_split hk x.val (e p).val hr

/-- Countable rectangular adapted atlases are constructed, rather than
postulated. Empty spaces require no arbitrary choice of a base point. -/
theorem countable_adapted_atlas :
    Specs.SmoothManifolds.Ch08.LeafStructures.countable_adapted_atlasType.{u} := by
  classical
  intro n k M _ S C D hD
  have hcoord := Frobenius.adapted_coordinates_of_involutive D hD
  have hlocal (p : M) :
      ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val),
        p ∈ e.source ∧ IsAdaptedChart D e he ∧ IsProductBallChart k e := by
    obtain ⟨e, he, hp, ha⟩ := hcoord p
    exact exists_productBall_adapted_chart D p e he hp ha
  choose e he hp ha hb using hlocal
  letI := S.topologicalManifold.secondCountable
  obtain ⟨J, hJ, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun p => (e p).source) (fun p => (e p).open_source)
  refine ⟨e '' J, hJ.image e, ?_, ?_⟩
  · intro p
    have hpall : p ∈ ⋃ q, (e q).source := mem_iUnion.mpr ⟨p, hp p⟩
    rw [← hcover] at hpall
    obtain ⟨q, hqJ, hpq⟩ := mem_iUnion₂.mp hpall
    exact ⟨e q, mem_image_of_mem e hqJ, hpq⟩
  · rintro d ⟨p, hpJ, rfl⟩
    exact ⟨he p, ha p, hb p⟩

/-- The product-ball condition makes every nonempty plaque connected.
No connectedness of intersections with other chart domains is asserted. -/
theorem productBall_plaque_preconnected
    (e : ModelChart n .euclidean M) (hprod : IsProductBallChart k e)
    (z : Euclidean (n-k)) : IsPreconnected (coordinateSlice e k z) := by
  classical
  obtain ⟨hk, a, b, r, s, hr, hs, htarget⟩ := hprod
  by_cases hz : z ∈ Metric.ball b s
  · let f : Euclidean k → M := fun x =>
      e.symm (Frobenius.modelPoint (Frobenius.sliceInsertion hk z x))
    have hlong (x : Euclidean k) :
        longitudinalCoordinates hk (Frobenius.sliceInsertion hk z x) = x := by
      exact Frobenius.longitudinalProjection_sliceInsertion hk z x
    have hmem (x : Euclidean k) (hx : x ∈ Metric.ball a r) :
        Frobenius.modelPoint (Frobenius.sliceInsertion hk z x) ∈ e.target := by
      rw [htarget]
      change longitudinalCoordinates hk (Frobenius.sliceInsertion hk z x) ∈ Metric.ball a r ∧
        transverseCoordinates k (Frobenius.sliceInsertion hk z x) ∈ Metric.ball b s
      exact ⟨by rw [hlong]; exact hx,
        by rw [Frobenius.transverseCoordinates_sliceInsertion]; exact hz⟩
    have himage : f '' Metric.ball a r = coordinateSlice e k z := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨e.map_target (hmem x hx), ?_⟩
        change transverseCoordinates k (e (e.symm _)).val = z
        rw [e.right_inv (hmem x hx)]
        exact Frobenius.transverseCoordinates_sliceInsertion hk z x
      · intro hq
        have ht : e q ∈ e.target := e.map_source hq.1
        rw [htarget] at ht
        refine ⟨longitudinalCoordinates hk (e q).val, ht.1, ?_⟩
        change e.symm (Frobenius.modelPoint (Frobenius.sliceInsertion hk z
          (longitudinalCoordinates hk (e q).val))) = q
        change e.symm (Frobenius.modelPoint (Frobenius.sliceInsertion hk z
          (Frobenius.longitudinalProjection hk (e q).val))) = q
        rw [Frobenius.sliceInsertion_projection hk z _ hq.2]
        exact e.left_inv hq.1
    rw [← himage]
    apply (convex_ball a r).isPreconnected.image f
    apply e.symm.continuousOn.comp
      ((Frobenius.continuous_modelPoint n).comp
        (Frobenius.contDiff_sliceInsertion hk z).continuous).continuousOn
    exact hmem
  · have hempty : coordinateSlice e k z = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have ht := e.map_source hq.1
      rw [htarget] at ht
      exact hz (hq.2 ▸ ht.2)
    rw [hempty]
    exact isPreconnected_empty

/-- Connectedness with exactly the hypotheses used in the leaf construction. -/
theorem connected_of_adapted_atlas
    {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (A : Set (ModelChart n .euclidean M))
    (hA : IsCountableAdaptedAtlas D A) (p : M) :
    @ConnectedSpace (leafSet A k p) (leafTopology A k p) := by
  apply leaf_connectedSpace A k
  intro e he z
  obtain ⟨_, _, hprod⟩ := hA.2.2 e he
  exact productBall_plaque_preconnected k e hprod z

/-- Relative openness of overlaps makes every plaque inclusion an open map
for the final topology. The overlap hypothesis must be proved geometrically. -/
theorem plaque_inclusion_isOpenMap
    (hO : ∀ e ∈ A, ∀ z : Euclidean (n-k), ∀ d ∈ A, ∀ w : Euclidean (n-k),
      IsOpen (Subtype.val ⁻¹' coordinateSlice d k w : Set (coordinateSlice e k z)))
    (e : ModelChart n .euclidean M) (he : e ∈ A) (z : Euclidean (n-k)) :
    @IsOpenMap (coordinateSlice e k z) M inferInstance (plaqueTopology A k)
      Subtype.val := by
  intro W hW d hd w
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hW
  have hEq : (Subtype.val ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' V : Set (coordinateSlice e k z))) :
      Set (coordinateSlice d k w)) =
      (Subtype.val ⁻¹' V) ∩ (Subtype.val ⁻¹' coordinateSlice e k z) := by
    ext q
    simp only [mem_preimage, mem_image, mem_inter_iff]
    constructor
    · rintro ⟨r, hr, hrq⟩
      exact ⟨hrq ▸ hr, hrq ▸ r.property⟩
    · rintro ⟨hqV, hqP⟩
      exact ⟨⟨q.val, hqP⟩, hqV, rfl⟩
  rw [hEq]
  exact (hV.preimage continuous_subtype_val).inter (hO d hd w e he z)

/-- Once geometric overlaps are open, the plaque-open sets form exactly a
basis of the specified leaf topology. -/
theorem plaqueBasis_isTopologicalBasis
    (hcover : ∀ q : M, ∃ e ∈ A, q ∈ e.source)
    (hO : ∀ e ∈ A, ∀ z : Euclidean (n-k), ∀ d ∈ A, ∀ w : Euclidean (n-k),
      IsOpen (Subtype.val ⁻¹' coordinateSlice d k w : Set (coordinateSlice e k z)))
    (p : M) : @TopologicalSpace.IsTopologicalBasis (leafSet A k p) (leafTopology A k p)
      (plaqueBasis A k p) := by
  apply @TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds _ (leafTopology A k p)
  · rintro V ⟨e, he, z, hP, W, hW, rfl⟩
    exact @IsOpen.preimage _ _ (leafTopology A k p) (plaqueTopology A k)
      Subtype.val (@continuous_subtype_val M (plaqueTopology A k) (leafSet A k p))
      (Subtype.val '' W) (plaque_inclusion_isOpenMap A k hO e he z W hW)
  · intro q U hq hU
    obtain ⟨V, hV, hVU⟩ := @isOpen_induced_iff _ M (plaqueTopology A k) U
      (Subtype.val : leafSet A k p → M) |>.mp hU
    obtain ⟨e, he, hqe⟩ := hcover q.val
    let z := transverseCoordinates k (e q.val).val
    have hqP : q.val ∈ coordinateSlice e k z := ⟨hqe, rfl⟩
    have hP := plaque_subset_leafSet A k q.property e he z hqP
    let W : Set (coordinateSlice e k z) := Subtype.val ⁻¹' V
    have hW : IsOpen W := hV e he z
    let B : Set (leafSet A k p) := {r | r.val ∈ Subtype.val '' W}
    refine ⟨B, ⟨e, he, z, hP, W, hW, rfl⟩, ?_, ?_⟩
    · have hqV : q.val ∈ V := by
        change q ∈ Subtype.val ⁻¹' V
        rwa [hVU]
      exact ⟨⟨q.val, hqP⟩, hqV, rfl⟩
    · rintro r ⟨s, hsW, hsr⟩
      rw [← hVU]
      change r.val ∈ V
      exact hsr ▸ hsW
/-- Full independent Hausdorff statement. -/
theorem hausdorff_leaves :
    Specs.SmoothManifolds.Ch08.LeafStructures.hausdorffType.{u} := by
  intro n M _ A k _ p
  exact leaf_t2Space A k p

/-- Full independent connectedness statement. -/
theorem connected_leaves :
    Specs.SmoothManifolds.Ch08.LeafStructures.connectedType.{u} := by
  intro n k M _ S C D A hA p
  exact connected_of_adapted_atlas D A hA p

/-- The proved gluing helper, with its overlap premise explicitly visible. -/
theorem basis_from_open_overlaps :
    Specs.SmoothManifolds.Ch08.LeafStructures.basis_from_open_overlapsType.{u} := by
  intro n M _ A k hcover hO p
  exact plaqueBasis_isTopologicalBasis A k hcover hO p

/-- Adapted plaques have relatively open overlaps in their original topology. -/
theorem adapted_open_overlaps
    {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hA : IsCountableAdaptedAtlas D A)
    (e : ModelChart n .euclidean M) (he : e ∈ A) (z : Euclidean (n-k))
    (d : ModelChart n .euclidean M) (hd : d ∈ A) (w : Euclidean (n-k)) :
    IsOpen (Subtype.val ⁻¹' coordinateSlice d k w : Set (coordinateSlice e k z)) := by
  obtain ⟨heS, heD, _⟩ := hA.2.2 e he
  obtain ⟨hdS, hdD, _⟩ := hA.2.2 d hd
  exact PlaqueOverlap.overlap_isOpen D e d heS hdS heD hdD z w


/-- The map from an original plaque into its leaf. -/
def plaqueToLeaf (p : M) (e : ModelChart n .euclidean M) (z : Euclidean (n-k))
    (hP : coordinateSlice e k z ⊆ leafSet A k p) :
    coordinateSlice e k z → leafSet A k p := fun q => ⟨q.val, hP q.property⟩

theorem plaqueToLeaf_isOpenEmbedding
    (hO : ∀ e ∈ A, ∀ z : Euclidean (n-k), ∀ d ∈ A, ∀ w : Euclidean (n-k),
      IsOpen (Subtype.val ⁻¹' coordinateSlice d k w : Set (coordinateSlice e k z)))
    (p : M) (e : ModelChart n .euclidean M) (he : e ∈ A) (z : Euclidean (n-k))
    (hP : coordinateSlice e k z ⊆ leafSet A k p) :
    @Topology.IsOpenEmbedding (coordinateSlice e k z) (leafSet A k p)
      inferInstance (leafTopology A k p) (plaqueToLeaf A k p e z hP) := by
  letI := leafTopology A k p
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact @Continuous.subtype_mk M (coordinateSlice e k z) (plaqueTopology A k) inferInstance
      (leafSet A k p) Subtype.val (continuous_plaque_inclusion A k e he z) (fun q => hP q.property)
  · intro q r h
    exact Subtype.ext (congrArg (fun x : leafSet A k p => x.val) h)
  · exact @IsOpenMap.subtype_mk M (coordinateSlice e k z) (plaqueTopology A k) inferInstance
      (leafSet A k p) Subtype.val (plaque_inclusion_isOpenMap A k hO e he z) (fun q => hP q.property)

local instance (d : ℕ) : Nonempty (ModelSpace d .euclidean) := ⟨Frobenius.modelPoint 0⟩

/-- A nonempty plaque chart transported to the intrinsic leaf topology. -/
def leafChart
    (hO : ∀ e ∈ A, ∀ z : Euclidean (n-k), ∀ d ∈ A, ∀ w : Euclidean (n-k),
      IsOpen (Subtype.val ⁻¹' coordinateSlice d k w : Set (coordinateSlice e k z)))
    (hk : k ≤ n) (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ A) (z : Euclidean (n-k)) (hP : coordinateSlice e k z ⊆ leafSet A k p)
    [Nonempty (coordinateSlice e k z)] :
    @ModelChart k .euclidean (leafSet A k p) (leafTopology A k p) := by
  letI := leafTopology A k p
  exact (Frobenius.sliceChart e hk z).lift_openEmbedding
    (plaqueToLeaf_isOpenEmbedding A k hO p e he z hP)

theorem leafChart_source
    (hO : ∀ e ∈ A, ∀ z : Euclidean (n-k), ∀ d ∈ A, ∀ w : Euclidean (n-k),
      IsOpen (Subtype.val ⁻¹' coordinateSlice d k w : Set (coordinateSlice e k z)))
    (hk : k ≤ n) (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ A) (z : Euclidean (n-k)) (hP : coordinateSlice e k z ⊆ leafSet A k p)
    [Nonempty (coordinateSlice e k z)] :
    (leafChart A k hO hk p e he z hP).source = {q | q.val ∈ coordinateSlice e k z} := by
  ext q
  change (∃ r, r ∈ (Set.univ : Set (coordinateSlice e k z)) ∧ plaqueToLeaf A k p e z hP r = q) ↔ _
  constructor
  · rintro ⟨r, _, rfl⟩
    exact r.property
  · intro hq
    exact ⟨⟨q.val, hq⟩, mem_univ _, Subtype.ext rfl⟩

theorem leafChart_apply
    (hO : ∀ e ∈ A, ∀ z : Euclidean (n-k), ∀ d ∈ A, ∀ w : Euclidean (n-k),
      IsOpen (Subtype.val ⁻¹' coordinateSlice d k w : Set (coordinateSlice e k z)))
    (hk : k ≤ n) (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ A) (z : Euclidean (n-k)) (hP : coordinateSlice e k z ⊆ leafSet A k p)
    [Nonempty (coordinateSlice e k z)] (q : leafSet A k p)
    (hq : q.val ∈ coordinateSlice e k z) :
    (leafChart A k hO hk p e he z hP q).val = Frobenius.longitudinalProjection hk (e q.val).val := by
  have h : plaqueToLeaf A k p e z hP ⟨q.val, hq⟩ = q := Subtype.ext rfl
  rw [← h]
  letI := leafTopology A k p
  exact congrArg Subtype.val ((Frobenius.sliceChart e hk z).lift_openEmbedding_apply
    (plaqueToLeaf_isOpenEmbedding A k hO p e he z hP) (x := ⟨q.val, hq⟩))

/-- Countably many selected plaques cover exactly each point-chain class. -/
theorem countable_plaque_cover
    {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hA : IsCountableAdaptedAtlas D A) (p : M) :
    ∃ B : Set (A × Euclidean (n-k)), B.Countable ∧
      (∀ b ∈ B, coordinateSlice b.1.val k b.2 ⊆ leafSet A k p) ∧
      leafSet A k p = ⋃ b ∈ B, coordinateSlice b.1.val k b.2 := by
  letI := S.topologicalManifold.secondCountable
  letI : Countable A := hA.1.to_subtype
  let P : A × Euclidean (n-k) → Set M := fun b => coordinateSlice b.1.val k b.2
  have hrel (x y : M) :
      (∃ b, x ∈ P b ∧ y ∈ P b) ↔ SamePlaque A k x y := by
    constructor
    · rintro ⟨⟨e, z⟩, hx, hy⟩
      exact ⟨e.val, e.property, z, hx, hy⟩
    · rintro ⟨e, he, z, hx, hy⟩
      exact ⟨(⟨e, he⟩, z), hx, hy⟩
  have hclass : {q | Relation.EqvGen (fun x y => ∃ b, x ∈ P b ∧ y ∈ P b) p q} =
      leafSet A k p := by
    have hr : (fun x y => ∃ b, x ∈ P b ∧ y ∈ P b) = SamePlaque A k :=
      funext fun x => funext fun y => propext (hrel x y)
    rw [hr]
    rfl
  obtain ⟨B, hB, hsub, hcover⟩ := PlaqueChains.point_class_cover P
    (fun _ => inferInstance)
    (by
      intro e z w hne
      apply Set.disjoint_left.mpr
      intro q hq hq'
      exact hne (hq.2.symm.trans hq'.2))
    (fun b c => adapted_open_overlaps A D hA b.1.val b.1.property b.2
      c.1.val c.1.property c.2)
    (by
      intro q
      obtain ⟨e, he, hqe⟩ := hA.2.1 q
      exact ⟨(⟨e, he⟩, transverseCoordinates k (e q).val), hqe, rfl⟩) p
  rw [hclass] at hsub hcover
  exact ⟨B, hB, hsub, hcover⟩

theorem plaqueToLeaf_range (p : M) (e : ModelChart n .euclidean M) (z : Euclidean (n-k))
    (hP : coordinateSlice e k z ⊆ leafSet A k p) :
    Set.range (plaqueToLeaf A k p e z hP) = {q | q.val ∈ coordinateSlice e k z} := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    exact r.property
  · intro hq
    exact ⟨⟨q.val, hq⟩, Subtype.ext rfl⟩

/-- A countable cover by open, originally second-countable plaques supplies
second countability for the intrinsic topology of an entire leaf. -/
theorem leaf_secondCountableTopology
    {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hA : IsCountableAdaptedAtlas D A) (p : M) :
    @SecondCountableTopology (leafSet A k p) (leafTopology A k p) := by
  classical
  letI := S.topologicalManifold.secondCountable
  letI := leafTopology A k p
  have hO := adapted_open_overlaps A D hA
  obtain ⟨B, hB, hsub, hcover⟩ := countable_plaque_cover A D hA p
  letI : Countable B := hB.to_subtype
  let U : B → Set (leafSet A k p) := fun b => {q | q.val ∈ coordinateSlice b.val.1.val k b.val.2}
  have hemb (b : B) := plaqueToLeaf_isOpenEmbedding A k hO p b.val.1.val
    b.val.1.property b.val.2 (hsub b.val b.property)
  have hrange (b : B) : Set.range (plaqueToLeaf A k p b.val.1.val b.val.2
      (hsub b.val b.property)) = U b := plaqueToLeaf_range A k p _ _ _
  letI : ∀ b, SecondCountableTopology (U b) := fun b => by
    have h := (hemb b).isEmbedding.toHomeomorph.symm.secondCountableTopology
    rwa [hrange b] at h
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
  · intro b
    rw [← hrange b]
    exact (hemb b).isOpen_range
  · ext q
    simp only [mem_iUnion, mem_univ, iff_true]
    have hq := q.property
    have hq := (Set.ext_iff.mp hcover q.val).mp hq
    obtain ⟨b, hb, hqb⟩ := mem_iUnion₂.mp hq
    exact ⟨⟨b, hb⟩, hqb⟩

/-- Nonempty plaques wholly contained in this leaf index its generating atlas. -/
abbrev LeafPlaque (A : Set (ModelChart n .euclidean M)) (k : ℕ) (p : M) :=
  {b : A × Euclidean (n-k) //
    coordinateSlice b.1.val k b.2 ⊆ leafSet A k p ∧ Nonempty (coordinateSlice b.1.val k b.2)}

section ChartAssembly
variable {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hA : IsCountableAdaptedAtlas D A)
    (hk : k ≤ n) (p : M)


def indexedLeafChart (b : LeafPlaque A k p) :
    @ModelChart k .euclidean (leafSet A k p) (leafTopology A k p) := by
  letI := b.property.2
  exact leafChart A k (adapted_open_overlaps A D hA) hk p b.val.1.val b.val.1.property
    b.val.2 b.property.1

theorem indexedLeafChart_source (b : LeafPlaque A k p) :
    (indexedLeafChart A D hA hk p b).source =
      {q | q.val ∈ coordinateSlice b.val.1.val k b.val.2} :=
  @leafChart_source _ _ _ A k (adapted_open_overlaps A D hA) hk p b.val.1.val
    b.val.1.property b.val.2 b.property.1 b.property.2

theorem indexedLeafChart_apply (b : LeafPlaque A k p) (q : leafSet A k p)
    (hq : q.val ∈ coordinateSlice b.val.1.val k b.val.2) :
    (indexedLeafChart A D hA hk p b q).val =
      Frobenius.longitudinalProjection hk (b.val.1.val q.val).val :=
  @leafChart_apply _ _ _ A k (adapted_open_overlaps A D hA) hk p b.val.1.val
    b.val.1.property b.val.2 b.property.1 b.property.2 q hq

theorem indexedLeafCharts_cover (q : leafSet A k p) :
    ∃ b : LeafPlaque A k p, q ∈ (indexedLeafChart A D hA hk p b).source := by
  obtain ⟨e, he, hqe⟩ := hA.2.1 q.val
  let z := transverseCoordinates k (e q.val).val
  have hq : q.val ∈ coordinateSlice e k z := ⟨hqe, rfl⟩
  let b : LeafPlaque A k p := ⟨(⟨e, he⟩, z),
    plaque_subset_leafSet A k q.property e he z hq, ⟨⟨q.val, hq⟩⟩⟩
  refine ⟨b, ?_⟩
  rw [indexedLeafChart_source]
  exact hq

/-- Smooth changes of longitudinal coordinates come from the genuine ambient
chart transition by inserting the fixed transverse coordinate. -/
theorem indexedLeafChart_transition (b c : LeafPlaque A k p)
    (q : leafSet A k p)
    (hqb : q ∈ (indexedLeafChart A D hA hk p b).source)
    (hqc : q ∈ (indexedLeafChart A D hA hk p c).source) :
    @MapData.ChartContDiffAt _ _ _ _ _ _ (leafTopology A k p) (leafTopology A k p)
      (⊤ : ℕ∞) (indexedLeafChart A D hA hk p b) (indexedLeafChart A D hA hk p c) id q := by
  letI := leafTopology A k p
  let e := b.val.1.val
  let d := c.val.1.val
  let z := b.val.2
  have hqe : q.val ∈ coordinateSlice e k z := by rwa [indexedLeafChart_source] at hqb
  have hqd : q.val ∈ coordinateSlice d k c.val.2 := by rwa [indexedLeafChart_source] at hqc
  obtain ⟨he, _, _⟩ := hA.2.2 e b.val.1.property
  obtain ⟨hd, _, _⟩ := hA.2.2 d c.val.1.property
  let V := Frobenius.sliceInsertion hk z ⁻¹' PlaqueOverlap.transitionDomain e d
  let F := fun x => Frobenius.longitudinalProjection hk
    (PlaqueOverlap.transitionMap e d (Frobenius.sliceInsertion hk z x))
  have hcoord (r : leafSet A k p) (hr : r.val ∈ coordinateSlice e k z) :
      Frobenius.sliceInsertion hk z (indexedLeafChart A D hA hk p b r).val = (e r.val).val := by
    rw [indexedLeafChart_apply A D hA hk p b r hr]
    exact Frobenius.sliceInsertion_projection hk z _ hr.2
  refine ⟨V, (PlaqueOverlap.transitionDomain_isOpen e d).preimage
    (Frobenius.contDiff_sliceInsertion hk z).continuous, ?_, F, ?_, ?_⟩
  · change Frobenius.modelPoint (Frobenius.sliceInsertion hk z
      (indexedLeafChart A D hA hk p b q).val) ∈ (e.symm.trans d).source
    rw [hcoord q hqe]
    have hpnt : Frobenius.modelPoint (e q.val).val = e q.val := Subtype.ext rfl
    rw [hpnt]
    refine ⟨e.map_source hqe.1, ?_⟩
    change e.symm (e q.val) ∈ d.source
    rw [e.left_inv hqe.1]
    exact hqd.1
  · exact (Frobenius.longitudinalProjection hk).contDiff.comp_contDiffOn
      ((PlaqueOverlap.transitionMap_contDiffOn e d he hd).comp
        (Frobenius.contDiff_sliceInsertion hk z).contDiffOn (fun _ hx => hx))
  · filter_upwards [(indexedLeafChart A D hA hk p b).open_source.mem_nhds hqb,
      (indexedLeafChart A D hA hk p c).open_source.mem_nhds hqc] with r hrb hrc
    have hre : r.val ∈ coordinateSlice e k z := by rwa [indexedLeafChart_source] at hrb
    have hrd : r.val ∈ coordinateSlice d k c.val.2 := by rwa [indexedLeafChart_source] at hrc
    change Frobenius.longitudinalProjection hk
      (d (e.symm (Frobenius.modelPoint (Frobenius.sliceInsertion hk z
        (indexedLeafChart A D hA hk p b r).val)))).val = _
    rw [hcoord r hre]
    have hpnt : Frobenius.modelPoint (e r.val).val = e r.val := Subtype.ext rfl
    rw [hpnt, e.left_inv hre.1]
    exact (indexedLeafChart_apply A D hA hk p c r hrd).symm

end ChartAssembly

/-- The plaque atlas extends to a maximal smooth atlas on the intrinsic topology. -/
theorem exists_leaf_manifold
    {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hA : IsCountableAdaptedAtlas D A) (p : M) :
    ∃ T : @SmoothManifold k .euclidean (leafSet A k p) (leafTopology A k p),
      HasPlaqueCharts A p T := by
  classical
  letI := leafTopology A k p
  letI := S.topologicalManifold.hausdorff
  letI := leaf_t2Space A k p
  letI := leaf_secondCountableTopology A D hA p
  have hk : k ≤ n := (D.smooth p).1
  let charts := Set.range (indexedLeafChart A D hA hk p)
  have hcharts : IsContDiffAtlas (⊤ : ℕ∞) charts := by
    constructor
    · intro q
      obtain ⟨b, hb⟩ := indexedLeafCharts_cover A D hA hk p q
      exact ⟨_, ⟨b, rfl⟩, hb⟩
    · rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
      apply contDiffCompatible_of_germs
      · exact indexedLeafChart_transition A D hA hk p b c
      · exact indexedLeafChart_transition A D hA hk p c b
  let T : SmoothManifold k .euclidean (leafSet A k p) := {
    topologicalManifold := {
      hausdorff := inferInstance
      secondCountable := inferInstance
      atlas := charts
      covers := hcharts.1 }
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) charts,
      maximalExtension_isMaximal hcharts⟩ }
  have hmem (b : LeafPlaque A k p) : indexedLeafChart A D hA hk p b ∈ T.smoothStructure.val :=
    subset_maximalExtension hcharts ⟨b, rfl⟩
  refine ⟨T, ?_⟩
  intro e he z hP
  cases isEmpty_or_nonempty (coordinateSlice e k z) with
  | inl hempty =>
    obtain ⟨b, hb⟩ := indexedLeafCharts_cover A D hA hk p ⟨p, mem_leafSet_self A k p⟩
    let c := (indexedLeafChart A D hA hk p b).restr ∅
    refine ⟨hk, c, Frobenius.chart_restr_mem T _ (hmem b) ∅, ?_, ?_⟩
    · ext q
      simp only [c, OpenPartialHomeomorph.restr_source, interior_empty, inter_empty, mem_empty_iff_false,
        mem_ofPred_eq]
      exact ⟨False.elim, fun hq => hempty.false ⟨q.val, hq⟩⟩
    · intro q hq
      simp [c] at hq
  | inr hnonempty =>
    let b : LeafPlaque A k p := ⟨(⟨e, he⟩, z), hP, hnonempty⟩
    refine ⟨hk, indexedLeafChart A D hA hk p b, hmem b,
      indexedLeafChart_source A D hA hk p b, ?_⟩
    intro q hq
    exact indexedLeafChart_apply A D hA hk p b q
      (by rwa [indexedLeafChart_source] at hq)

/-- Plaque coordinates give the inclusion's actual intrinsic tangent image. -/
theorem integral_leaf_of_plaqueCharts
    {k : ℕ} {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hA : IsCountableAdaptedAtlas D A) (p : M)
    (T : @SmoothManifold k .euclidean (leafSet A k p) (leafTopology A k p))
    (hT : HasPlaqueCharts A p T) : IsIntegralLeaf D A p T := by
  classical
  letI := leafTopology A k p
  have hlocal (q : leafSet A k p) :
      ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
        (c : ModelChart k .euclidean (leafSet A k p)) (hk : k ≤ n)
        (z : Euclidean (n-k)),
        c ∈ T.smoothStructure.val ∧ q ∈ c.source ∧ q.val ∈ e.source ∧
        IsAdaptedChart D e he ∧
        (fun r => Frobenius.sliceInsertion hk z (c r).val) =ᶠ[𝓝 q]
          (fun r => (e r.val).val) := by
    obtain ⟨e, he, hqe⟩ := hA.2.1 q.val
    let z := transverseCoordinates k (e q.val).val
    have hq : q.val ∈ coordinateSlice e k z := ⟨hqe, rfl⟩
    have hP := plaque_subset_leafSet A k q.property e he z hq
    obtain ⟨hk, c, hc, hsource, hcoord⟩ := hT e he z hP
    obtain ⟨heS, hadapt, _⟩ := hA.2.2 e he
    have hqc : q ∈ c.source := by rw [hsource]; exact hq
    refine ⟨e, heS, c, hk, z, hc, hqc, hqe, hadapt, ?_⟩
    filter_upwards [c.open_source.mem_nhds hqc] with r hr
    rw [hcoord r hr]
    exact Frobenius.sliceInsertion_projection hk z _ ((Set.ext_iff.mp hsource r).mp hr).2
  have hsmooth : MapData.IsSmoothMap T S (Subtype.val : leafSet A k p → M) := by
    intro q
    obtain ⟨e, he, c, hk, z, hc, hqc, hqe, _, hcoord⟩ := hlocal q
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      T.smoothStructure.property.1 S.smoothStructure.property.1 _ q).mpr
    exact ⟨(continuous_leaf_inclusion A k p).continuousAt, c, hc, e, he, hqc, hqe,
      univ, isOpen_univ, mem_univ _, Frobenius.sliceInsertion hk z,
      (Frobenius.contDiff_sliceInsertion hk z).contDiffOn, hcoord⟩
  let L := fun q : leafSet A k p => differential T S Subtype.val hsmooth q
  have hL : ∀ q, DifferentialData.IsDifferential T S Subtype.val q (L q) :=
    fun q => differential_spec T S Subtype.val hsmooth q
  have hlin (q : leafSet A k p) : Function.Injective (L q) ∧ LinearMap.range (L q) = D.fiber q.val := by
    obtain ⟨e, he, c, hk, z, hc, hqc, hqe, hadapt, hcoord⟩ := hlocal q
    obtain ⟨E, hE⟩ := FiniteRegularity.exists_smooth_chart_coordinates T q c hc hqc
    let F := C.tangent.fiberCoordinates.equiv e he q.val hqe
    have hsquare (v : TangentData.TangentSpace T q) :
        F (L q v) = Frobenius.longitudinalInclusion hk (E v) := by
      have h := differential_jacobian T S Subtype.val hsmooth q (L q) (hL q)
        c e hc he hqc hqe E F hE (C.tangent.fiberCoordinates.isCoordinates e he q.val hqe)
        univ (Frobenius.sliceInsertion hk z) isOpen_univ (mem_univ _)
        (Frobenius.contDiff_sliceInsertion hk z).contDiffOn hcoord v
      rwa [(Frobenius.hasFDerivAt_sliceInsertion hk z (c q).val).fderiv] at h
    constructor
    · intro v w hvw
      apply E.injective
      have h := congrArg (fun x => Frobenius.longitudinalProjection hk (F x)) hvw
      simpa only [hsquare, Frobenius.longitudinalProjection_inclusion] using h
    · ext v
      constructor
      · rintro ⟨w, rfl⟩
        apply (hadapt q.val hqe (L q w)).mpr
        rw [hsquare, ← Frobenius.range_longitudinalInclusion hk]
        exact ⟨E w, rfl⟩
      · intro hv
        have hplane := (hadapt q.val hqe v).mp hv
        rw [← Frobenius.range_longitudinalInclusion hk] at hplane
        obtain ⟨x, hx⟩ := hplane
        refine ⟨E.symm x, F.injective ?_⟩
        rw [hsquare, LinearEquiv.apply_symm_apply]
        exact hx
  refine ⟨hsmooth, ?_, Subtype.val_injective, L, hL, fun q => (hlin q).2⟩
  intro q
  exact (MapClasses.smooth_tangent_invariants T S Subtype.val hsmooth q (L q) (hL q)).2.1.mpr
    (hlin q).1

/-- The complete intrinsic leaf-manifold construction. -/
theorem leaf_structures : Specs.SmoothManifolds.Ch08.LeafStructures.leaf_structuresType.{u} := by
  intro n k M _ S C D A hA p
  obtain ⟨T, hT⟩ := exists_leaf_manifold A D hA p
  exact ⟨T, connected_of_adapted_atlas D A hA p,
    plaqueBasis_isTopologicalBasis A k hA.2.1 (adapted_open_overlaps A D hA) p,
    hT, integral_leaf_of_plaqueCharts A D hA p T hT⟩

end SmoothManifolds.LeafStructures
