import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Data.List.OfFn
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.AttachedCellPresentations
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.BasicFundamentalGroups
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.GraphFundamentalGroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Disk attachment, finite CW presentations, and the surface polygon example
of paper.tex, Theorem 2.5 and Example 2.6. The final declarations specialize
the geometric constructions to the proved graph fundamental-group theorem. -/
noncomputable section
open Set Topology CategoryTheory
open scoped ContinuousMap
open P202Specs.Topology P202.Cellular
universe u v w z
set_option backward.isDefEq.respectTransparency false

namespace P202.Topology

private theorem disk_pathConnected (n : ℕ) : PathConnectedSpace (Disk n) :=
  isPathConnected_iff_pathConnectedSpace.mp (Metric.isPathConnected_closedBall (by norm_num))

private theorem cell_pathComponent_preimage {X : Type u} [TopologicalSpace X]
    [CWStructure X] (x : X) (n : ℕ) (c : Cell X n) :
    characteristic X n c ⁻¹' pathComponent x = ∅ ∨
      characteristic X n c ⁻¹' pathComponent x = univ := by
  letI := disk_pathConnected n
  by_cases h : (characteristic X n c ⁻¹' pathComponent x).Nonempty
  · right
    rcases h with ⟨p, hp⟩
    apply eq_univ_of_forall
    intro q
    exact hp.trans ((PathConnectedSpace.joined p q).map (characteristic X n c).continuous)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp h)

theorem cw_pathConnectedSpace {X : Type u} [TopologicalSpace X]
    [CWStructure X] [ConnectedSpace X] : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_eq.mpr
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  refine ⟨x, IsClopen.eq_univ ?_ (pathComponent.nonempty x)⟩
  have hcl (B : Set X) (hB : ∀ n (c : Cell X n),
      characteristic X n c ⁻¹' B = ∅ ∨ characteristic X n c ⁻¹' B = univ) :
      IsClosed B := by
    apply (CWStructure.weak_topology B).mpr
    intro n c
    rcases hB n c with h | h <;> rw [h]
    · exact isClosed_empty
    · exact isClosed_univ
  constructor
  · exact hcl _ (cell_pathComponent_preimage x)
  · apply isClosed_compl_iff.mp
    apply hcl
    intro n c
    rcases cell_pathComponent_preimage x n c with h | h
    · right
      rw [preimage_compl, h, compl_empty]
    · left
      rw [preimage_compl, h, compl_univ]

end P202.Topology

namespace P202.Topology

variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- The restricted characteristic map on an actual skeletal subspace. -/
def skeletalCharacteristic (K n : ℕ) (c : {c : Cell X n // n < K}) :
    C(Disk n, skeletonLT X K) :=
  ⟨fun p => ⟨characteristic X n c.val p,
      skeletonLT_mono (Nat.succ_le_of_lt c.property)
        (diskToSkeleton X CWStructure.boundary_lands n c.val p).property⟩,
    (characteristic X n c.val).continuous.subtype_mk _⟩

@[instance_reducible] def skeletalCellStructure (K : ℕ) :
    CellStructure (skeletonLT X K) where
  Cell n := {c : Cell X n // n < K}
  characteristic n := skeletalCharacteristic K n

theorem skeletal_openCell (K n : ℕ) (c : {c : Cell X n // n < K}) :
    letI := skeletalCellStructure (X := X) K
    openCell (skeletonLT X K) n c =
      (Subtype.val : skeletonLT X K → X) ⁻¹' openCell X n c.val := by
  letI := skeletalCellStructure (X := X) K
  ext p
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, congrArg Subtype.val hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩

theorem skeletal_skeletonLT (K n : ℕ) :
    letI := skeletalCellStructure (X := X) K
    skeletonLT (skeletonLT X K) n =
      (Subtype.val : skeletonLT X K → X) ⁻¹' skeletonLT X (min n K) := by
  letI := skeletalCellStructure (X := X) K
  ext p
  constructor
  · intro hp
    obtain ⟨m, hp⟩ := mem_iUnion.mp hp
    obtain ⟨hmn, hp⟩ := mem_iUnion.mp hp
    obtain ⟨c, hc⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨lt_min hmn c.property,
      mem_iUnion.mpr ⟨c.val, by rwa [skeletal_openCell] at hc⟩⟩⟩
  · intro hp
    obtain ⟨m, hp⟩ := mem_iUnion.mp hp
    obtain ⟨hm, hp⟩ := mem_iUnion.mp hp
    obtain ⟨c, hc⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨(lt_min_iff.mp hm).1, mem_iUnion.mpr
      ⟨⟨c, (lt_min_iff.mp hm).2⟩,
        by rwa [skeletal_openCell]⟩⟩⟩

theorem skeletal_interior_embedding (K n : ℕ)
    (c : {c : Cell X n // n < K}) :
    letI := skeletalCellStructure (X := X) K
    IsEmbedding (interiorMap (skeletonLT X K) n c) := by
  letI := skeletalCellStructure (X := X) K
  apply (IsEmbedding.of_comp_iff (f := interiorMap (skeletonLT X K) n c)
    (g := (Subtype.val : skeletonLT X K → X)) IsEmbedding.subtypeVal).mp
  exact CWStructure.interior_embedding n c.val

theorem skeletal_disjoint (K : ℕ) :
    letI := skeletalCellStructure (X := X) K
    (univ : Set (Σ n, Cell (skeletonLT X K) n)).PairwiseDisjoint
      (fun c => openCell (skeletonLT X K) c.1 c.2) := by
  letI := skeletalCellStructure (X := X) K
  intro a _ b _ hab
  change Disjoint (openCell (skeletonLT X K) a.1 a.2)
    (openCell (skeletonLT X K) b.1 b.2)
  rw [skeletal_openCell, skeletal_openCell]
  apply Disjoint.preimage
  apply CWStructure.disjoint_interiors (mem_univ ⟨a.1, a.2.val⟩)
    (mem_univ ⟨b.1, b.2.val⟩)
  intro h
  apply hab
  cases a with | mk n a =>
    cases b with | mk m b =>
      obtain rfl : n = m := congrArg Sigma.fst h
      have : a.val = b.val := by simpa using h
      simpa using Subtype.ext this

theorem skeletal_cover (K : ℕ) :
    letI := skeletalCellStructure (X := X) K
    ⋃ (n : ℕ) (c : Cell (skeletonLT X K) n), openCell (skeletonLT X K) n c = univ := by
  letI := skeletalCellStructure (X := X) K
  apply eq_univ_of_forall
  intro p
  obtain ⟨n, hn, c, hc⟩ := by simpa only [skeletonLT, mem_iUnion] using p.property
  exact mem_iUnion₂.mpr ⟨n, ⟨c, hn⟩, by rwa [skeletal_openCell]⟩

theorem skeletal_boundary_lands (K n : ℕ)
    (c : {c : Cell X n // n < K}) :
    letI := skeletalCellStructure (X := X) K
    MapsTo (boundaryMap (skeletonLT X K) n c) univ (skeletonLT (skeletonLT X K) n) := by
  letI := skeletalCellStructure (X := X) K
  intro p _
  rw [skeletal_skeletonLT, mem_preimage, min_eq_left c.property.le]
  exact CWStructure.boundary_lands n c.val (mem_univ p)

theorem skeletal_weak_topology (K : ℕ) (A : Set (skeletonLT X K)) :
    letI := skeletalCellStructure (X := X) K
    IsClosed A ↔ ∀ n (c : Cell (skeletonLT X K) n),
      IsClosed (characteristic (skeletonLT X K) n c ⁻¹' A) := by
  letI := skeletalCellStructure (X := X) K
  constructor
  · intro hA n c
    exact hA.preimage (skeletalCharacteristic K n c).continuous
  · intro hA
    let B : Set X := Subtype.val '' A
    have hB : B ⊆ skeletonLT X K := by rintro _ ⟨p, _, rfl⟩; exact p.property
    have hBclosed : IsClosed B := by
      apply isClosed_of_skeleton_cellwise CWStructure.disjoint_interiors
        CWStructure.closure_finite CWStructure.weak_topology K B hB
      intro n hn c
      have heq : characteristic X n c ⁻¹' B =
          characteristic (skeletonLT X K) n ⟨c, hn⟩ ⁻¹' A := by
        ext p
        constructor
        · rintro ⟨q, hq, hpq⟩
          have h : (skeletalCharacteristic K n ⟨c, hn⟩) p = q := Subtype.ext hpq.symm
          change (skeletalCharacteristic K n ⟨c, hn⟩) p ∈ A
          rwa [h]
        · intro hp
          exact ⟨(skeletalCharacteristic K n ⟨c, hn⟩) p, hp, rfl⟩
      rw [heq]
      exact hA n ⟨c, hn⟩
    have heq : (Subtype.val : skeletonLT X K → X) ⁻¹' B = A := by
      ext p
      exact ⟨fun ⟨q, hq, heq⟩ => (Subtype.val_injective heq) ▸ hq,
        fun hp => ⟨p, hp, rfl⟩⟩
    rw [← heq]
    exact hBclosed.preimage continuous_subtype_val

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

theorem skeletal_closure_finite (K n : ℕ)
    (c : {c : Cell X n // n < K}) :
    letI := skeletalCellStructure (X := X) K
    ∃ F : Finset (Σ m, Cell (skeletonLT X K) m),
      closedCell (skeletonLT X K) n c ⊆
        ⋃ d ∈ F, openCell (skeletonLT X K) d.1 d.2 := by
  classical
  letI := skeletalCellStructure (X := X) K
  obtain ⟨F, hF⟩ := CWStructure.closure_finite n c.val
  let forget : (Σ m, Cell (skeletonLT X K) m) → (Σ m, Cell X m) :=
    Sigma.map id (fun _ => Subtype.val)
  have hforget : Function.Injective forget :=
    Function.Injective.sigma_map Function.injective_id (fun _ => Subtype.val_injective)
  have hfinite : (forget ⁻¹' (F : Set (Σ m, Cell X m))).Finite :=
    Set.Finite.preimage (fun _ _ _ _ h => hforget h) F.finite_toSet
  refine ⟨hfinite.toFinset, ?_⟩
  intro p hp
  obtain ⟨q, hq⟩ := hp
  have hpamb : p.val ∈ closedCell X n c.val := ⟨q, congrArg Subtype.val hq⟩
  obtain ⟨d, hdF, hpd⟩ := mem_iUnion₂.mp (hF hpamb)
  obtain ⟨m, hm, a, hpa⟩ := by simpa only [skeletonLT, mem_iUnion] using p.property
  have hdeq : d = (⟨m, a⟩ : Σ m, Cell X m) := by
    by_contra hne
    exact Set.disjoint_left.mp (CWStructure.disjoint_interiors
      (mem_univ d) (mem_univ _) hne) hpd hpa
  have hdK : d.1 < K := by simpa only [hdeq] using hm
  let e : (Σ m, Cell (skeletonLT X K) m) := ⟨d.1, ⟨d.2, hdK⟩⟩
  refine mem_iUnion₂.mpr ⟨e, hfinite.mem_toFinset.mpr hdF, ?_⟩
  change p ∈ openCell (skeletonLT X K) d.1 ⟨d.2, hdK⟩
  rwa [skeletal_openCell]

/-- A CW structure on the actual skeletal subspace, retaining exactly the old
characteristic maps in the selected dimensions. -/
@[instance_reducible] def skeletalCWStructure (K : ℕ) : CWStructure (skeletonLT X K) := by
  letI := skeletalCellStructure (X := X) K
  exact cwStructureOfWeak (skeletal_interior_embedding K) (skeletal_disjoint K)
    (skeletal_cover K) (skeletal_boundary_lands K) (skeletal_closure_finite K)
    (skeletal_weak_topology K)

theorem oneSkeleton_isGraph :
    letI := skeletalCWStructure (X := X) 2
    IsGraph (OneSkeleton X) := by
  letI := skeletalCWStructure (X := X) 2
  intro n hn
  exact ⟨fun c => (Nat.not_lt_of_ge hn) c.property⟩

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

private theorem sphere_pathConnected (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace (Sphere n) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ (0 : EuclideanSpace ℝ (Fin n)) (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
  exact_mod_cast (show 1 < n from hn)

theorem skeletal_connected_pred (n : ℕ) (hn : 2 ≤ n)
    [ConnectedSpace (skeletonLT X (n + 1))] :
    ConnectedSpace (skeletonLT X n) := by
  letI := sphere_pathConnected n hn
  let z : Sphere n := Classical.choice inferInstance
  have hpre : PreconnectedSpace (skeletonLT X n) := by
    apply preconnectedSpace_of_forall_constant
    intro f hf x y
    let g : ∀ c : Cell X n, C(Disk n, Bool) :=
      fun c => ContinuousMap.const _ (f (attachingMap n c z))
    have hg : ∀ c (p : Sphere n),
        g c (boundaryInclusion n p) = f (attachingMap n c p) := by
      intro c p
      exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace (Sphere n))
        (hf.comp (attachingMap n c).continuous)
    obtain ⟨h, ⟨hleft, _⟩, _⟩ := attachmentPushout (X := X) n ⟨f, hf⟩ g hg
    exact (hleft x).symm.trans ((PreconnectedSpace.constant
      (inferInstance : PreconnectedSpace (skeletonLT X (n + 1))) h.continuous).trans (hleft y))
  letI := hpre
  have hne : Nonempty (skeletonLT X n) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (skeletonLT X (n + 1)))
    obtain ⟨p, _⟩ := (CWStructure.attachment_quotient n).surjective x
    cases p with
    | inl p => exact ⟨p⟩
    | inr p => exact ⟨attachingMap n p.1 z⟩
  exact { toNonempty := hne }

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- A connected finite CW complex has connected actual one-skeleton: attaching
higher disks along connected spheres cannot join components. -/
theorem finiteCW_oneSkeleton_connected [Finite (Σ n, Cell X n)] [ConnectedSpace X] :
    ConnectedSpace (OneSkeleton X) := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun d : Σ n, Cell X n => d.1)).bddAbove
  have hwhole : skeletonLT X (M + 2) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
      rw [CWStructure.cover]; trivial
    obtain ⟨n, c, hc⟩ := mem_iUnion₂.mp hx
    have hn : n < M + 2 := lt_of_le_of_lt (hM ⟨⟨n, c⟩, rfl⟩)
      (Nat.lt_succ_of_lt (Nat.lt_succ_self M))
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, mem_iUnion.mpr ⟨c, hc⟩⟩⟩
  have hlarge : ConnectedSpace (skeletonLT X (M + 2)) := by
    let e : skeletonLT X (M + 2) ≃ₜ X :=
      (Homeomorph.setCongr hwhole).trans (Homeomorph.Set.univ X)
    exact e.symm.surjective.connectedSpace e.symm.continuous
  have hdown : ∀ k, ConnectedSpace (skeletonLT X (2 + k)) →
      ConnectedSpace (OneSkeleton X) := by
    intro k
    induction k with
    | zero => exact fun h => h
    | succ k ih =>
      intro h
      letI := h
      exact ih (skeletal_connected_pred (2 + k) (Nat.le_add_right 2 k))
  exact hdown M ((Nat.add_comm M 2) ▸ hlarge)


/-- The algebraic step in van Kampen when the other side of the pushout is
trivial. The universal property must hold for every group in this universe. -/
theorem quotientOfKillingUniversalProperty
    {K G H : Type u} [Group K] [Group G] [Group H]
    (i : K →* G) (j : G →* H) (hkill : j.comp i = 1)
    (hup : ∀ (A : Type u) [Group A] (f : G →* A), f.comp i = 1 →
      ∃! h : H →* A, h.comp j = f) :
    ∃ e : G ⧸ Subgroup.normalClosure (Set.range i) ≃* H,
      ∀ g : G, e (QuotientGroup.mk g) = j g := by
  let N := Subgroup.normalClosure (Set.range i)
  have hn : N ≤ j.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨k, rfl⟩
    exact DFunLike.congr_fun hkill k
  let F : G ⧸ N →* H := QuotientGroup.lift N j hn
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : q.comp i = 1 := by
    ext k
    exact (QuotientGroup.eq_one_iff (N := N) (i k)).mpr
      (Subgroup.subset_normalClosure ⟨k, rfl⟩)
  obtain ⟨R, hR, _⟩ := hup (G ⧸ N) q hq
  have hRF : R.comp F = MonoidHom.id (G ⧸ N) := by
    apply QuotientGroup.monoidHom_ext
    ext g
    exact DFunLike.congr_fun hR g
  have hFR : F.comp R = MonoidHom.id H := by
    obtain ⟨h, _, huniq⟩ := hup H j hkill
    apply (huniq (F.comp R) ?_).trans (huniq (MonoidHom.id H) (by simp)).symm
    rw [MonoidHom.comp_assoc, hR]
    rfl
  exact ⟨{
    toFun := F
    invFun := R
    left_inv := fun a => DFunLike.congr_fun hRF a
    right_inv := fun b => DFunLike.congr_fun hFR b
    map_mul' := F.map_mul }, fun _ => rfl⟩

/-- The quotient consequence of the actual two-open-set theorem. This still
requires a suitable geometric cover; no such cover is assumed to exist. -/
theorem vanKampenQuotientOfSimplyConnectedRight
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hUp : IsPathConnected U) (hVp : IsPathConnected V)
    (hinter : IsPathConnected (U ∩ V)) [SimplyConnectedSpace V]
    (x : X) (hx : x ∈ U ∩ V) :
    ∃ e : Pi1 U ⟨x, hx.1⟩ ⧸
        Subgroup.normalClosure (Set.range (VanKampen.leftMap U V x hx)) ≃* Pi1 X x,
      ∀ g, e (QuotientGroup.mk g) = (VanKampen.ambientMap U x hx.1).induced g := by
  obtain ⟨hsq, hup⟩ := vanKampen X U V hU hV hcover hUp hVp hinter x hx
  have hright : (VanKampen.ambientMap V x hx.2).induced = 1 := by
    ext b
    simpa using congrArg (VanKampen.ambientMap V x hx.2).induced (Subsingleton.elim b 1)
  have hkill : (VanKampen.ambientMap U x hx.1).induced.comp
      (VanKampen.leftMap U V x hx) = 1 := by
    rw [hsq, hright]
    simp
  apply quotientOfKillingUniversalProperty (VanKampen.leftMap U V x hx)
    (VanKampen.ambientMap U x hx.1).induced hkill
  intro A _ f hf
  have hcompat : f.comp (VanKampen.leftMap U V x hx) =
      (1 : Pi1 V ⟨x, hx.2⟩ →* A).comp (VanKampen.rightMap U V x hx) := by
    simpa using hf
  obtain ⟨h, hfac, huniq⟩ := hup A f 1 hcompat
  refine ⟨h, hfac.1, fun k hk => huniq k ⟨hk, ?_⟩⟩
  rw [hright]
  simp

/-- Conjugating an attaching loop does not change the normal subgroup it
generates. This is the algebra behind independence of the whiskering path. -/
theorem normalClosureSingletonConjugate {G : Type u} [Group G] (a c : G) :
    Subgroup.normalClosure ({c * a * c⁻¹} : Set G) =
      Subgroup.normalClosure ({a} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro t ht
    rw [show t = c * a * c⁻¹ from ht]
    exact (inferInstance : (Subgroup.normalClosure ({a} : Set G)).Normal).conj_mem a
      (Subgroup.subset_normalClosure (Set.mem_singleton a)) c
  · apply Subgroup.normalClosure_le_normal
    intro t ht
    rw [show t = a from ht]
    have hh := (inferInstance :
      (Subgroup.normalClosure ({c * a * c⁻¹} : Set G)).Normal).conj_mem (c * a * c⁻¹)
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) c⁻¹
    have hc : c⁻¹ * (c * a * c⁻¹) * (c⁻¹)⁻¹ = a := by group
    rw [hc] at hh
    exact hh

/-- The basepoint change formula from §1.1 gives exactly conjugate relators. -/
theorem attachingLoopNormalClosureIndependent
    {X : Type u} [TopologicalSpace X] {x y : X}
    (d d' : Path x y) (b : Pi1 X y) :
    Subgroup.normalClosure ({changeBasepoint d' b} : Set (Pi1 X x)) =
      Subgroup.normalClosure ({changeBasepoint d b} : Set (Pi1 X x)) := by
  rw [basepointInner X x y d d' b]
  exact normalClosureSingletonConjugate _ _

/-- Naturality of basepoint transport with no endpoint casts hidden in the
map. This applies to the inclusion into a disk adjunction. -/
theorem inducedChangeBasepoint
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (d : Path x y) (b : Pi1 X y) :
    (show PointedMap X Y x (f x) from ⟨f, rfl⟩).induced (changeBasepoint d b) =
      changeBasepoint (d.map f.continuous)
        ((show PointedMap X Y y (f y) from ⟨f, rfl⟩).induced b) := by
  obtain ⟨p, rfl⟩ := loopClass_surjective b
  apply pathClass_injective
  rw [induced_pathClass, basepointFormula X x y d (loopClass p),
    basepointFormula Y (f x) (f y) (d.map f.continuous)]
  simp only [induced_pathClass, pathClass_loopClass,
    Path.Homotopic.Quotient.cast_rfl_rfl]
  change Path.Homotopic.Quotient.mk (((d.trans p).trans d.symm).map f.continuous) =
    Path.Homotopic.Quotient.mk
      (((d.map f.continuous).trans (p.map f.continuous)).trans (d.map f.continuous).symm)
  rw [Path.map_trans, Path.map_trans, Path.map_symm]

/-- Transport a quotient by the normally generated image across isomorphic
source and ambient groups. The two groups of relations may inhabit different
universes. -/
def quotientNormalClosureRangeEquiv
    {K : Type u} {G : Type v} {K' : Type w} {G' : Type z}
    [Group K] [Group G] [Group K'] [Group G']
    (i : K →* G) (i' : K' →* G') (eK : K ≃* K') (eG : G ≃* G')
    (h : ∀ k, eG (i k) = i' (eK k)) :
    G ⧸ Subgroup.normalClosure (Set.range i) ≃*
      G' ⧸ Subgroup.normalClosure (Set.range i') := by
  have hr : eG '' Set.range i = Set.range i' := by
    ext g
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨eK k, (h k).symm⟩
    · rintro ⟨k', rfl⟩
      obtain ⟨k, rfl⟩ := eK.surjective k'
      exact ⟨i k, ⟨k, rfl⟩, h k⟩
  exact QuotientGroup.congr (Subgroup.normalClosure (Set.range i))
    (Subgroup.normalClosure (Set.range i')) eG
    ((Subgroup.map_normalClosure (Set.range i) eG.toMonoidHom eG.surjective).trans
      (congrArg Subgroup.normalClosure hr))

@[simp] theorem quotientNormalClosureRangeEquiv_mk
    {K : Type u} {G : Type v} {K' : Type w} {G' : Type z}
    [Group K] [Group G] [Group K'] [Group G']
    (i : K →* G) (i' : K' →* G') (eK : K ≃* K') (eG : G ≃* G')
    (h : ∀ k, eG (i k) = i' (eK k)) (g : G) :
    quotientNormalClosureRangeEquiv i i' eK eG h (QuotientGroup.mk g) =
      QuotientGroup.mk (eG g) := rfl


def subtypeSumHomeomorph {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (p : A ⊕ B → Prop) :
    {z // p z} ≃ₜ {a // p (.inl a)} ⊕ {b // p (.inr b)} where
  toEquiv := Equiv.subtypeSum
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨a | b, h⟩
    · have hi := (IsOpenEmbedding.inl (X := A) (Y := B)).restrictPreimage {z | p z}
      apply (hi.continuousAt_iff (g := Equiv.subtypeSum) (x := ⟨a,h⟩)).mp
      exact continuous_inl.continuousAt
    · have hi := (IsOpenEmbedding.inr (X := A) (Y := B)).restrictPreimage {z | p z}
      apply (hi.continuousAt_iff (g := Equiv.subtypeSum) (x := ⟨b,h⟩)).mp
      exact continuous_inr.continuousAt
  continuous_invFun := continuous_sum_dom.mpr
    ⟨(continuous_inl.comp continuous_subtype_val).subtype_mk _,
     (continuous_inr.comp continuous_subtype_val).subtype_mk _⟩

def homotopyEquivPi1 {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) :
    Pi1 X x ≃* Pi1 Y (e x) :=
  oppositeEquiv ((FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x))

@[simp] theorem homotopyEquivPi1_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) (b : Pi1 X x) :
    homotopyEquivPi1 e x b =
      (⟨e.toFun, rfl⟩ : PointedMap X Y x (e x)).induced b := by
  apply pathClass_injective
  rw [induced_pathClass]
  simp [homotopyEquivPi1, oppositeEquiv, pathClass,
    CategoryTheory.Functor.FullyFaithful.mulEquivEnd,
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv,
    CategoryTheory.Functor.FullyFaithful.homEquiv,
    CategoryTheory.Equivalence.mk, End.homEquiv]
  rfl


theorem inducedHomotopyBasepoint
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (f g : C(A, B)) (H : f.Homotopy g) (x : A) (y z : B)
    (hf : f x = y) (hg : g x = z) (b : Pi1 A x) :
    (⟨f, hf⟩ : PointedMap A B x y).induced b =
      changeBasepoint ((H.evalAt x).cast hf.symm hg.symm)
        ((⟨g, hg⟩ : PointedMap A B x z).induced b) := by
  subst y
  subst z
  obtain ⟨p, rfl⟩ := loopClass_surjective b
  rw [inducedFormula A B x (f x) ⟨f,rfl⟩ p,
    inducedFormula A B x (g x) ⟨g,rfl⟩ p]
  simpa only [Path.cast_rfl_rfl] using unbasedHomotopy A B f g H x p

theorem pointedInducedBijectiveOfEq
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A,B)) (x : A) (y : B) (h : f x = y)
    (hf : Function.Bijective (⟨f,rfl⟩ : PointedMap A B x (f x)).induced) :
    Function.Bijective (⟨f,h⟩ : PointedMap A B x y).induced := by
  subst y
  exact hf

@[simp] theorem quotientNormalClosureRangeEquiv_symm_mk
    {K : Type u} {G : Type v} {K' : Type*} {G' : Type*}
    [Group K] [Group G] [Group K'] [Group G']
    (i : K →* G) (i' : K' →* G') (eK : K ≃* K') (eG : G ≃* G')
    (h : ∀ k, eG (i k) = i' (eK k)) (g : G') :
    (quotientNormalClosureRangeEquiv i i' eK eG h).symm (QuotientGroup.mk g) =
      QuotientGroup.mk (eG.symm g) := by
  apply (quotientNormalClosureRangeEquiv i i' eK eG h).injective
  simp


/-- A surjective map out of the free group with exactly the specified normal
kernel is the isomorphism defined by the presentation. -/
def presentedGroupEquivOfSurjective
    {E : Type u} {G : Type v} [Group G]
    (relators : Set (FreeGroup E)) (F : FreeGroup E →* G)
    (hF : Function.Surjective F)
    (hker : F.ker = Subgroup.normalClosure relators) :
    PresentedGroup relators ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective F hF)

@[simp] theorem presentedGroupEquivOfSurjective_mk
    {E : Type u} {G : Type v} [Group G]
    (relators : Set (FreeGroup E)) (F : FreeGroup E →* G)
    (hF : Function.Surjective F)
    (hker : F.ker = Subgroup.normalClosure relators) (w : FreeGroup E) :
    presentedGroupEquivOfSurjective relators F hF hker (PresentedGroup.mk relators w) = F w :=
  rfl

@[simp] theorem presentedGroupEquivOfSurjective_of
    {E : Type u} {G : Type v} [Group G]
    (relators : Set (FreeGroup E)) (F : FreeGroup E →* G)
    (hF : Function.Surjective F)
    (hker : F.ker = Subgroup.normalClosure relators) (e : E) :
    presentedGroupEquivOfSurjective relators F hF hker (PresentedGroup.of e) =
      F (FreeGroup.of e) := rfl

/-- Composing a quotient by existing relations with a quotient by the images
of further relations adds exactly those further relations to the normal kernel. -/
theorem kernelNormalClosure_comp
    {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (hf : Function.Surjective f)
    (S T : Set G)
    (hkerf : f.ker = Subgroup.normalClosure S)
    (hkerg : g.ker = Subgroup.normalClosure (f '' T)) :
    (g.comp f).ker = Subgroup.normalClosure (S ∪ T) := by
  let N := Subgroup.normalClosure (S ∪ T)
  have hkerN : f.ker ≤ N := by
    rw [hkerf]
    exact Subgroup.normalClosure_mono Set.subset_union_left
  have hmap : N.map f = Subgroup.normalClosure (f '' T) := by
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply Subgroup.normalClosure_le_normal
      rintro x (hx | hx)
      · have hxker : x ∈ f.ker := by
          rw [hkerf]
          exact Subgroup.subset_normalClosure hx
        change f x ∈ Subgroup.normalClosure (f '' T)
        rw [show f x = 1 from hxker]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_normalClosure ⟨x,hx,rfl⟩
    · letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨x,hx,rfl⟩
      exact ⟨x, Subgroup.subset_normalClosure (Or.inr hx), rfl⟩
  rw [← MonoidHom.comap_ker, hkerg, ← hmap]
  exact Subgroup.comap_map_eq_self hkerN

/-- A version indexed by chosen words and their images, as in adjoining
successive two-cells. -/
theorem kernelNormalClosure_comp_of_lifts
    {G : Type u} {H : Type v} {K : Type w} {R : Type z}
    [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (hf : Function.Surjective f)
    (S : Set G) (words : R → G) (relations : R → H)
    (hkerf : f.ker = Subgroup.normalClosure S)
    (hkerg : g.ker = Subgroup.normalClosure (Set.range relations))
    (hlift : ∀ r, f (words r) = relations r) :
    (g.comp f).ker = Subgroup.normalClosure (S ∪ Set.range words) := by
  apply kernelNormalClosure_comp f g hf S (Set.range words) hkerf
  rw [hkerg]
  congr 1
  ext h
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨words r, ⟨r,rfl⟩, hlift r⟩
  · rintro ⟨_,⟨r,rfl⟩,rfl⟩
    exact ⟨r, (hlift r).symm⟩


/-- The map from a fixed initial group into stage `n` of a sequence. -/
def finiteChainHomFrom {A : Type u} [Group A]
    (G : ℕ → Type v) [∀ n, Group (G n)] (initial : A →* G 0)
    (step : ∀ n, G n →* G (n+1)) : ∀ n, A →* G n
  | 0 => initial
  | n+1 => (step n).comp (finiteChainHomFrom G initial step n)

/-- The relations present initially, together with the first `n` sets of
additional relations, all written in the original group. -/
def finiteChainRelators {A : Type u} (initial : Set A) (relations : ℕ → Set A) : ℕ → Set A
  | 0 => initial
  | n+1 => finiteChainRelators initial relations n ∪ relations n

@[simp] theorem mem_finiteChainRelators {A : Type u} (initial : Set A)
    (relations : ℕ → Set A) (n : ℕ) (a : A) :
    a ∈ finiteChainRelators initial relations n ↔
      a ∈ initial ∨ ∃ k < n, a ∈ relations k := by
  induction n with
  | zero => simp [finiteChainRelators]
  | succ n ih =>
    simp only [finiteChainRelators, Set.mem_union, ih]
    constructor
    · rintro ((ha | ⟨k,hk,ha⟩) | ha)
      · exact Or.inl ha
      · exact Or.inr ⟨k,Nat.lt_succ_of_lt hk,ha⟩
      · exact Or.inr ⟨n,Nat.lt_succ_self n,ha⟩
    · rintro (ha | ⟨k,hk,ha⟩)
      · exact Or.inl (Or.inl ha)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Or.inl (Or.inr ⟨k,hk,ha⟩)
        · exact Or.inr ha

theorem finiteChainHomFrom_surjective
    {A : Type u} [Group A] (G : ℕ → Type v) [∀ n, Group (G n)]
    (initial : A →* G 0) (step : ∀ n, G n →* G (n+1))
    (hinitial : Function.Surjective initial) (n : ℕ)
    (hstep : ∀ k < n, Function.Surjective (step k)) :
    Function.Surjective (finiteChainHomFrom G initial step n) := by
  induction n with
  | zero => exact hinitial
  | succ n ih =>
    exact (hstep n (Nat.lt_succ_self n)).comp
      (ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk)))

/-- A finite sequence of surjective quotients has precisely the normal kernel
generated by all lifted relations. No assertion is assumed beyond stage `n`. -/
theorem finiteChainHomFrom_kernel
    {A : Type u} [Group A] (G : ℕ → Type v) [∀ n, Group (G n)]
    (initial : A →* G 0) (step : ∀ n, G n →* G (n+1))
    (hinitial : Function.Surjective initial)
    (S0 : Set A) (relations : ℕ → Set A)
    (hkerinitial : initial.ker = Subgroup.normalClosure S0) (n : ℕ)
    (hstep : ∀ k < n, Function.Surjective (step k))
    (hkerstep : ∀ k < n, (step k).ker = Subgroup.normalClosure
      (finiteChainHomFrom G initial step k '' relations k)) :
    (finiteChainHomFrom G initial step n).ker =
      Subgroup.normalClosure (finiteChainRelators S0 relations n) := by
  induction n with
  | zero => exact hkerinitial
  | succ n ih =>
    exact kernelNormalClosure_comp (finiteChainHomFrom G initial step n) (step n)
      (finiteChainHomFrom_surjective G initial step hinitial n
        (fun k hk => hstep k (Nat.lt_succ_of_lt hk)))
      (finiteChainRelators S0 relations n) (relations n)
      (ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
        (fun k hk => hkerstep k (Nat.lt_succ_of_lt hk)))
      (hkerstep n (Nat.lt_succ_self n))

/-- The finite-chain result when the original group is free, yielding the
presentation with exactly the union of the chosen lifted relators. -/
def finiteChainPresentedGroupEquiv
    {E : Type u} (G : ℕ → Type v) [∀ n, Group (G n)]
    (initial : FreeGroup E →* G 0) (step : ∀ n, G n →* G (n+1))
    (hinitial : Function.Surjective initial)
    (S0 : Set (FreeGroup E)) (relations : ℕ → Set (FreeGroup E))
    (hkerinitial : initial.ker = Subgroup.normalClosure S0) (n : ℕ)
    (hstep : ∀ k < n, Function.Surjective (step k))
    (hkerstep : ∀ k < n, (step k).ker = Subgroup.normalClosure
      (finiteChainHomFrom G initial step k '' relations k)) :
    PresentedGroup (finiteChainRelators S0 relations n) ≃* G n :=
  presentedGroupEquivOfSurjective (finiteChainRelators S0 relations n)
    (finiteChainHomFrom G initial step n)
    (finiteChainHomFrom_surjective G initial step hinitial n hstep)
    (finiteChainHomFrom_kernel G initial step hinitial S0 relations hkerinitial n hstep hkerstep)

@[simp] theorem finiteChainPresentedGroupEquiv_of
    {E : Type u} (G : ℕ → Type v) [∀ n, Group (G n)]
    (initial : FreeGroup E →* G 0) (step : ∀ n, G n →* G (n+1))
    (hinitial : Function.Surjective initial)
    (S0 : Set (FreeGroup E)) (relations : ℕ → Set (FreeGroup E))
    (hkerinitial : initial.ker = Subgroup.normalClosure S0) (n : ℕ)
    (hstep : ∀ k < n, Function.Surjective (step k))
    (hkerstep : ∀ k < n, (step k).ker = Subgroup.normalClosure
      (finiteChainHomFrom G initial step k '' relations k)) (e : E) :
    finiteChainPresentedGroupEquiv G initial step hinitial S0 relations hkerinitial n hstep hkerstep
      (PresentedGroup.of e) = finiteChainHomFrom G initial step n (FreeGroup.of e) := rfl


/-- Recover the surjectivity and exact kernel needed for finite-chain assembly
from a quotient isomorphism and its formula on quotient representatives. -/
theorem surjectiveAndKernelOfQuotientEquiv
    {A : Type u} {B : Type v} [Group A] [Group B]
    (relations : Set A) (f : A →* B)
    (e : A ⧸ Subgroup.normalClosure relations ≃* B)
    (he : ∀ a, e (QuotientGroup.mk a) = f a) :
    Function.Surjective f ∧ f.ker = Subgroup.normalClosure relations := by
  constructor
  · intro b
    obtain ⟨q,hq⟩ := e.surjective b
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a,(he a).symm.trans hq⟩
  · ext a
    change f a = 1 ↔ a ∈ Subgroup.normalClosure relations
    constructor
    · intro ha
      apply (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure relations) a).mp
      apply e.injective
      exact (he a).trans (ha.trans e.map_one.symm)
    · intro ha
      rw [← he a, (QuotientGroup.eq_one_iff
        (N := Subgroup.normalClosure relations) a).mpr ha, map_one]


namespace DiskAttachmentProof
open P202.Cellular.DiskAttachment
variable {X : Type u} [TopologicalSpace X] {n : ℕ} (a : C(Sphere n, X))

@[simp] theorem glue (z : Sphere n) :
    inclusion a (a z) = characteristic a (boundaryInclusion n z) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (DiskAttachment.Relation.glue z))

/-- Continuous descent on the topological adjunction, with its boundary
compatibility hypothesis stated explicitly. -/
def descend {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Disk n, Y))
    (h : ∀ z : Sphere n, f (a z) = g (boundaryInclusion n z)) : C(Space a, Y) := by
  let raw : X ⊕ Disk n → Y := Sum.elim f g
  have hc : Continuous raw := continuous_sum_dom.mpr ⟨f.continuous, g.continuous⟩
  have he : ∀ p q, setoid a p q → raw p = raw q := by
    intro p q hpq
    induction hpq with
    | rel p q hpq => cases hpq with | glue z => exact h z
    | refl p => rfl
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact ⟨Quotient.lift raw he, hc.quotient_lift he⟩

@[simp] theorem descend_inclusion {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Disk n, Y)) (h) (x : X) :
    descend a f g h (inclusion a x) = f x := rfl

@[simp] theorem descend_characteristic {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Disk n, Y)) (h) (z : Disk n) :
    descend a f g h (characteristic a z) = g z := rfl

theorem descend_unique {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Disk n, Y)) (h)
    (k : C(Space a, Y)) (hkX : ∀ x, k (inclusion a x) = f x)
    (hkD : ∀ z, k (characteristic a z) = g z) : k = descend a f g h := by
  ext y
  induction y using Quotient.inductionOn with
  | h y => cases y with
    | inl x => exact hkX x
    | inr z => exact hkD z

/-- The attaching sphere is killed because its map factors through the actual
contractible disk after adjunction. This holds in every dimension. -/
theorem killsAttachingSphere (z : Sphere n) (b : Pi1 (Sphere n) z) :
    (pointedInclusion a (a z)).induced ((pointedAttachingMap a z).induced b) = 1 := by
  let bd : PointedMap (Sphere n) (Disk n) z (boundaryInclusion n z) :=
    ⟨⟨boundaryInclusion n, continuous_subtype_val.subtype_mk _⟩, rfl⟩
  let chi : PointedMap (Disk n) (Space a) (boundaryInclusion n z) (inclusion a (a z)) :=
    ⟨characteristic a, (glue a z).symm⟩
  have he : (pointedInclusion a (a z)).comp (pointedAttachingMap a z) = chi.comp bd := by
    apply pointedMap_ext
    ext w
    exact glue a w
  have hc : ContractibleSpace (Disk n) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).contractibleSpace
      (Metric.nonempty_closedBall.mpr zero_le_one)
  letI := hc
  have hb : bd.induced b = 1 := Subsingleton.elim _ _
  have hh := congrArg (fun k => k.induced b) he
  simpa only [induced_comp, MonoidHom.comp_apply, hb, map_one] using hh

/-- Every transported attaching class lies in the inclusion kernel. In
particular this handles arbitrary, possibly unequal, chosen basepoints. -/
theorem killsTransportedAttachingSphere (z : Sphere n) {x : X}
    (d : Path x (a z)) (b : Pi1 (Sphere n) z) :
    (pointedInclusion a x).induced (attachingHom a z d b) = 1 := by
  change (pointedInclusion a x).induced
    (changeBasepoint d ((pointedAttachingMap a z).induced b)) = 1
  dsimp only [pointedInclusion]
  rw [inducedChangeBasepoint (inclusion a) d]
  change changeBasepoint (d.map (inclusion a).continuous)
    ((pointedInclusion a (a z)).induced ((pointedAttachingMap a z).induced b)) = 1
  rw [killsAttachingSphere, map_one]

theorem attachingNormalClosureLeKernel (z : Sphere n) {x : X} (d : Path x (a z)) :
    Subgroup.normalClosure (Set.range (attachingHom a z d)) ≤
      (pointedInclusion a x).induced.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨b, rfl⟩
  exact killsTransportedAttachingSphere a z d b

/-- The canonical candidate for the isomorphism in the independent Specs.
Its bijectivity follows from the geometric van Kampen calculation below. -/
def quotientToFundamentalGroup (z : Sphere n) {x : X} (d : Path x (a z)) :
    Pi1 X x ⧸ Subgroup.normalClosure (Set.range (attachingHom a z d)) →*
      Pi1 (Space a) (inclusion a x) :=
  QuotientGroup.lift _ (pointedInclusion a x).induced (attachingNormalClosureLeKernel a z d)

@[simp] theorem quotientToFundamentalGroup_mk (z : Sphere n) {x : X}
    (d : Path x (a z)) (b : Pi1 X x) :
    quotientToFundamentalGroup a z d (QuotientGroup.mk b) =
      (pointedInclusion a x).induced b := rfl

/-- Set-theoretic normal form for the adjunction: retain all old points and
exactly the interior points of the new disk. No topology is put on this sum
to claim that it is a topological disjoint union. -/
def normalFormRaw : X ⊕ Disk n → X ⊕ OpenDisk n
  | .inl x => .inl x
  | .inr z => if h : ‖z.val‖ < 1 then
      .inr ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩
    else .inl (a ⟨z.val, by
      rw [Metric.mem_sphere, dist_zero_right]
      have hz : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      exact le_antisymm hz (not_lt.mp h)⟩)

theorem normalFormRaw_glue (z : Sphere n) :
    normalFormRaw a (.inl (a z)) = normalFormRaw a (.inr (boundaryInclusion n z)) := by
  have hz : ‖z.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  simp only [normalFormRaw, boundaryInclusion, hz, lt_self_iff_false, dite_false]

def normalForm : Space a → X ⊕ OpenDisk n := Quotient.lift (normalFormRaw a) (by
  intro p q hpq
  induction hpq with
  | rel p q hpq => cases hpq with | glue z => exact normalFormRaw_glue a z
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def insertNormalForm : X ⊕ OpenDisk n → Space a :=
  Sum.elim (inclusion a) (fun z => characteristic a (interiorInclusion n z))

@[simp] theorem normalForm_inclusion (x : X) :
    normalForm a (inclusion a x) = .inl x := rfl

@[simp] theorem normalForm_interior (z : OpenDisk n) :
    normalForm a (characteristic a (interiorInclusion n z)) = .inr z := by
  have hz : ‖z.val‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using z.property
  simp only [normalForm, DiskAttachment.characteristic, interiorInclusion, normalFormRaw, hz, dite_true,
    Quotient.lift_mk, quotientMap, ContinuousMap.coe_mk]

theorem insertNormalForm_normalForm (y : Space a) :
    insertNormalForm a (normalForm a y) = y := by
  induction y using Quotient.inductionOn with
  | h y =>
    cases y with
    | inl x => rfl
    | inr z =>
      change insertNormalForm a (normalFormRaw a (.inr z)) = characteristic a z
      dsimp only [normalFormRaw]
      split_ifs with hz
      · rfl
      · exact glue a _

theorem normalForm_insertNormalForm (y : X ⊕ OpenDisk n) :
    normalForm a (insertNormalForm a y) = y := by
  cases y with
  | inl x => rfl
  | inr z => exact normalForm_interior a z

def normalFormEquiv : Space a ≃ X ⊕ OpenDisk n where
  toFun := normalForm a
  invFun := insertNormalForm a
  left_inv := insertNormalForm_normalForm a
  right_inv := normalForm_insertNormalForm a

theorem inclusion_injective : Function.Injective (inclusion a) := by
  intro x y h
  exact Sum.inl.inj (congrArg (normalForm a) h)

def interiorMap : OpenDisk n → Space a :=
  fun z => characteristic a (interiorInclusion n z)

theorem interiorMap_injective : Function.Injective (interiorMap a) := by
  intro x y h
  have hh := congrArg (normalForm a) h
  simpa only [interiorMap, normalForm_interior, Sum.inr.injEq] using hh

theorem quotientMap_eq_interior_iff (p : X ⊕ Disk n) (z : OpenDisk n) :
    quotientMap a p = interiorMap a z ↔ p = .inr (interiorInclusion n z) := by
  constructor
  · intro h
    have hh : normalFormRaw a p = .inr z := by
      exact (congrArg (normalForm a) h).trans (normalForm_interior a z)
    cases p with
    | inl x => simp only [normalFormRaw, Sum.inl_ne_inr] at hh
    | inr w =>
      dsimp only [normalFormRaw] at hh
      split_ifs at hh with hw
      · have hval := congrArg Subtype.val (Sum.inr.inj hh)
        exact congrArg Sum.inr (Subtype.ext hval)
  · rintro rfl
    rfl

theorem quotientMap_preimage_interior_image (S : Set (OpenDisk n)) :
    quotientMap a ⁻¹' (interiorMap a '' S) = Sum.inr '' (interiorInclusion n '' S) := by
  ext p
  constructor
  · rintro ⟨z, hz, heq⟩
    exact ⟨interiorInclusion n z, ⟨z, hz, rfl⟩,
      ((quotientMap_eq_interior_iff a p z).mp heq.symm).symm⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- The disk interior embeds as an open subset of the adjunction even when
the old space is not Hausdorff. -/
theorem interiorMap_isOpenEmbedding : IsOpenEmbedding (interiorMap a) := by
  have hi : IsOpenEmbedding (interiorInclusion n) :=
    Topology.IsOpenEmbedding.inclusion Metric.ball_subset_closedBall
      ((Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).preimage
        continuous_subtype_val)
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((characteristic a).continuous.comp hi.continuous) (interiorMap_injective a)
  intro S hS
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (quotientMap a ⁻¹' (interiorMap a '' S))
  rw [quotientMap_preimage_interior_image]
  exact isOpenMap_inr _ (hi.isOpenMap S hS)

def smallClosedDisk : Set (Space a) :=
  interiorMap a '' {z : OpenDisk n | ‖z.val‖ ≤ 1 / 2}

def oldOpen : Set (Space a) := (smallClosedDisk a)ᶜ
def diskOpen : Set (Space a) := Set.range (interiorMap a)

theorem smallClosedDisk_isClosed : IsClosed (smallClosedDisk a) := by
  have he : quotientMap a ⁻¹' smallClosedDisk a =
      Sum.inr '' {z : Disk n | ‖z.val‖ ≤ 1 / 2} := by
    rw [smallClosedDisk, quotientMap_preimage_interior_image]
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      have hz' : z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt hz (by norm_num)
      exact ⟨⟨z.val, hz'⟩, hz, Subtype.ext rfl⟩
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  change IsClosed (quotientMap a ⁻¹' smallClosedDisk a)
  rw [he]
  exact isClosedMap_inr _ (isClosed_le continuous_subtype_val.norm continuous_const)

theorem oldOpen_isOpen : IsOpen (oldOpen a) := (smallClosedDisk_isClosed a).isOpen_compl

theorem diskOpen_isOpen : IsOpen (diskOpen a) := (interiorMap_isOpenEmbedding a).isOpen_range

theorem openCover : oldOpen a ∪ diskOpen a = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y ∈ smallClosedDisk a
  · obtain ⟨z, _, rfl⟩ := hy
    exact Or.inr ⟨z, rfl⟩
  · exact Or.inl hy

def diskOpenHomeomorph : OpenDisk n ≃ₜ diskOpen a :=
  (interiorMap_isOpenEmbedding a).isEmbedding.toHomeomorph

theorem diskOpen_contractible : ContractibleSpace (diskOpen a) := by
  have hc : ContractibleSpace (OpenDisk n) :=
    (convex_ball (0 : EuclideanSpace ℝ (Fin n)) 1).contractibleSpace
      (Metric.nonempty_ball.mpr (by norm_num))
  letI := hc
  exact (diskOpenHomeomorph a).symm.contractibleSpace

theorem interior_mem_smallClosedDisk_iff (z : OpenDisk n) :
    interiorMap a z ∈ smallClosedDisk a ↔ ‖z.val‖ ≤ 1 / 2 := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (interiorMap_injective a he) ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem intersection_eq_annulus : oldOpen a ∩ diskOpen a =
    interiorMap a '' {z : OpenDisk n | 1 / 2 < ‖z.val‖} := by
  ext y
  constructor
  · rintro ⟨hy, ⟨z, rfl⟩⟩
    refine ⟨z, ?_, rfl⟩
    exact lt_of_not_ge ((interior_mem_smallClosedDisk_iff a z).not.mp hy)
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(interior_mem_smallClosedDisk_iff a z).not.mpr (not_le.mpr hz), ⟨z, rfl⟩⟩

abbrev AnnulusRadius := Set.Ioo (1 / 2 : ℝ) 1

def annulusParam (n : ℕ) : Sphere n × AnnulusRadius → OpenDisk n := fun p =>
  ⟨p.2.val • p.1.val, by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (lt_trans (by norm_num) p.2.property.1)]
    have hs : ‖p.1.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property
    rw [hs, mul_one]
    exact p.2.property.2⟩

theorem annulusParam_norm (p : Sphere n × AnnulusRadius) :
    ‖(annulusParam n p).val‖ = p.2.val := by
  have hs : ‖p.1.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property
  dsimp only [annulusParam]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (lt_trans (by norm_num) p.2.property.1), hs, mul_one]

theorem annulusParam_continuous (n : ℕ) : Continuous (annulusParam n) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)

theorem annulusParam_range (n : ℕ) : Set.range (annulusParam n) =
    {z : OpenDisk n | 1 / 2 < ‖z.val‖} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    rw [Set.mem_setOf_eq, annulusParam_norm]
    exact p.2.property.1
  · intro hz
    have hp : 0 < ‖z.val‖ := lt_trans (by norm_num) hz
    have hz1 : ‖z.val‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using z.property
    let s : Sphere n := ⟨‖z.val‖⁻¹ • z.val, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']⟩
    refine ⟨(s, ⟨‖z.val‖, hz, hz1⟩), ?_⟩
    apply Subtype.ext
    change ‖z.val‖ • (‖z.val‖⁻¹ • z.val) = z.val
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

abbrev Annulus (n : ℕ) := {z : OpenDisk n // (1 / 2 : ℝ) < ‖z.val‖}

def annulusPolar (n : ℕ) : Annulus n → Sphere n × AnnulusRadius := fun z =>
  let hp : 0 < ‖z.val.val‖ := lt_trans (by norm_num) z.property
  (⟨‖z.val.val‖⁻¹ • z.val.val, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']⟩,
   ⟨‖z.val.val‖, z.property, by
      simpa only [Metric.mem_ball, dist_zero_right] using z.val.property⟩)

def annulusHomeomorph (n : ℕ) : Sphere n × AnnulusRadius ≃ₜ Annulus n where
  toFun p := ⟨annulusParam n p, by rw [annulusParam_norm]; exact p.2.property.1⟩
  invFun := annulusPolar n
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp only [annulusPolar]
      rw [annulusParam_norm]
      change p.2.val⁻¹ • (p.2.val • p.1.val) = p.1.val
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) p.2.property.1)),
        one_smul]
    · apply Subtype.ext
      exact annulusParam_norm p
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change ‖z.val.val‖ • (‖z.val.val‖⁻¹ • z.val.val) = z.val.val
    rw [smul_smul, mul_inv_cancel₀
      (ne_of_gt (lt_trans (by norm_num) z.property)), one_smul]
  continuous_toFun := (annulusParam_continuous n).subtype_mk _
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
        (fun z => ne_of_gt (lt_trans (by norm_num) z.property))).smul
          (continuous_subtype_val.comp continuous_subtype_val)
    · exact (continuous_subtype_val.comp continuous_subtype_val).norm.subtype_mk _


def intersectionPolarHomeomorph : Sphere n × AnnulusRadius ≃ₜ ↥(oldOpen a ∩ diskOpen a) :=
  (annulusHomeomorph n).trans
    (((interiorMap_isOpenEmbedding a).isEmbedding.homeomorphImage
      {z : OpenDisk n | (1 / 2 : ℝ) < ‖z.val‖}).trans
      (Homeomorph.setCongr (intersection_eq_annulus a).symm))

@[simp] theorem intersectionPolarHomeomorph_coe (p : Sphere n × AnnulusRadius) :
    (intersectionPolarHomeomorph a p).val = interiorMap a (annulusParam n p) := rfl

noncomputable def productSpherePi1Equiv (z : Sphere n) (r : AnnulusRadius) :
    Pi1 (Sphere n × AnnulusRadius) (z, r) ≃* Pi1 (Sphere n) z := by
  have hc : ContractibleSpace AnnulusRadius :=
    (convex_Ioo (1 / 2 : ℝ) 1).contractibleSpace ⟨r, r.property⟩
  letI := hc
  letI : Unique (Pi1 AnnulusRadius r) := { default := 1, uniq := fun _ => Subsingleton.elim _ _ }
  exact (fundamentalGroupProdEquiv (Sphere n) AnnulusRadius z r).trans
    (MulEquiv.prodUnique : (Pi1 (Sphere n) z × Pi1 AnnulusRadius r) ≃* Pi1 (Sphere n) z)

@[simp] theorem productSpherePi1Equiv_apply (z : Sphere n) (r : AnnulusRadius)
    (b : Pi1 (Sphere n × AnnulusRadius) (z, r)) :
    productSpherePi1Equiv z r b =
      (BasicFundamentalGroups.first (Sphere n) AnnulusRadius z r).induced b := rfl

noncomputable def intersectionSpherePi1Equiv (z : Sphere n) (r : AnnulusRadius) :
    Pi1 ↥(oldOpen a ∩ diskOpen a) (intersectionPolarHomeomorph a (z,r)) ≃*
      Pi1 (Sphere n) z :=
  (pointedHomeomorphEquiv (intersectionPolarHomeomorph a).symm
    (intersectionPolarHomeomorph a (z,r)) (z,r)
    ((intersectionPolarHomeomorph a).symm_apply_apply (z,r))).trans
    (productSpherePi1Equiv z r)


def intersectionDirection : C(↥(oldOpen a ∩ diskOpen a), Sphere n) :=
  ⟨fun y => ((intersectionPolarHomeomorph a).symm y).1,
    continuous_fst.comp (intersectionPolarHomeomorph a).symm.continuous⟩

def pointedIntersectionDirection (y : ↥(oldOpen a ∩ diskOpen a)) :
    PointedMap ↥(oldOpen a ∩ diskOpen a) (Sphere n) y (intersectionDirection a y) :=
  ⟨intersectionDirection a, rfl⟩

noncomputable def intersectionDirectionPi1Equiv (y : ↥(oldOpen a ∩ diskOpen a)) :
    Pi1 ↥(oldOpen a ∩ diskOpen a) y ≃* Pi1 (Sphere n) (intersectionDirection a y) :=
  (pointedHomeomorphEquiv (intersectionPolarHomeomorph a).symm y
    ((intersectionPolarHomeomorph a).symm y) rfl).trans
    (productSpherePi1Equiv ((intersectionPolarHomeomorph a).symm y).1
      ((intersectionPolarHomeomorph a).symm y).2)

@[simp] theorem intersectionDirectionPi1Equiv_apply (y : ↥(oldOpen a ∩ diskOpen a))
    (b : Pi1 ↥(oldOpen a ∩ diskOpen a) y) :
    intersectionDirectionPi1Equiv a y b = (pointedIntersectionDirection a y).induced b := by
  change ((BasicFundamentalGroups.first (Sphere n) AnnulusRadius
    ((intersectionPolarHomeomorph a).symm y).1
    ((intersectionPolarHomeomorph a).symm y).2).induced.comp
      (⟨⟨(intersectionPolarHomeomorph a).symm,
        (intersectionPolarHomeomorph a).symm.continuous⟩, rfl⟩ :
          PointedMap ↥(oldOpen a ∩ diskOpen a) (Sphere n × AnnulusRadius)
            y ((intersectionPolarHomeomorph a).symm y)).induced) b = _
  rw [← induced_comp]
  rfl


@[simp] theorem intersectionDirection_param (p : Sphere n × AnnulusRadius) :
    intersectionDirection a (intersectionPolarHomeomorph a p) = p.1 :=
  congrArg Prod.fst ((intersectionPolarHomeomorph a).symm_apply_apply p)

def intersectionInteriorPoint (z : Annulus n) : ↥(oldOpen a ∩ diskOpen a) :=
  ⟨interiorMap a z.val, by
    rw [intersection_eq_annulus]
    exact ⟨z.val, z.property, rfl⟩⟩

theorem intersectionPolarHomeomorph_symm_interior (z : Annulus n) :
    (intersectionPolarHomeomorph a).symm (intersectionInteriorPoint a z) =
      annulusPolar n z := by
  apply (intersectionPolarHomeomorph a).injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change interiorMap a z.val = interiorMap a
    ((annulusHomeomorph n) ((annulusHomeomorph n).symm z)).val
  rw [Homeomorph.apply_symm_apply]

@[simp] theorem intersectionDirection_interior_coe (z : Annulus n) :
    (intersectionDirection a (intersectionInteriorPoint a z)).val =
      ‖z.val.val‖⁻¹ • z.val.val := by
  change (((intersectionPolarHomeomorph a).symm (intersectionInteriorPoint a z)).1).val = _
  rw [intersectionPolarHomeomorph_symm_interior]
  rfl


theorem intersection_pathConnected (hn : 2 ≤ n) :
    IsPathConnected (oldOpen a ∩ diskOpen a) := by
  have hs : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simpa using (show 1 < n by omega)))
      0 zero_le_one
  have hr : IsPathConnected (Set.Ioo (1 / 2 : ℝ) 1) :=
    (convex_Ioo _ _).isPathConnected ⟨3 / 4, by norm_num⟩
  have : PathConnectedSpace (Sphere n) := isPathConnected_iff_pathConnectedSpace.mp hs
  have : PathConnectedSpace AnnulusRadius := isPathConnected_iff_pathConnectedSpace.mp hr
  rw [intersection_eq_annulus, ← annulusParam_range]
  have hh : IsPathConnected (Set.range (annulusParam n)) := by
    simpa only [Set.image_univ] using
      (isPathConnected_univ : IsPathConnected (Set.univ : Set (Sphere n × AnnulusRadius))).image
        (annulusParam_continuous n)
  exact hh.image ((characteristic a).continuous.comp (continuous_subtype_val.subtype_mk _))

theorem inclusion_mem_oldOpen (x : X) : inclusion a x ∈ oldOpen a := by
  intro hx
  obtain ⟨z, _, he⟩ := hx
  have hh := congrArg (normalForm a) he
  simp only [interiorMap, normalForm_interior, normalForm_inclusion, Sum.inr_ne_inl] at hh

def oldInclusion : C(X, oldOpen a) :=
  ⟨fun x => ⟨inclusion a x, inclusion_mem_oldOpen a x⟩, (inclusion a).continuous.subtype_mk _⟩

theorem characteristic_mem_smallClosedDisk_iff (z : Disk n) :
    characteristic a z ∈ smallClosedDisk a ↔ ‖z.val‖ ≤ 1 / 2 := by
  constructor
  · rintro ⟨w, hw, he⟩
    have hzw : z = interiorInclusion n w :=
      Sum.inr.inj ((quotientMap_eq_interior_iff a (.inr z) w).mp he.symm)
    rw [hzw]
    exact hw
  · intro hz
    have hz' : z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hz (by norm_num)
    exact ⟨⟨z.val, hz'⟩, hz, rfl⟩

theorem characteristic_mem_oldOpen_iff (z : Disk n) :
    characteristic a z ∈ oldOpen a ↔ 1 / 2 < ‖z.val‖ := by
  exact (characteristic_mem_smallClosedDisk_iff a z).not.trans not_le

def diskDirection (z : Disk n) (hz : 1 / 2 < ‖z.val‖) : Sphere n :=
  ⟨‖z.val‖⁻¹ • z.val, by
    have hp : 0 < ‖z.val‖ := lt_trans (by norm_num) hz
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']⟩

def radialPoint (z : Disk n) (hz : 1 / 2 < ‖z.val‖) (t : unitInterval) : Disk n :=
  ⟨((1 - (t : ℝ)) + (t : ℝ) / ‖z.val‖) • z.val, by
    have hp : 0 < ‖z.val‖ := lt_trans (by norm_num) hz
    have hs : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖z.val‖ :=
      add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 hp.le)
    have hle : ‖z.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs, add_mul, div_mul_cancel₀ _ hp.ne']
    nlinarith [t.property.1, t.property.2]⟩

theorem radialPoint_norm (z : Disk n) (hz : 1 / 2 < ‖z.val‖) (t : unitInterval) :
    ‖(radialPoint z hz t).val‖ = (1 - (t : ℝ)) * ‖z.val‖ + (t : ℝ) := by
  have hp : 0 < ‖z.val‖ := lt_trans (by norm_num) hz
  have hs : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖z.val‖ :=
    add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 hp.le)
  dsimp only [radialPoint]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, add_mul, div_mul_cancel₀ _ hp.ne']

theorem radialPoint_continuous (z : Disk n) (hz : 1 / 2 < ‖z.val‖) :
    Continuous (radialPoint z hz) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub continuous_subtype_val).add
    (continuous_subtype_val.div_const ‖z.val‖)).smul continuous_const

theorem radialPoint_mem_oldOpen (z : Disk n) (hz : 1 / 2 < ‖z.val‖)
    (t : unitInterval) : characteristic a (radialPoint z hz t) ∈ oldOpen a := by
  apply (characteristic_mem_oldOpen_iff a _).mpr
  rw [radialPoint_norm]
  have hle : ‖z.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  nlinarith [t.property.1, t.property.2]

def radialPath (z : Disk n) (hz : 1 / 2 < ‖z.val‖) :
    Path (⟨characteristic a z, (characteristic_mem_oldOpen_iff a z).mpr hz⟩ : oldOpen a)
      (oldInclusion a (a (diskDirection z hz))) where
  toFun t := ⟨characteristic a (radialPoint z hz t), radialPoint_mem_oldOpen a z hz t⟩
  continuous_toFun := ((characteristic a).continuous.comp
    (radialPoint_continuous z hz)).subtype_mk _
  source' := by
    apply Subtype.ext
    congr 1
    apply Subtype.ext
    simp [radialPoint]
  target' := by
    apply Subtype.ext
    change characteristic a (radialPoint z hz 1) = inclusion a (a (diskDirection z hz))
    rw [show radialPoint z hz 1 = boundaryInclusion n (diskDirection z hz) by
      apply Subtype.ext
      simp [radialPoint, diskDirection, boundaryInclusion]]
    exact (glue a _).symm

theorem oldOpen_pathConnectedSpace [PathConnectedSpace X] : PathConnectedSpace (oldOpen a) := by
  have hreach : ∀ y : oldOpen a, ∃ x : X, Joined y (oldInclusion a x) := by
    rintro ⟨y, hy⟩
    induction y using Quotient.inductionOn with
    | h p =>
      cases p with
      | inl x => exact ⟨x, ⟨Path.refl _⟩⟩
      | inr z =>
        have hz : 1 / 2 < ‖z.val‖ := (characteristic_mem_oldOpen_iff a z).mp hy
        exact ⟨a (diskDirection z hz), ⟨radialPath a z hz⟩⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  refine ⟨⟨oldInclusion a x⟩, fun y w => ?_⟩
  obtain ⟨xy, ⟨py⟩⟩ := hreach y
  obtain ⟨xw, ⟨pw⟩⟩ := hreach w
  exact ⟨(py.trans ((PathConnectedSpace.somePath xy xw).map (oldInclusion a).continuous)).trans pw.symm⟩

/-- Van Kampen applied to the concrete disk-adjunction cover. The old-open-set retraction and its attaching-sphere map are identified below. -/
theorem diskCoverQuotient [PathConnectedSpace X] (hn : 2 ≤ n)
    (y : Space a) (hy : y ∈ oldOpen a ∩ diskOpen a) :
    ∃ e : Pi1 (oldOpen a) ⟨y, hy.1⟩ ⧸ Subgroup.normalClosure
        (Set.range (VanKampen.leftMap (oldOpen a) (diskOpen a) y hy)) ≃* Pi1 (Space a) y,
      ∀ b, e (QuotientGroup.mk b) = (VanKampen.ambientMap (oldOpen a) y hy.1).induced b := by
  have : ContractibleSpace (diskOpen a) := diskOpen_contractible a
  have : PathConnectedSpace (oldOpen a) := oldOpen_pathConnectedSpace a
  exact vanKampenQuotientOfSimplyConnectedRight (oldOpen a) (diskOpen a)
    (oldOpen_isOpen a) (diskOpen_isOpen a) (openCover a)
    (isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
    (isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
    (intersection_pathConnected a hn) y hy

abbrev Collar (n : ℕ) := {z : Disk n // 1 / 2 < ‖z.val‖}

abbrev OldPreimage := {p : X ⊕ Disk n // quotientMap a p ∈ oldOpen a}

def oldRaw {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) (g : C(Collar n, Y)) : OldPreimage a → Y := fun p =>
  match p with
  | ⟨.inl x, _⟩ => f x
  | ⟨.inr z, hz⟩ => g ⟨z, (characteristic_mem_oldOpen_iff a z).mp hz⟩

theorem oldRaw_continuous {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) (g : C(Collar n, Y)) :
    Continuous (oldRaw a f g) := by
  let H := subtypeSumHomeomorph (fun p : X ⊕ Disk n => quotientMap a p ∈ oldOpen a)
  have hc : Continuous (fun p : {x : X // quotientMap a (.inl x) ∈ oldOpen a} ⊕
      {z : Disk n // quotientMap a (.inr z) ∈ oldOpen a} =>
      match p with
      | .inl x => f x.val
      | .inr z => g ⟨z.val, (characteristic_mem_oldOpen_iff a z.val).mp z.property⟩) := by
    apply continuous_sum_dom.mpr
    constructor
    · exact f.continuous.comp continuous_subtype_val
    · exact g.continuous.comp (continuous_subtype_val.subtype_mk _)
  convert hc.comp H.continuous using 1
  funext p
  rcases p with ⟨p,hp⟩
  cases p <;> rfl

def collarDirection (n : ℕ) : C(Collar n, Sphere n) :=
  ⟨fun z => diskDirection z.val z.property, by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀ (by
      intro z
      exact ne_of_gt (lt_trans (by norm_num) z.property))).smul
        (continuous_subtype_val.comp continuous_subtype_val)⟩

@[simp] theorem diskDirection_boundary (z : Sphere n) :
    diskDirection (boundaryInclusion n z) (by
      have hz : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
      change (1:ℝ)/2 < ‖z.val‖
      rw [hz]
      norm_num) = z := by
  apply Subtype.ext
  have hz : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  simp [diskDirection, boundaryInclusion, hz]

theorem oldRaw_factors_of_boundary {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Collar n, Y))
    (hglue : ∀ z : Sphere n, f (a z) = g ⟨boundaryInclusion n z, by
      have hz : ‖z.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using z.property
      change (1:ℝ)/2 < ‖z.val‖
      rw [hz]
      norm_num⟩) :
    Function.FactorsThrough (oldRaw a f g)
      ((oldOpen a).restrictPreimage (quotientMap a)) := by
  have aux : ∀ (p q : X ⊕ Disk n), setoid a p q →
      ∀ hp hq, oldRaw a f g ⟨p,hp⟩ =
        oldRaw a f g ⟨q,hq⟩ := by
    intro p q h
    induction h with
    | rel p q h =>
      cases h with
      | glue z =>
        intro hp hq
        exact hglue z
    | refl p => intro hp hq; rfl
    | symm p q h ih => intro hp hq; exact (ih hq hp).symm
    | trans p q r hpq hqr ih₁ ih₂ =>
      intro hp hr
      have hq : quotientMap a q ∈ oldOpen a := by
        have he : quotientMap a p = quotientMap a q := Quotient.sound hpq
        rw [← he]
        exact hp
      exact (ih₁ hp hq).trans (ih₂ hq hr)
  intro p q h
  exact aux p.val q.val (Quotient.exact (congrArg Subtype.val h)) p.property q.property

theorem oldRaw_factors :
    Function.FactorsThrough (oldRaw a (ContinuousMap.id X) (a.comp (collarDirection n)))
      ((oldOpen a).restrictPreimage (quotientMap a)) := by
  apply oldRaw_factors_of_boundary
  intro z
  dsimp only [ContinuousMap.id_apply, ContinuousMap.comp_apply, collarDirection, ContinuousMap.coe_mk]
  rw [diskDirection_boundary]

def oldQuotient : C(OldPreimage a, oldOpen a) :=
  ⟨(oldOpen a).restrictPreimage (quotientMap a),
    continuous_quotient_mk'.restrictPreimage⟩

theorem oldQuotient_isQuotientMap : IsQuotientMap (oldQuotient a) :=
  isQuotientMap_quotient_mk'.restrictPreimage_isOpen (oldOpen_isOpen a)

def oldDescend {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Collar n, Y))
    (h : Function.FactorsThrough (oldRaw a f g) (oldQuotient a)) : C(oldOpen a, Y) :=
  (oldQuotient_isQuotientMap a).lift ⟨oldRaw a f g, oldRaw_continuous a f g⟩ h

@[simp] theorem oldDescend_oldQuotient {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Collar n, Y)) (h) (p : OldPreimage a) :
    oldDescend a f g h (oldQuotient a p) = oldRaw a f g p :=
  DFunLike.congr_fun ((oldQuotient_isQuotientMap a).lift_comp
    ⟨oldRaw a f g, oldRaw_continuous a f g⟩ h) p

def oldRetraction : C(oldOpen a, X) :=
  (oldQuotient_isQuotientMap a).lift
    ⟨oldRaw a (ContinuousMap.id X) (a.comp (collarDirection n)),
      oldRaw_continuous a _ _⟩ (oldRaw_factors a)

@[simp] theorem oldRetraction_oldInclusion (x : X) :
    oldRetraction a (oldInclusion a x) = x := by
  have he := IsQuotientMap.lift_comp
    (oldQuotient_isQuotientMap a)
    (⟨oldRaw a (ContinuousMap.id X) (a.comp (collarDirection n)),
      oldRaw_continuous a _ _⟩ : C(OldPreimage a, X)) (oldRaw_factors a)
  exact DFunLike.congr_fun he ⟨.inl x, inclusion_mem_oldOpen a x⟩

@[simp] theorem oldRetraction_characteristic (z : Disk n) (hz : 1/2 < ‖z.val‖) :
    oldRetraction a ⟨characteristic a z, (characteristic_mem_oldOpen_iff a z).mpr hz⟩ =
      a (diskDirection z hz) := by
  have he := IsQuotientMap.lift_comp
    (oldQuotient_isQuotientMap a)
    (⟨oldRaw a (ContinuousMap.id X) (a.comp (collarDirection n)),
      oldRaw_continuous a _ _⟩ : C(OldPreimage a, X)) (oldRaw_factors a)
  exact DFunLike.congr_fun he ⟨.inr z, (characteristic_mem_oldOpen_iff a z).mpr hz⟩


@[simp] theorem radialPoint_zero (z : Disk n) (hz : 1/2 < ‖z.val‖) :
    radialPoint z hz 0 = z := by
  apply Subtype.ext
  simp [radialPoint]

@[simp] theorem radialPoint_one (z : Disk n) (hz : 1/2 < ‖z.val‖) :
    radialPoint z hz 1 = boundaryInclusion n (diskDirection z hz) := by
  apply Subtype.ext
  simp [radialPoint, boundaryInclusion, diskDirection]

@[simp] theorem radialPoint_boundary (z : Sphere n) (hz : 1/2 < ‖(boundaryInclusion n z).val‖)
    (t : unitInterval) : radialPoint (boundaryInclusion n z) hz t = boundaryInclusion n z := by
  apply Subtype.ext
  have hz1 : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  simp [radialPoint, boundaryInclusion, hz1]

def collarRadial : C(Collar n × unitInterval, oldOpen a) :=
  ⟨fun p => ⟨characteristic a (radialPoint p.1.val p.1.property p.2),
    radialPoint_mem_oldOpen a p.1.val p.1.property p.2⟩, by
    apply Continuous.subtype_mk
    apply (characteristic a).continuous.comp
    apply Continuous.subtype_mk
    have hz : ∀ z : Collar n, ‖z.val.val‖ ≠ 0 :=
      fun z => ne_of_gt (lt_trans (by norm_num) z.property)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_snd).div
        ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).norm
        (fun p => hz p.1))).smul
          ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst)⟩

def oldConstantCurried : C(X, C(unitInterval, oldOpen a)) :=
  ContinuousMap.curry ((oldInclusion a).comp ContinuousMap.fst)

theorem oldDeformation_factors :
    Function.FactorsThrough
      (oldRaw a (oldConstantCurried a) (ContinuousMap.curry (collarRadial a)))
      (oldQuotient a) := by
  apply oldRaw_factors_of_boundary
  intro z
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change inclusion a (a z) = characteristic a (radialPoint (boundaryInclusion n z) _ t)
  rw [radialPoint_boundary]
  exact glue a z

def oldDeformationCurried : C(oldOpen a, C(unitInterval, oldOpen a)) :=
  oldDescend a (oldConstantCurried a) (ContinuousMap.curry (collarRadial a))
    (oldDeformation_factors a)

@[simp] theorem oldDeformationCurried_inclusion (x : X) (t : unitInterval) :
    oldDeformationCurried a (oldInclusion a x) t = oldInclusion a x := by
  have he := oldDescend_oldQuotient a (oldConstantCurried a)
    (ContinuousMap.curry (collarRadial a)) (oldDeformation_factors a)
    ⟨.inl x, inclusion_mem_oldOpen a x⟩
  exact DFunLike.congr_fun he t

@[simp] theorem oldDeformationCurried_characteristic (z : Disk n)
    (hz : 1/2 < ‖z.val‖) (t : unitInterval) :
    oldDeformationCurried a ⟨characteristic a z, (characteristic_mem_oldOpen_iff a z).mpr hz⟩ t =
      ⟨characteristic a (radialPoint z hz t), radialPoint_mem_oldOpen a z hz t⟩ := by
  have he := oldDescend_oldQuotient a (oldConstantCurried a)
    (ContinuousMap.curry (collarRadial a)) (oldDeformation_factors a)
    ⟨.inr z, (characteristic_mem_oldOpen_iff a z).mpr hz⟩
  exact DFunLike.congr_fun he t

def oldDeformation : (ContinuousMap.id (oldOpen a)).Homotopy
    ((oldInclusion a).comp (oldRetraction a)) where
  toFun p := oldDeformationCurried a p.2 p.1
  continuous_toFun := (ContinuousMap.continuous_uncurry_of_continuous
    (oldDeformationCurried a)).comp continuous_swap
  map_zero_left y := by
    obtain ⟨p, rfl⟩ := (oldQuotient_isQuotientMap a).surjective y
    rcases p with ⟨p,hp⟩
    cases p with
    | inl x => exact oldDeformationCurried_inclusion a x 0
    | inr z =>
      change oldDeformationCurried a ⟨characteristic a z, hp⟩ 0 = ⟨characteristic a z, hp⟩
      rw [oldDeformationCurried_characteristic a z ((characteristic_mem_oldOpen_iff a z).mp hp) 0]
      apply Subtype.ext
      exact congrArg (characteristic a) (radialPoint_zero z _)
  map_one_left y := by
    obtain ⟨p, rfl⟩ := (oldQuotient_isQuotientMap a).surjective y
    rcases p with ⟨p,hp⟩
    cases p with
    | inl x =>
      change oldDeformationCurried a (oldInclusion a x) 1 =
        oldInclusion a (oldRetraction a (oldInclusion a x))
      rw [oldDeformationCurried_inclusion, oldRetraction_oldInclusion]
    | inr z =>
      change oldDeformationCurried a ⟨characteristic a z, hp⟩ 1 =
        oldInclusion a (oldRetraction a ⟨characteristic a z, hp⟩)
      rw [oldDeformationCurried_characteristic a z ((characteristic_mem_oldOpen_iff a z).mp hp) 1,
        oldRetraction_characteristic a z ((characteristic_mem_oldOpen_iff a z).mp hp)]
      apply Subtype.ext
      change characteristic a (radialPoint z ((characteristic_mem_oldOpen_iff a z).mp hp) 1) =
        inclusion a (a (diskDirection z ((characteristic_mem_oldOpen_iff a z).mp hp)))
      rw [radialPoint_one]
      exact (glue a _).symm


def oldRetractionHomotopyEquiv : ContinuousMap.HomotopyEquiv (oldOpen a) X where
  toFun := oldRetraction a
  invFun := oldInclusion a
  left_inv := ⟨(oldDeformation a).symm⟩
  right_inv := by
    have he : (oldRetraction a).comp (oldInclusion a) = ContinuousMap.id X := by
      ext x
      exact oldRetraction_oldInclusion a x
    rw [he]

def oldRetractionPi1Equiv (y : oldOpen a) :
    Pi1 (oldOpen a) y ≃* Pi1 X (oldRetraction a y) :=
  homotopyEquivPi1 (oldRetractionHomotopyEquiv a) y

@[simp] theorem oldRetractionPi1Equiv_apply (y : oldOpen a) (b : Pi1 (oldOpen a) y) :
    oldRetractionPi1Equiv a y b =
      (⟨oldRetraction a, rfl⟩ : PointedMap (oldOpen a) X y (oldRetraction a y)).induced b :=
  homotopyEquivPi1_apply (oldRetractionHomotopyEquiv a) y b

theorem oldRetraction_induced_bijective (y : oldOpen a) :
    Function.Bijective (⟨oldRetraction a, rfl⟩ :
      PointedMap (oldOpen a) X y (oldRetraction a y)).induced :=
  by
    have he : (oldRetractionPi1Equiv a y : Pi1 (oldOpen a) y → Pi1 X (oldRetraction a y)) =
        (⟨oldRetraction a, rfl⟩ : PointedMap (oldOpen a) X y (oldRetraction a y)).induced :=
      funext (oldRetractionPi1Equiv_apply a y)
    rw [← he]
    exact (oldRetractionPi1Equiv a y).bijective


theorem oldRetraction_intersection (y : ↥(oldOpen a ∩ diskOpen a)) :
    oldRetraction a ⟨y.val,y.property.1⟩ = a (intersectionDirection a y) := by
  obtain ⟨w, hw⟩ := y.property.2
  have hn : (1/2:ℝ) < ‖w.val‖ := by
    apply lt_of_not_ge
    intro hn
    apply y.property.1
    exact ⟨w, hn, hw⟩
  have hy : y = intersectionInteriorPoint a ⟨w,hn⟩ := Subtype.ext hw.symm
  rw [hy]
  rw [show (⟨(intersectionInteriorPoint a ⟨w,hn⟩).val,
      (intersectionInteriorPoint a ⟨w,hn⟩).property.1⟩ : oldOpen a) =
    ⟨characteristic a (interiorInclusion n w),
      (characteristic_mem_oldOpen_iff a _).mpr (by exact hn)⟩ from rfl]
  rw [oldRetraction_characteristic a (interiorInclusion n w) (by exact hn)]
  congr 1
  apply Subtype.ext
  exact (intersectionDirection_interior_coe a ⟨w,hn⟩).symm

@[simp] theorem intersectionSpherePi1Equiv_apply (z : Sphere n) (r : AnnulusRadius)
    (b : Pi1 ↥(oldOpen a ∩ diskOpen a) (intersectionPolarHomeomorph a (z,r))) :
    intersectionSpherePi1Equiv a z r b =
      (⟨intersectionDirection a, intersectionDirection_param a (z,r)⟩ :
        PointedMap ↥(oldOpen a ∩ diskOpen a) (Sphere n)
          (intersectionPolarHomeomorph a (z,r)) z).induced b := by
  change ((BasicFundamentalGroups.first (Sphere n) AnnulusRadius z r).induced.comp
      (⟨⟨(intersectionPolarHomeomorph a).symm,
        (intersectionPolarHomeomorph a).symm.continuous⟩,
        (intersectionPolarHomeomorph a).symm_apply_apply (z,r)⟩ :
          PointedMap ↥(oldOpen a ∩ diskOpen a) (Sphere n × AnnulusRadius)
            (intersectionPolarHomeomorph a (z,r)) (z,r)).induced) b = _
  rw [← induced_comp]
  rfl


/-- Close the disk calculation from the actual old-open deformation and the
induced equivalence of its radial retraction. -/
theorem attachedDiskQuotientOfOldDeformation [PathConnectedSpace X]
    (hn : 2 ≤ n)
    (H : (ContinuousMap.id (oldOpen a)).Homotopy
      ((oldInclusion a).comp (oldRetraction a)))
    (hR : ∀ y : oldOpen a, Function.Bijective
      (⟨oldRetraction a, rfl⟩ : PointedMap (oldOpen a) X y (oldRetraction a y)).induced)
    (z : Sphere n) (x : X) (d : Path x (a z)) :
    ∃ e : Pi1 X x ⧸ Subgroup.normalClosure (Set.range (attachingHom a z d)) ≃*
        Pi1 (Space a) (inclusion a x),
      ∀ b : Pi1 X x, e (QuotientGroup.mk b) = (pointedInclusion a x).induced b := by
  let r : AnnulusRadius := ⟨3/4, by norm_num⟩
  let yi := intersectionPolarHomeomorph a (z,r)
  let yu : oldOpen a := ⟨yi.val, yi.property.1⟩
  have hbase : oldRetraction a yu = a z := by
    rw [oldRetraction_intersection]
    exact congrArg a (intersectionDirection_param a (z,r))
  let fR : PointedMap (oldOpen a) X yu (a z) := ⟨oldRetraction a, hbase⟩
  let eG : Pi1 (oldOpen a) yu ≃* Pi1 X (a z) :=
    MulEquiv.ofBijective fR.induced
      (pointedInducedBijectiveOfEq (oldRetraction a) yu (a z) hbase (hR yu))
  let eK := intersectionSpherePi1Equiv a z r
  let i := VanKampen.leftMap (oldOpen a) (diskOpen a) yi.val yi.property
  let i' := (pointedAttachingMap a z).induced
  have hc : ∀ b, eG (i b) = i' (eK b) := by
    intro b
    change fR.induced ((VanKampen.subspaceMap Set.inter_subset_left
      yi.val yi.property).induced b) =
      (pointedAttachingMap a z).induced (intersectionSpherePi1Equiv a z r b)
    rw [intersectionSpherePi1Equiv_apply]
    have hm : fR.comp (VanKampen.subspaceMap Set.inter_subset_left yi.val yi.property) =
        (pointedAttachingMap a z).comp
          (⟨intersectionDirection a, intersectionDirection_param a (z,r)⟩ :
            PointedMap ↥(oldOpen a ∩ diskOpen a) (Sphere n) yi z) := by
      apply pointedMap_ext
      ext yy
      exact oldRetraction_intersection a yy
    simpa only [induced_comp, MonoidHom.comp_apply] using
      congrArg (fun k => k.induced b) hm
  let T := quotientNormalClosureRangeEquiv i i' eK eG hc
  obtain ⟨E, hE⟩ := diskCoverQuotient a hn yi.val yi.property
  let q : Path yu (oldInclusion a (a z)) :=
    (H.evalAt yu).cast rfl (congrArg (oldInclusion a) hbase).symm
  let valMap : C(oldOpen a, Space a) := ⟨Subtype.val, continuous_subtype_val⟩
  let delta := q.map valMap.continuous
  have hambient (b : Pi1 (oldOpen a) yu) :
      (VanKampen.ambientMap (oldOpen a) yi.val yi.property.1).induced b =
        changeBasepoint delta ((pointedInclusion a (a z)).induced (eG b)) := by
    let gp : PointedMap (oldOpen a) (oldOpen a) yu (oldInclusion a (a z)) :=
      ⟨(oldInclusion a).comp (oldRetraction a), congrArg (oldInclusion a) hbase⟩
    have hh : b = changeBasepoint q (gp.induced b) := by
      have hh := inducedHomotopyBasepoint (ContinuousMap.id (oldOpen a))
        ((oldInclusion a).comp (oldRetraction a)) H yu yu (oldInclusion a (a z))
        rfl (congrArg (oldInclusion a) hbase) b
      simpa only [show (⟨ContinuousMap.id (oldOpen a), rfl⟩ :
          PointedMap (oldOpen a) (oldOpen a) yu yu) = PointedMap.id yu from rfl,
        induced_id, MonoidHom.id_apply] using hh
    calc
      _ = (⟨valMap,rfl⟩ : PointedMap (oldOpen a) (Space a) yu yi.val).induced
          (changeBasepoint q (gp.induced b)) := congrArg _ hh
      _ = changeBasepoint delta
          ((⟨valMap,rfl⟩ : PointedMap (oldOpen a) (Space a)
            (oldInclusion a (a z)) (inclusion a (a z))).induced (gp.induced b)) :=
        inducedChangeBasepoint valMap q (gp.induced b)
      _ = _ := by
        congr 1
        have hm : (⟨valMap,rfl⟩ : PointedMap (oldOpen a) (Space a)
              (oldInclusion a (a z)) (inclusion a (a z))).comp gp =
            (pointedInclusion a (a z)).comp fR := by
          apply pointedMap_ext
          ext yy
          rfl
        change (⟨valMap,rfl⟩ : PointedMap (oldOpen a) (Space a)
            (oldInclusion a (a z)) (inclusion a (a z))).induced (gp.induced b) =
          (pointedInclusion a (a z)).induced (fR.induced b)
        simpa only [induced_comp, MonoidHom.comp_apply] using
          congrArg (fun k => k.induced b) hm
  let E0 : Pi1 X (a z) ⧸ Subgroup.normalClosure (Set.range i') ≃*
      Pi1 (Space a) (inclusion a (a z)) := T.symm.trans (E.trans (changeBasepoint delta).symm)
  have hE0 (b : Pi1 X (a z)) :
      E0 (QuotientGroup.mk b) = (pointedInclusion a (a z)).induced b := by
    change (changeBasepoint delta).symm
      (E (T.symm (QuotientGroup.mk b))) = _
    rw [quotientNormalClosureRangeEquiv_symm_mk, hE, hambient]
    rw [MulEquiv.symm_apply_apply, eG.apply_symm_apply]
  let Td := quotientNormalClosureRangeEquiv i' (attachingHom a z d)
    (MulEquiv.refl _) (changeBasepoint d) (fun _ => rfl)
  refine ⟨Td.symm.trans (E0.trans (changeBasepoint (d.map (inclusion a).continuous))), ?_⟩
  intro b
  change changeBasepoint (d.map (inclusion a).continuous)
    (E0 (Td.symm (QuotientGroup.mk b))) = _
  rw [quotientNormalClosureRangeEquiv_symm_mk, hE0]
  have hh := inducedChangeBasepoint (inclusion a) d ((changeBasepoint d).symm b)
  simpa only [pointedInclusion, MulEquiv.apply_symm_apply] using hh.symm


theorem attachment_pathConnected [PathConnectedSpace X] (z : Sphere n) :
    PathConnectedSpace (Space a) := by
  have hreach : ∀ y : Space a, Joined y (inclusion a (a z)) := by
    intro y
    induction y using Quotient.inductionOn with
    | h p =>
      cases p with
      | inl x =>
        exact (PathConnectedSpace.joined x (a z)).map (inclusion a).continuous
      | inr p =>
        rw [glue a z]
        letI : PathConnectedSpace (Disk n) :=
          isPathConnected_iff_pathConnectedSpace.mp (Metric.isPathConnected_closedBall (by norm_num))
        exact (PathConnectedSpace.joined p (boundaryInclusion n z)).map
          (characteristic a).continuous
  refine { nonempty := ⟨inclusion a (a z)⟩, joined := ?_ }
  intro y w
  exact (hreach y).trans (hreach w).symm

theorem attachedDiskInducedSurjectiveAndKernel
    [PathConnectedSpace X] (hn : 2 ≤ n) (z : Sphere n) (x : X) (d : Path x (a z)) :
    Function.Surjective (pointedInclusion a x).induced ∧
      (pointedInclusion a x).induced.ker =
        Subgroup.normalClosure (Set.range (attachingHom a z d)) := by
  obtain ⟨e, he⟩ := attachedDiskQuotientOfOldDeformation a hn
    (oldDeformation a) (oldRetraction_induced_bijective a) z x d
  constructor
  · intro b
    obtain ⟨c, rfl⟩ := e.surjective b
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
    exact ⟨c, (he c).symm⟩
  · ext b
    change (pointedInclusion a x).induced b = 1 ↔ _
    rw [← he b, ← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff b


end DiskAttachmentProof

/-- The actual Euclidean one-sphere is the complex unit circle. -/
def euclideanBoundaryCircleHomeomorph : Sphere 2 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype (fun z => by
    rw [Metric.mem_sphere, dist_zero_right]
    change (‖z‖ = 1) ↔
      Complex.orthonormalBasisOneI.repr.symm z ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map])

theorem euclideanBoundaryCircleFundamentalGroup (z : Sphere 2) :
    Nonempty (Pi1 (Sphere 2) z ≃* Multiplicative ℤ) := by
  obtain ⟨η, _⟩ := windingNumber
  let H := euclideanBoundaryCircleHomeomorph
  exact ⟨(pointedHomeomorphEquiv H z (H z) rfl).trans
    ((changeBasepoint (PathConnectedSpace.somePath 1 (H z))).trans η)⟩

/-- A homomorphism from an infinite cyclic group has normally cyclic image. -/
theorem normalClosureRangeOfIntegerEquiv
    {K : Type u} {G : Type v} [Group K] [Group G]
    (η : K ≃* Multiplicative ℤ) (f : K →* G) :
    Subgroup.normalClosure (Set.range f) =
      Subgroup.normalClosure ({f (η.symm (Multiplicative.ofAdd 1))} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨k, rfl⟩
    have hk : (η.symm (Multiplicative.ofAdd 1)) ^ (η k).toAdd = k := by
      apply η.injective
      rw [map_zpow, η.apply_symm_apply, ← Int.ofAdd_mul]
      simp
    rw [← hk, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _)) _
  · apply Subgroup.normalClosure_mono
    intro b hb
    exact ⟨η.symm (Multiplicative.ofAdd 1), hb.symm⟩

/-- Once the geometric quotient calculation is proved, the two-cell formula
follows using the checked circle calculation. This lemma does not supply or
assume a proof certificate for that geometric calculation. -/
theorem attachedTwoCellOfAttachedDiskQuotient
    (hQ : P202Specs.Topology.AttachedCellPresentations.attachedDiskQuotient.{u}) :
    P202Specs.Topology.AttachedCellPresentations.attachedTwoCell.{u} := by
  intro X _ _ a z
  obtain ⟨η⟩ := euclideanBoundaryCircleFundamentalGroup z
  refine ⟨η, fun x d => ?_⟩
  obtain ⟨e, he⟩ := hQ 2 (by omega) a z x d
  let hn := normalClosureRangeOfIntegerEquiv η (DiskAttachment.attachingHom a z d)
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hn.symm).trans e, fun b => ?_⟩
  simpa only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk] using he b

theorem attachedHigherCellOfAttachedDiskQuotient
    (hQ : P202Specs.Topology.AttachedCellPresentations.attachedDiskQuotient.{u}) :
    P202Specs.Topology.AttachedCellPresentations.attachedHigherCell.{u} := by
  intro X _ _ n hn a x
  have hs : SimplyConnectedSpace (Sphere n) := by
    cases n with
    | zero => omega
    | succ m => exact (spheresSimplyConnected m (by omega)).2
  letI := hs
  obtain ⟨z⟩ := (inferInstance : Nonempty (Sphere n))
  let d := PathConnectedSpace.somePath x (a z)
  obtain ⟨e, he⟩ := hQ n (by omega) a z x d
  have hN : Subgroup.normalClosure (Set.range (DiskAttachment.attachingHom a z d)) = ⊥ := by
    apply Subgroup.normalClosure_eq_bot_iff.mpr
    rintro _ ⟨b, rfl⟩
    have hb : b = 1 := Subsingleton.elim _ _
    simp [hb]
  refine ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hN.symm)).trans e, fun b => ?_⟩
  simpa only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientBot_symm_apply] using he b

/-- The disk-attachment theorem, retained as a conditional draft under the
full ordered graph premise required by this task. -/
theorem attachedDiskQuotient_conditional
    (_graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u}) :
    P202Specs.Topology.AttachedCellPresentations.attachedDiskQuotient.{u} := by
  intro X _ _ n hn a z x d
  exact DiskAttachmentProof.attachedDiskQuotientOfOldDeformation a hn
    (DiskAttachmentProof.oldDeformation a)
    (DiskAttachmentProof.oldRetraction_induced_bijective a) z x d

theorem attachedTwoCell_conditional
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u}) :
    P202Specs.Topology.AttachedCellPresentations.attachedTwoCell.{u} :=
  attachedTwoCellOfAttachedDiskQuotient (attachedDiskQuotient_conditional graph)

theorem attachedHigherCell_conditional
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u}) :
    P202Specs.Topology.AttachedCellPresentations.attachedHigherCell.{u} :=
  attachedHigherCellOfAttachedDiskQuotient (attachedDiskQuotient_conditional graph)

namespace OneSkeletonGraph
set_option backward.isDefEq.respectTransparency false
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

local instance cw : CWStructure (OneSkeleton X) := skeletalCWStructure 2

def vertexEquiv : GraphVertex (OneSkeleton X) ≃ GraphVertex X where
  toFun v := ⟨v.val.val, by
    have hv := v.property
    change v.val ∈ skeletonLT (skeletonLT X 2) 1 at hv
    rw [skeletal_skeletonLT] at hv
    exact hv⟩
  invFun v := ⟨vertexInOneSkeleton v, by
    change vertexInOneSkeleton v ∈ skeletonLT (skeletonLT X 2) 1
    rw [skeletal_skeletonLT]
    exact v.property⟩
  left_inv v := rfl
  right_inv v := rfl

def edgeEquiv : Cell X 1 ≃ Cell (OneSkeleton X) 1 where
  toFun e := ⟨e, by decide⟩
  invFun e := e.val
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem vertexEquiv_endpoint (e : Cell (OneSkeleton X) 1) (b : Bool) :
    vertexEquiv (graphEndpoint e b) = graphEndpoint e.val b := rfl

@[simp] theorem vertexEquiv_source (e : Cell (OneSkeleton X) 1) :
    vertexEquiv ((graphEndpoints (OneSkeleton X)).source e) =
      (graphEndpoints X).source e.val := rfl

@[simp] theorem vertexEquiv_target (e : Cell (OneSkeleton X) 1) :
    vertexEquiv ((graphEndpoints (OneSkeleton X)).target e) =
      (graphEndpoints X).target e.val := rfl

@[simp] theorem vertexInOneSkeleton_vertexEquiv (v : GraphVertex (OneSkeleton X)) :
    vertexInOneSkeleton (vertexEquiv v) = v.val := rfl

@[simp] theorem graphEdgePath_edgeEquiv (e : Cell X 1) :
    graphEdgePath (edgeEquiv e) = edgeInOneSkeleton e := rfl


def ambientTree (T : Set (Cell (OneSkeleton X) 1)) : Set (Cell X 1) :=
  edgeEquiv ⁻¹' T

def supportIso (T : Set (Cell (OneSkeleton X) 1)) :
    (graphEndpoints (OneSkeleton X)).support T ≃g
      (graphEndpoints X).support (ambientTree T) where
  toEquiv := vertexEquiv
  map_rel_iff' := by
    intro a b
    constructor
    · rintro ⟨hne, e, he, hor⟩
      refine ⟨fun h => hne (congrArg vertexEquiv h), edgeEquiv e, he, ?_⟩
      rcases hor with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨vertexEquiv.injective hs, vertexEquiv.injective ht⟩
      · exact Or.inr ⟨vertexEquiv.injective hs, vertexEquiv.injective ht⟩
    · rintro ⟨hne, e, he, hor⟩
      refine ⟨fun h => hne (vertexEquiv.injective h), e.val, he, ?_⟩
      rcases hor with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨congrArg vertexEquiv hs, congrArg vertexEquiv ht⟩
      · exact Or.inr ⟨congrArg vertexEquiv hs, congrArg vertexEquiv ht⟩

theorem forest_iff (T : Set (Cell (OneSkeleton X) 1)) :
    (graphEndpoints (OneSkeleton X)).IsForest T ↔
      (graphEndpoints X).IsForest (ambientTree T) := by
  constructor
  · rintro ⟨hnoloop, hinj, hacyc⟩
    refine ⟨?_, ?_, (supportIso T).isAcyclic_iff.mp hacyc⟩
    · intro e he h
      exact hnoloop (edgeEquiv e) he (vertexEquiv.injective h)
    · intro e he f hf h
      apply edgeEquiv.injective
      apply hinj he hf
      rcases Sym2.eq_iff.mp h with h | h
      · exact Sym2.eq_iff.mpr (Or.inl
          ⟨vertexEquiv.injective h.1, vertexEquiv.injective h.2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr
          ⟨vertexEquiv.injective h.1, vertexEquiv.injective h.2⟩)
  · rintro ⟨hnoloop, hinj, hacyc⟩
    refine ⟨?_, ?_, (supportIso T).isAcyclic_iff.mpr hacyc⟩
    · intro e he h
      exact hnoloop e.val he (congrArg vertexEquiv h)
    · intro e he f hf h
      apply Subtype.ext
      apply hinj he hf
      rcases Sym2.eq_iff.mp h with h | h
      · exact Sym2.eq_iff.mpr (Or.inl
          ⟨congrArg vertexEquiv h.1, congrArg vertexEquiv h.2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr
          ⟨congrArg vertexEquiv h.1, congrArg vertexEquiv h.2⟩)

theorem spanning (T : Set (Cell (OneSkeleton X) 1))
    (hT : (graphEndpoints (OneSkeleton X)).IsSpanningTree T) :
    (graphEndpoints X).IsSpanningTree (ambientTree T) :=
  ⟨(forest_iff T).mp hT.1, (supportIso T).connected_iff.mp hT.2⟩

theorem maximal (T : Set (Cell (OneSkeleton X) 1))
    (hT : Maximal (graphEndpoints (OneSkeleton X)).IsForest T) :
    Maximal (graphEndpoints X).IsForest (ambientTree T) := by
  refine ⟨(forest_iff T).mp hT.1, ?_⟩
  intro U hU hTU e he
  let U' : Set (Cell (OneSkeleton X) 1) := {e | e.val ∈ U}
  have hU' : (graphEndpoints (OneSkeleton X)).IsForest U' :=
    (forest_iff U').mpr hU
  have hTU' : T ⊆ U' := fun e he => hTU he
  exact hT.2 hU' hTU' he


def complementEquiv (T : Set (Cell (OneSkeleton X) 1)) :
    {e : Cell X 1 // e ∉ ambientTree T} ≃
      {e : Cell (OneSkeleton X) 1 // e ∉ T} where
  toFun e := ⟨edgeEquiv e.val, e.property⟩
  invFun e := ⟨e.val.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrier_iff (T : Set (Cell (OneSkeleton X) 1)) (y : OneSkeleton X) :
    y ∈ graphTreeCarrier T ↔ y.val ∈ graphTreeCarrier (ambientTree T) := by
  change (y ∈ skeletonLT (skeletonLT X 2) 1 ∨
      y ∈ ⋃ e ∈ T, openCell (skeletonLT X 2) 1 e) ↔ _
  rw [skeletal_skeletonLT]
  constructor
  · rintro (hy | hy)
    · exact Or.inl hy
    · obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
      exact Or.inr (mem_iUnion₂.mpr ⟨e.val, he, by rwa [skeletal_openCell] at hy⟩)
  · rintro (hy | hy)
    · exact Or.inl hy
    · obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
      exact Or.inr (mem_iUnion₂.mpr ⟨edgeEquiv e, he, by rwa [skeletal_openCell]⟩)

theorem presentation
    (hgraph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u})
    [Finite (Σ n, Cell X n)] [ConnectedSpace X] (x : X) :
    Nonempty (OneSkeletonPresentation X x) := by
  letI := finiteCW_oneSkeleton_connected (X := X)
  letI := cw_pathConnectedSpace (X := X)
  letI := cw_pathConnectedSpace (X := OneSkeleton X)
  obtain ⟨y⟩ := (inferInstance : Nonempty (OneSkeleton X))
  obtain ⟨T, hspan, hmax, r, d, p, hp, Φ, hΦ⟩ :=
    hgraph (X := OneSkeleton X) oneSkeleton_isGraph inferInstance y
  let E := complementEquiv T
  let Φ' := (FreeGroup.freeGroupCongr E).trans (Φ.trans (changeBasepoint d).symm)
  let z : Sphere 2 := ⟨EuclideanSpace.single 0 1, by
    norm_num [Metric.mem_sphere, dist_zero_right]⟩
  obtain ⟨η⟩ := euclideanBoundaryCircleFundamentalGroup z
  refine ⟨{
    connected := inferInstance
    tree := ambientTree T
    spanning := spanning T hspan
    maximal := maximal T hmax
    root := vertexEquiv r
    basepath := PathConnectedSpace.somePath x (vertexEquiv r).val
    paths := fun v => p (vertexEquiv.symm v)
    paths_in_tree := fun v t => (carrier_iff T _).mp (hp (vertexEquiv.symm v) t)
    freeEquiv := Φ'
    on_edge := ?_
    sphereBasepoint := z
    sphereEquiv := η
    cellPaths := fun c => PathConnectedSpace.somePath _ _ }⟩
  intro e
  change (changeBasepoint d).symm
    (Φ ((FreeGroup.freeGroupCongr E) (FreeGroup.of e))) = _
  apply (changeBasepoint d).injective
  rw [MulEquiv.apply_symm_apply]
  change Φ (FreeGroup.of (E e)) = _
  rw [hΦ]
  apply pathClass_injective
  simp only [changeBasepoint_pathClass, pathClass_loopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rfl

end OneSkeletonGraph

open private disk_cases from MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
namespace PartialSkeletonAttachment
variable {X : Type u} [TopologicalSpace X] [CWStructure X]
local instance cellDecidableEq (n : ℕ) : DecidableEq (Cell X n) := Classical.decEq _

def carrier (n : ℕ) (S : Finset (Cell X n)) : Set X :=
  skeletonLT X n ∪ ⋃ c ∈ S, openCell X n c

theorem closedCell_subset (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n)
    (hc : c ∈ S) : closedCell X n c ⊆ carrier n S := by
  rintro x ⟨z, rfl⟩
  rcases disk_cases n z with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inr (mem_iUnion₂.mpr ⟨c, hc, ⟨z, rfl⟩⟩)
  · exact Or.inl (CWStructure.boundary_lands n c (mem_univ z))

theorem skeleton_compact [Finite (Σ n, Cell X n)] (n : ℕ) :
    IsCompact (skeletonLT X n) := by
  have heq : skeletonLT X n =
      ⋃ d : {d : Σ m, Cell X m // d.1 < n}, closedCell X d.val.1 d.val.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm, c, z, rfl⟩ := by
        simpa only [skeletonLT, mem_iUnion, openCell, mem_range] using hx
      exact mem_iUnion.mpr ⟨⟨⟨m, c⟩, hm⟩, interiorInclusion m z, rfl⟩
    · intro hx
      obtain ⟨d, z, rfl⟩ := mem_iUnion.mp hx
      exact skeletonLT_mono (Nat.succ_le_of_lt d.property)
        (diskToSkeleton X CWStructure.boundary_lands d.val.1 d.val.2 z).property
  rw [heq]
  apply isCompact_iUnion
  intro d
  letI : CompactSpace (Disk d.val.1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact isCompact_range (characteristic X d.val.1 d.val.2).continuous

theorem compact [Finite (Σ n, Cell X n)] (n : ℕ) (S : Finset (Cell X n)) :
    IsCompact (carrier n S) := by
  have heq : carrier n S = skeletonLT X n ∪ ⋃ c ∈ S, closedCell X n c := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact Or.inl hx
      · obtain ⟨c, hc, z, rfl⟩ := mem_iUnion₂.mp hx
        exact Or.inr (mem_iUnion₂.mpr ⟨c, hc, interiorInclusion n z, rfl⟩)
    · rintro x (hx | hx)
      · exact Or.inl hx
      · obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp hx
        exact closedCell_subset n S c hc hx
  rw [heq]
  apply (skeleton_compact n).union
  apply S.finite_toSet.isCompact_biUnion
  intro c hc
  letI : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact isCompact_range (characteristic X n c).continuous

theorem mono {n : ℕ} {S T : Finset (Cell X n)} (hST : S ⊆ T) :
    carrier n S ⊆ carrier n T := by
  rintro x (hx | hx)
  · exact Or.inl hx
  · obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨c, hST hc, hx⟩)

def attachingMap (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n) :
    C(Sphere n, carrier n S) :=
  ⟨fun z => ⟨boundaryMap X n c z, Or.inl (CWStructure.boundary_lands n c (mem_univ z))⟩,
    ((characteristic X n c).continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

def oldInclusion (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n) :
    C(carrier n S, carrier n (insert c S)) :=
  ⟨fun x => ⟨x.val, mono (Finset.subset_insert c S) x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def newCharacteristic (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n) :
    C(Disk n, carrier n (insert c S)) :=
  ⟨fun z => ⟨characteristic X n c z,
      closedCell_subset n (insert c S) c (Finset.mem_insert_self _ _) ⟨z, rfl⟩⟩,
    (characteristic X n c).continuous.subtype_mk _⟩

def adjunctionMap (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n) :
    C(DiskAttachment.Space (attachingMap n S c), carrier n (insert c S)) :=
  DiskAttachmentProof.descend _ (oldInclusion n S c) (newCharacteristic n S c)
    (fun _ => rfl)

theorem disjoint_new (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n) (hc : c ∉ S) :
    Disjoint (openCell X n c) (carrier n S) := by
  refine disjoint_union_right.mpr ⟨openCellDisjointSkeletonLT n c, ?_⟩
  apply disjoint_iUnion_right.mpr
  intro d
  apply disjoint_iUnion_right.mpr
  intro hd
  apply CWStructure.disjoint_interiors (mem_univ ⟨n, c⟩) (mem_univ ⟨n, d⟩)
  intro heq
  have hcd : c = d := by simpa using heq
  exact hc (hcd ▸ hd)


def normalInsertion (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n) :
    (carrier n S ⊕ OpenDisk n) → carrier n (insert c S) :=
  Sum.elim (oldInclusion n S c)
    (fun z => newCharacteristic n S c (interiorInclusion n z))

theorem normalInsertion_injective (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n)
    (hc : c ∉ S) : Function.Injective (normalInsertion n S c) := by
  intro p q hpq
  have hpq' := congrArg Subtype.val hpq
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (Subtype.ext hpq')
    | inr q =>
      exact False.elim (Set.disjoint_left.mp (disjoint_new n S c hc)
        ⟨q, hpq'.symm⟩ p.property)
  | inr p =>
    cases q with
    | inl q =>
      exact False.elim (Set.disjoint_left.mp (disjoint_new n S c hc)
        ⟨p, hpq'⟩ q.property)
    | inr q =>
      exact congrArg Sum.inr ((CWStructure.interior_embedding n c).injective hpq')

theorem normalInsertion_surjective (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n) :
    Function.Surjective (normalInsertion n S c) := by
  intro y
  rcases y.property with hy | hy
  · exact ⟨Sum.inl ⟨y.val, Or.inl hy⟩, rfl⟩
  · obtain ⟨d, hd, hy⟩ := mem_iUnion₂.mp hy
    rcases Finset.mem_insert.mp hd with rfl | hd
    · obtain ⟨z, hz⟩ := hy
      exact ⟨Sum.inr z, Subtype.ext hz⟩
    · exact ⟨Sum.inl ⟨y.val, Or.inr (mem_iUnion₂.mpr ⟨d, hd, hy⟩)⟩, rfl⟩

theorem adjunctionMap_insertNormalForm (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n)
    (p : carrier n S ⊕ OpenDisk n) :
    adjunctionMap n S c (DiskAttachmentProof.insertNormalForm (attachingMap n S c) p) =
      normalInsertion n S c p := by
  cases p <;> rfl

theorem adjunctionMap_bijective (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n)
    (hc : c ∉ S) : Function.Bijective (adjunctionMap n S c) := by
  constructor
  · intro p q hpq
    apply (DiskAttachmentProof.normalFormEquiv (attachingMap n S c)).injective
    apply normalInsertion_injective n S c hc
    change normalInsertion n S c (DiskAttachmentProof.normalForm (attachingMap n S c) p) =
      normalInsertion n S c (DiskAttachmentProof.normalForm (attachingMap n S c) q)
    rw [← adjunctionMap_insertNormalForm, ← adjunctionMap_insertNormalForm,
      DiskAttachmentProof.insertNormalForm_normalForm,
      DiskAttachmentProof.insertNormalForm_normalForm]
    exact hpq
  · intro y
    obtain ⟨p, hp⟩ := normalInsertion_surjective n S c y
    exact ⟨DiskAttachmentProof.insertNormalForm (attachingMap n S c) p,
      (adjunctionMap_insertNormalForm n S c p).trans hp⟩

/-- Adding one new cell to an actual finite partial skeleton is exactly the
canonical topological disk adjunction. -/
def adjunctionHomeomorph [Finite (Σ n, Cell X n)] (n : ℕ)
    (S : Finset (Cell X n)) (c : Cell X n) (hc : c ∉ S) :
    DiskAttachment.Space (attachingMap n S c) ≃ₜ carrier n (insert c S) := by
  letI : CompactSpace (carrier n S) := isCompact_iff_compactSpace.mp (compact n S)
  letI : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  letI : CompactSpace (DiskAttachment.Space (attachingMap n S c)) :=
    @Quotient.compactSpace _ _ (DiskAttachment.setoid (attachingMap n S c)) inferInstance
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (adjunctionMap n S c) (adjunctionMap_bijective n S c hc))
    (adjunctionMap n S c).continuous

@[simp] theorem adjunctionHomeomorph_inclusion [Finite (Σ n, Cell X n)] (n : ℕ)
    (S : Finset (Cell X n)) (c : Cell X n) (hc : c ∉ S) (x : carrier n S) :
    adjunctionHomeomorph n S c hc (DiskAttachment.inclusion (attachingMap n S c) x) =
      oldInclusion n S c x := rfl

@[simp] theorem adjunctionHomeomorph_characteristic [Finite (Σ n, Cell X n)] (n : ℕ)
    (S : Finset (Cell X n)) (c : Cell X n) (hc : c ∉ S) (z : Disk n) :
    adjunctionHomeomorph n S c hc (DiskAttachment.characteristic (attachingMap n S c) z) =
      newCharacteristic n S c z := rfl

attribute [local instance] cellDecidableEq

def pointedOldInclusion (n : ℕ) (S : Finset (Cell X n)) (c : Cell X n)
    (x : carrier n S) : PointedMap (carrier n S) (carrier n (insert c S))
      x (oldInclusion n S c x) := ⟨oldInclusion n S c, rfl⟩

theorem insert_pathConnected [Finite (Σ n, Cell X n)] (n : ℕ)
    (S : Finset (Cell X n)) (c : Cell X n) (hc : c ∉ S)
    [PathConnectedSpace (carrier n S)] (z : Sphere n) :
    PathConnectedSpace (carrier n (insert c S)) := by
  letI := DiskAttachmentProof.attachment_pathConnected (attachingMap n S c) z
  exact (adjunctionHomeomorph n S c hc).surjective.pathConnectedSpace
    (adjunctionHomeomorph n S c hc).continuous

theorem pathConnected [Finite (Σ n, Cell X n)] (n : ℕ) (S : Finset (Cell X n))
    [PathConnectedSpace (skeletonLT X n)] (z : Sphere n) :
    PathConnectedSpace (carrier n S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have heq : carrier n (∅ : Finset (Cell X n)) = skeletonLT X n := by simp [carrier]
    exact (Homeomorph.setCongr heq.symm).surjective.pathConnectedSpace
      (Homeomorph.setCongr heq.symm).continuous
  | @insert c S hc ih =>
    letI := ih
    exact insert_pathConnected n S c hc z

/-- The actual partial-skeleton inclusion is the single-disk quotient map on
fundamental groups, with the exact attaching-sphere normal kernel. -/
theorem induced_surjective_and_kernel [Finite (Σ n, Cell X n)]
    (n : ℕ) (hn : 2 ≤ n) (S : Finset (Cell X n))
    (c : Cell X n) (hc : c ∉ S) [PathConnectedSpace (carrier n S)]
    (z : Sphere n) (x : carrier n S) (d : Path x (attachingMap n S c z)) :
    Function.Surjective (pointedOldInclusion n S c x).induced ∧
      (pointedOldInclusion n S c x).induced.ker =
        Subgroup.normalClosure (Set.range (DiskAttachment.attachingHom (attachingMap n S c) z d)) := by
  let a := attachingMap n S c
  let H := adjunctionHomeomorph n S c hc
  let x' := DiskAttachment.inclusion a x
  let hbase : H x' = oldInclusion n S c x := rfl
  let E := pointedHomeomorphEquiv H x' (oldInclusion n S c x) hbase
  let F : PointedMap (DiskAttachment.Space a) (carrier n (insert c S)) x'
      (oldInclusion n S c x) := ⟨⟨H, H.continuous⟩, hbase⟩
  have hcomp : (pointedOldInclusion n S c x).induced =
      E.toMonoidHom.comp (DiskAttachment.pointedInclusion a x).induced := by
    change (pointedOldInclusion n S c x).induced =
      F.induced.comp (DiskAttachment.pointedInclusion a x).induced
    rw [← induced_comp]
    rfl
  obtain ⟨hsur, hker⟩ := DiskAttachmentProof.attachedDiskInducedSurjectiveAndKernel
    a hn z x d
  constructor
  · rw [hcomp]
    exact E.surjective.comp hsur
  · ext b
    change (pointedOldInclusion n S c x).induced b = 1 ↔ _
    rw [hcomp, MonoidHom.comp_apply, ← E.map_one]
    change E ((DiskAttachment.pointedInclusion a x).induced b) = E 1 ↔ _
    rw [E.injective.eq_iff]
    change b ∈ (DiskAttachment.pointedInclusion a x).induced.ker ↔ _
    rw [hker]


end PartialSkeletonAttachment

namespace PartialSkeletonAttachment
variable {X : Type u} [TopologicalSpace X] [CWStructure X] {x : X}

def oneSkeletonInclusion (S : Finset (Cell X 2)) : C(OneSkeleton X, carrier 2 S) :=
  ⟨fun y => ⟨y.val, Or.inl y.property⟩, continuous_subtype_val.subtype_mk _⟩

def twoCellBasepath (D : OneSkeletonPresentation X x) (S : Finset (Cell X 2)) (c : Cell X 2) :
    Path (oneSkeletonInclusion S (vertexInOneSkeleton D.root))
      (attachingMap 2 S c D.sphereBasepoint) :=
  (D.cellPaths c).map (oneSkeletonInclusion S).continuous

def freeHom (D : OneSkeletonPresentation X x) (S : Finset (Cell X 2)) :
    FreeGroup {e : Cell X 1 // e ∉ D.tree} →*
      Pi1 (carrier 2 S) (oneSkeletonInclusion S (vertexInOneSkeleton D.root)) :=
  (⟨oneSkeletonInclusion S, rfl⟩ : PointedMap (OneSkeleton X) (carrier 2 S)
    (vertexInOneSkeleton D.root) _).induced.comp D.freeEquiv.toMonoidHom

theorem freeHom_relator (D : OneSkeletonPresentation X x) (S : Finset (Cell X 2))
    (c : Cell X 2) :
    freeHom D S (D.relator c) =
      DiskAttachment.attachingHom (attachingMap 2 S c) D.sphereBasepoint
        (twoCellBasepath D S c) (D.sphereEquiv.symm (Multiplicative.ofAdd 1)) := by
  change (⟨oneSkeletonInclusion S, rfl⟩ : PointedMap (OneSkeleton X) (carrier 2 S)
    (vertexInOneSkeleton D.root) _).induced (D.freeEquiv (D.relator c)) = _
  dsimp only [OneSkeletonPresentation.relator]
  rw [D.freeEquiv.apply_symm_apply, inducedChangeBasepoint]
  change changeBasepoint ((D.cellPaths c).map (oneSkeletonInclusion S).continuous)
      ((⟨oneSkeletonInclusion S, rfl⟩ : PointedMap (OneSkeleton X) (carrier 2 S)
        (P202.Cellular.attachingMap 2 c D.sphereBasepoint) _).induced
        ((⟨P202.Cellular.attachingMap 2 c, rfl⟩ : PointedMap (Sphere 2) (OneSkeleton X)
          D.sphereBasepoint _).induced (D.sphereEquiv.symm (Multiplicative.ofAdd 1)))) =
    changeBasepoint ((D.cellPaths c).map (oneSkeletonInclusion S).continuous)
      ((DiskAttachment.pointedAttachingMap (attachingMap 2 S c) D.sphereBasepoint).induced
        (D.sphereEquiv.symm (Multiplicative.ofAdd 1)))
  apply congrArg (changeBasepoint ((D.cellPaths c).map (oneSkeletonInclusion S).continuous))
  have he : (⟨oneSkeletonInclusion S, rfl⟩ :
      PointedMap (OneSkeleton X) (carrier 2 S)
        (P202.Cellular.attachingMap 2 c D.sphereBasepoint)
        (attachingMap 2 S c D.sphereBasepoint)).comp
      (⟨P202.Cellular.attachingMap 2 c, rfl⟩ :
        PointedMap (Sphere 2) (OneSkeleton X) D.sphereBasepoint
          (P202.Cellular.attachingMap 2 c D.sphereBasepoint)) =
      DiskAttachment.pointedAttachingMap (attachingMap 2 S c) D.sphereBasepoint := by
    apply pointedMap_ext
    rfl
  have hh := congrArg (fun k => k.induced (D.sphereEquiv.symm (Multiplicative.ofAdd 1))) he
  rw [induced_comp] at hh
  exact hh

end PartialSkeletonAttachment

namespace PartialSkeletonAttachment
variable {X : Type u} [TopologicalSpace X] [CWStructure X] {x : X}
attribute [local instance] cellDecidableEq

theorem freeHom_empty_bijective (D : OneSkeletonPresentation X x) :
    Function.Bijective (freeHom D ∅) := by
  have he : OneSkeleton X = carrier 2 (∅ : Finset (Cell X 2)) := by
    simp [carrier, OneSkeleton]
  let H := Homeomorph.setCongr he
  let E := D.freeEquiv.trans (pointedHomeomorphEquiv H
    (vertexInOneSkeleton D.root) (oneSkeletonInclusion ∅ (vertexInOneSkeleton D.root)) rfl)
  have hf : (E : FreeGroup {e : Cell X 1 // e ∉ D.tree} →
      Pi1 (carrier 2 ∅) (oneSkeletonInclusion ∅ (vertexInOneSkeleton D.root))) = freeHom D ∅ := by
    funext b
    rfl
  rw [← hf]
  exact E.bijective

theorem freeHom_insert (D : OneSkeletonPresentation X x) (S : Finset (Cell X 2))
    (c : Cell X 2) :
    (pointedOldInclusion 2 S c (oneSkeletonInclusion S (vertexInOneSkeleton D.root))).induced.comp
      (freeHom D S) = freeHom D (insert c S) := by
  apply MonoidHom.ext
  intro b
  change (pointedOldInclusion 2 S c (oneSkeletonInclusion S (vertexInOneSkeleton D.root))).induced
    ((⟨oneSkeletonInclusion S, rfl⟩ : PointedMap (OneSkeleton X) (carrier 2 S)
      (vertexInOneSkeleton D.root) _).induced (D.freeEquiv b)) = _
  rw [← MonoidHom.comp_apply, ← induced_comp]
  rfl

/-- The two-skeleton calculation on every finite partial collection of actual
cells. Each newly adjoined cell contributes precisely its specified relator. -/
theorem freeHom_surjective_and_kernel [Finite (Σ n, Cell X n)]
    (D : OneSkeletonPresentation X x) (S : Finset (Cell X 2)) :
    Function.Surjective (freeHom D S) ∧
      (freeHom D S).ker = Subgroup.normalClosure (D.relator '' (S : Set (Cell X 2))) := by
  classical
  letI := skeletalCWStructure (X := X) 2
  letI : ConnectedSpace (OneSkeleton X) := D.connected
  letI : PathConnectedSpace (OneSkeleton X) := cw_pathConnectedSpace
  induction S using Finset.induction_on with
  | empty =>
    have hb := freeHom_empty_bijective D
    refine ⟨hb.2, ?_⟩
    rw [(freeHom D ∅).ker_eq_bot hb.1]
    simp
  | @insert c S hc ih =>
    letI := pathConnected 2 S D.sphereBasepoint
    let root := oneSkeletonInclusion S (vertexInOneSkeleton D.root)
    let f := freeHom D S
    let g := (pointedOldInclusion 2 S c root).induced
    obtain ⟨hgs, hgk⟩ := induced_surjective_and_kernel 2 (by omega) S c hc
      D.sphereBasepoint root (twoCellBasepath D S c)
    have hgk' : g.ker = Subgroup.normalClosure (f '' ({D.relator c} : Set _)) := by
      rw [hgk, normalClosureRangeOfIntegerEquiv D.sphereEquiv,
        ← freeHom_relator D S c]
      simp only [Set.image_singleton]
      rfl
    have hcomp : g.comp f = freeHom D (insert c S) := freeHom_insert D S c
    constructor
    · rw [← hcomp]
      exact hgs.comp ih.1
    · rw [← hcomp]
      have hk := kernelNormalClosure_comp f g ih.1
        (D.relator '' (S : Set (Cell X 2))) ({D.relator c} : Set _) ih.2 hgk'
      rw [hk]
      congr 1
      ext a
      simp [Finset.coe_insert, Set.image_insert_eq, Set.union_comm]

end PartialSkeletonAttachment

namespace PartialSkeletonAttachment
variable {X : Type u} [TopologicalSpace X] [CWStructure X]
attribute [local instance] cellDecidableEq

local instance finiteCells [Finite (Σ n, Cell X n)] (n : ℕ) : Finite (Cell X n) :=
  Finite.of_injective (fun c => (⟨n, c⟩ : Σ n, Cell X n)) (by
    intro c d h; simpa using h)

def allCells [Finite (Σ n, Cell X n)] (n : ℕ) : Finset (Cell X n) :=
  @Finset.univ _ (Fintype.ofFinite _)

@[simp] theorem mem_allCells [Finite (Σ n, Cell X n)] (n : ℕ) (c : Cell X n) :
    c ∈ allCells n := @Finset.mem_univ _ (Fintype.ofFinite _) c

theorem carrier_allCells [Finite (Σ n, Cell X n)] (n : ℕ) :
    carrier n (allCells n : Finset (Cell X n)) = skeletonLT X (n + 1) := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact skeletonLT_mono (Nat.le_succ n) hx
    · obtain ⟨c, _, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Nat.lt_succ_self n, mem_iUnion.mpr ⟨c, hx⟩⟩⟩
  · intro hx
    obtain ⟨m, hm, c, hc⟩ := by simpa only [skeletonLT, mem_iUnion] using hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hmn | rfl
    · exact Or.inl (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn, mem_iUnion.mpr ⟨c, hc⟩⟩⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨c, mem_allCells _ c, hc⟩)

def spherePoint (n : ℕ) (hn : 0 < n) : Sphere n :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by norm_num [Metric.mem_sphere, dist_zero_right]⟩

theorem skeleton_pathConnected [Finite (Σ n, Cell X n)] [ConnectedSpace X]
    (n : ℕ) (hn : 2 ≤ n) : PathConnectedSpace (skeletonLT X n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    letI := skeletalCWStructure (X := X) 2
    letI := finiteCW_oneSkeleton_connected (X := X)
    exact cw_pathConnectedSpace (X := OneSkeleton X)
  | succ k ih =>
    letI := ih
    letI := pathConnected (2 + k) (allCells (2 + k) : Finset (Cell X (2 + k)))
      (spherePoint (2 + k) (by omega))
    let H := Homeomorph.setCongr (carrier_allCells (X := X) (2 + k))
    exact H.surjective.pathConnectedSpace H.continuous

/-- Higher cells give bijections on the actual fundamental groups of partial
skeleta, by the already proved single-disk calculation. -/
theorem higher_induced_bijective [Finite (Σ n, Cell X n)]
    (n : ℕ) (hn : 3 ≤ n) (S : Finset (Cell X n))
    (c : Cell X n) (hc : c ∉ S) [PathConnectedSpace (carrier n S)]
    (x : carrier n S) : Function.Bijective (pointedOldInclusion n S c x).induced := by
  have hs : SimplyConnectedSpace (Sphere n) := by
    cases n with
    | zero => omega
    | succ m => exact (spheresSimplyConnected m (by omega)).2
  letI := hs
  obtain ⟨z⟩ := (inferInstance : Nonempty (Sphere n))
  let d := PathConnectedSpace.somePath x (attachingMap n S c z)
  obtain ⟨hsur, hker⟩ := induced_surjective_and_kernel n (by omega) S c hc z x d
  have hN : Subgroup.normalClosure
      (Set.range (DiskAttachment.attachingHom (attachingMap n S c) z d)) = ⊥ := by
    apply Subgroup.normalClosure_eq_bot_iff.mpr
    rintro _ ⟨b, rfl⟩
    have hb : b = 1 := Subsingleton.elim _ _
    simp [hb]
  exact ⟨(MonoidHom.ker_eq_bot_iff _).mp (hker.trans hN), hsur⟩



def skeletonInclusion (n : ℕ) (S : Finset (Cell X n)) :
    C(skeletonLT X n, carrier n S) :=
  ⟨fun x => ⟨x.val, Or.inl x.property⟩, continuous_subtype_val.subtype_mk _⟩

def pointedSkeletonInclusion (n : ℕ) (S : Finset (Cell X n)) (x : skeletonLT X n) :
    PointedMap (skeletonLT X n) (carrier n S) x (skeletonInclusion n S x) :=
  ⟨skeletonInclusion n S, rfl⟩

theorem higher_skeletonInclusion_bijective [Finite (Σ n, Cell X n)]
    (n : ℕ) (hn : 3 ≤ n) (S : Finset (Cell X n))
    [PathConnectedSpace (skeletonLT X n)] (x : skeletonLT X n) :
    Function.Bijective (pointedSkeletonInclusion n S x).induced := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have heq : skeletonLT X n = carrier n (∅ : Finset (Cell X n)) := by simp [carrier]
    let H := Homeomorph.setCongr heq
    exact (pointedHomeomorphEquiv H x (skeletonInclusion n ∅ x) rfl).bijective
  | @insert c S hc ih =>
    letI := pathConnected n S (spherePoint n (by omega))
    have hcomp : (pointedSkeletonInclusion n (insert c S) x).induced =
        (pointedOldInclusion n S c (skeletonInclusion n S x)).induced.comp
          (pointedSkeletonInclusion n S x).induced := by
      rw [← induced_comp]
      rfl
    rw [hcomp]
    exact (higher_induced_bijective n hn S c hc (skeletonInclusion n S x)).comp ih

def skeletonStep (n : ℕ) : C(skeletonLT X n, skeletonLT X (n + 1)) :=
  ⟨oldSkeletonInclusion X n, continuous_subtype_val.subtype_mk _⟩

def pointedSkeletonStep (n : ℕ) (x : skeletonLT X n) :
    PointedMap (skeletonLT X n) (skeletonLT X (n + 1)) x (skeletonStep n x) :=
  ⟨skeletonStep n, rfl⟩

theorem higher_skeletonStep_bijective [Finite (Σ n, Cell X n)]
    (n : ℕ) (hn : 3 ≤ n) [PathConnectedSpace (skeletonLT X n)] (x : skeletonLT X n) :
    Function.Bijective (pointedSkeletonStep n x).induced := by
  let S := allCells (X := X) n
  let H := Homeomorph.setCongr (carrier_allCells (X := X) n)
  let y := skeletonInclusion n S x
  let E := pointedHomeomorphEquiv H y (skeletonStep n x) rfl
  have hcomp : (pointedSkeletonStep n x).induced =
      E.toMonoidHom.comp (pointedSkeletonInclusion n S x).induced := by
    rw [show E.toMonoidHom =
      (⟨⟨H, H.continuous⟩, rfl⟩ : PointedMap _ _ y (skeletonStep n x)).induced from rfl,
      ← induced_comp]
    rfl
  rw [hcomp]
  exact E.bijective.comp (higher_skeletonInclusion_bijective n hn S x)



def boundedSkeletonInclusion (m n : ℕ) (hmn : m ≤ n) :
    C(skeletonLT X m, skeletonLT X n) :=
  ⟨fun x => ⟨x.val, skeletonLT_mono hmn x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def pointedBoundedSkeletonInclusion (m n : ℕ) (hmn : m ≤ n) (x : skeletonLT X m) :
    PointedMap (skeletonLT X m) (skeletonLT X n) x (boundedSkeletonInclusion m n hmn x) :=
  ⟨boundedSkeletonInclusion m n hmn, rfl⟩

theorem higher_boundedSkeletonInclusion_bijective [Finite (Σ n, Cell X n)] [ConnectedSpace X]
    (m k : ℕ) (hm : 3 ≤ m) (x : skeletonLT X m) :
    Function.Bijective
      (pointedBoundedSkeletonInclusion m (m+k) (Nat.le_add_right m k) x).induced := by
  induction k with
  | zero =>
    change Function.Bijective (PointedMap.id x).induced
    rw [induced_id]
    exact Function.bijective_id
  | succ k ih =>
    letI := skeleton_pathConnected (X := X) (m+k) (by omega)
    let y := boundedSkeletonInclusion m (m+k) (Nat.le_add_right m k) x
    have hcomp :
        (pointedBoundedSkeletonInclusion m (m+(k+1)) (Nat.le_add_right m (k+1)) x).induced =
          (pointedSkeletonStep (m+k) y).induced.comp
            (pointedBoundedSkeletonInclusion m (m+k) (Nat.le_add_right m k) x).induced := by
      rw [← induced_comp]
      rfl
    rw [hcomp]
    exact (higher_skeletonStep_bijective (m+k) (by omega) y).comp ih

theorem exists_fullSkeleton [Finite (Σ n, Cell X n)] (N : ℕ) :
    ∃ M, N ≤ M ∧ skeletonLT X M = univ := by
  obtain ⟨B, hB⟩ := (Set.finite_range (fun d : Σ n, Cell X n => d.1)).bddAbove
  refine ⟨B + N + 1, by omega, eq_univ_of_forall ?_⟩
  intro x
  have hx : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
    rw [CWStructure.cover]; trivial
  obtain ⟨n, c, hc⟩ := mem_iUnion₂.mp hx
  have hn : n ≤ B := hB ⟨⟨n, c⟩, rfl⟩
  exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨by omega, mem_iUnion.mpr ⟨c, hc⟩⟩⟩

/-- The actual inclusion of the two-skeleton induces an isomorphism on
fundamental groups of a connected finite CW complex. -/
theorem twoSkeletonAmbient_bijective [Finite (Σ n, Cell X n)] [ConnectedSpace X]
    (x : skeletonLT X 3) :
    Function.Bijective (VanKampen.ambientMap (skeletonLT X 3) x.val x.property).induced := by
  obtain ⟨M, hM, hwhole⟩ := exists_fullSkeleton (X := X) 3
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
  let H := (Homeomorph.setCongr hwhole).trans (Homeomorph.Set.univ X)
  let y := boundedSkeletonInclusion 3 (3+k) (Nat.le_add_right 3 k) x
  let E := pointedHomeomorphEquiv H y x.val rfl
  have hcomp : (VanKampen.ambientMap (skeletonLT X 3) x.val x.property).induced =
      E.toMonoidHom.comp
        (pointedBoundedSkeletonInclusion 3 (3+k) (Nat.le_add_right 3 k) x).induced := by
    rw [show E.toMonoidHom =
      (⟨⟨H, H.continuous⟩, rfl⟩ : PointedMap _ _ y x.val).induced from rfl, ← induced_comp]
    rfl
  rw [hcomp]
  exact E.bijective.comp (higher_boundedSkeletonInclusion_bijective 3 k (by omega) x)

end PartialSkeletonAttachment


open PartialSkeletonAttachment

theorem finiteCWPresentationOfOneSkeletonData
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    [Finite (Σ n, Cell X n)] [ConnectedSpace X] {x : X}
    (D : OneSkeletonPresentation X x) :
    ∃ e : PresentedGroup (Set.range D.relator) ≃* Pi1 X x,
      ∀ j, e (PresentedGroup.of j) = D.ambientGenerator j := by
  let S := allCells (X := X) 2
  let y := oneSkeletonInclusion S (vertexInOneSkeleton D.root)
  let root3 : skeletonLT X 3 :=
    ⟨D.root.val, skeletonLT_mono (show 2 ≤ 3 by decide) (vertexInOneSkeleton D.root).property⟩
  let H := Homeomorph.setCongr (carrier_allCells (X := X) 2)
  let E0 := pointedHomeomorphEquiv H y root3 rfl
  let i3 := VanKampen.ambientMap (skeletonLT X 3) root3.val root3.property
  let E1 := MulEquiv.ofBijective i3.induced (twoSkeletonAmbient_bijective root3)
  let E := E0.trans (E1.trans (changeBasepoint D.basepath))
  let F := E.toMonoidHom.comp (freeHom D S)
  obtain ⟨hsur, hker⟩ := freeHom_surjective_and_kernel D S
  have hrel : D.relator '' (S : Set (Cell X 2)) = Set.range D.relator := by
    ext a
    constructor
    · rintro ⟨c, _, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact ⟨c, mem_allCells 2 c, rfl⟩
  have hFsur : Function.Surjective F := E.surjective.comp hsur
  have hFker : F.ker = Subgroup.normalClosure (Set.range D.relator) := by
    rw [← hrel, ← hker]
    ext b
    change E ((freeHom D S) b) = 1 ↔ (freeHom D S) b = 1
    rw [← E.map_one, E.injective.eq_iff]
  let Q := presentedGroupEquivOfSurjective (Set.range D.relator) F hFsur hFker
  refine ⟨Q, ?_⟩
  intro j
  change F (FreeGroup.of j) = D.ambientGenerator j
  let P : PointedMap (carrier 2 S) (skeletonLT X 3) y root3 := ⟨⟨H, H.continuous⟩, rfl⟩
  let I : PointedMap (OneSkeleton X) (carrier 2 S) (vertexInOneSkeleton D.root) y :=
    ⟨oneSkeletonInclusion S, rfl⟩
  have hmaps : (i3.comp P).comp I =
      VanKampen.ambientMap (skeletonLT X 2) D.root.val (vertexInOneSkeleton D.root).property := by
    apply pointedMap_ext
    ext z
    rfl
  change changeBasepoint D.basepath
      (i3.induced (P.induced (I.induced (D.freeEquiv (FreeGroup.of j))))) = _
  have hh := congrArg (fun k => k.induced (D.freeEquiv (FreeGroup.of j))) hmaps
  simp only [induced_comp, MonoidHom.comp_apply] at hh
  exact congrArg (changeBasepoint D.basepath) hh

/-- The finite CW presentation, retained as a conditional derivation under the
full frozen graph assertion. -/
theorem finiteCWPresentation_conditional
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u}) :
    P202Specs.Topology.AttachedCellPresentations.finiteCWPresentation.{u} := by
  intro X _ _ _ hconnected x
  letI := hconnected
  obtain ⟨D⟩ := OneSkeletonGraph.presentation graph x
  exact ⟨D, finiteCWPresentationOfOneSkeletonData D⟩


open scoped OnePoint


def boundarySpherePoint (s : ℝ) : Sphere 2 :=
  euclideanBoundaryCircleHomeomorph.symm
    (P202Specs.Topology.BasicFundamentalGroups.circleCover s)

@[simp] theorem boundarySpherePoint_disk (s : ℝ) :
    boundaryInclusion 2 (boundarySpherePoint s) = SurfacePolygon.boundaryPoint s := by
  apply Subtype.ext
  rfl

@[simp] theorem boundarySpherePoint_circle (s : ℝ) :
    euclideanBoundaryCircleHomeomorph (boundarySpherePoint s) =
      P202Specs.Topology.BasicFundamentalGroups.circleCover s :=
  euclideanBoundaryCircleHomeomorph.apply_symm_apply _

@[simp] theorem boundarySpherePoint_circle_zero :
    euclideanBoundaryCircleHomeomorph (boundarySpherePoint 0) = 1 := by
  rw [boundarySpherePoint_circle]
  simp [P202Specs.Topology.BasicFundamentalGroups.circleCover]

def boundarySphereLoop : Path (boundarySpherePoint 0) (boundarySpherePoint 0) where
  toFun t := boundarySpherePoint (t : ℝ)
  continuous_toFun := euclideanBoundaryCircleHomeomorph.symm.continuous.comp
    (P202Specs.Topology.BasicFundamentalGroups.circleCover.continuous.comp continuous_subtype_val)
  source' := rfl
  target' := by
    apply euclideanBoundaryCircleHomeomorph.injective
    simp [P202Specs.Topology.BasicFundamentalGroups.circleCover, Circle.exp_two_pi]

theorem boundarySphereLoop_generator :
    ∃ η : Pi1 (Sphere 2) (boundarySpherePoint 0) ≃* Multiplicative ℤ,
      η.symm (Multiplicative.ofAdd 1) = loopClass boundarySphereLoop := by
  obtain ⟨ξ,hξ⟩ := windingNumber
  let H := euclideanBoundaryCircleHomeomorph
  let f : PointedMap (Sphere 2) Circle (boundarySpherePoint 0) 1 :=
    ⟨⟨H,H.continuous⟩,boundarySpherePoint_circle_zero⟩
  let E := pointedHomeomorphEquiv H (boundarySpherePoint 0) 1 boundarySpherePoint_circle_zero
  let p : Path (1 : Circle) 1 :=
    (boundarySphereLoop.map H.continuous).cast boundarySpherePoint_circle_zero.symm
      boundarySpherePoint_circle_zero.symm
  have hvalue : ξ (loopClass p) = Multiplicative.ofAdd 1 := by
    have hp := hξ p ⟨Subtype.val,continuous_subtype_val⟩ (fun t => by
      change P202Specs.Topology.BasicFundamentalGroups.circleCover (t : ℝ) =
        H (boundarySpherePoint (t : ℝ))
      exact (boundarySpherePoint_circle (t : ℝ)).symm) rfl
    apply Multiplicative.toAdd.injective
    change (ξ (loopClass p)).toAdd = 1
    change ((ξ (loopClass p)).toAdd : ℝ) = 1 at hp
    exact_mod_cast hp
  have he : E (loopClass boundarySphereLoop) = loopClass p :=
    inducedFormula (Sphere 2) Circle (boundarySpherePoint 0) 1 f boundarySphereLoop
  refine ⟨E.trans ξ, ?_⟩
  apply (E.trans ξ).injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.trans_apply, he, hvalue]




variable {X : Type u} [TopologicalSpace X] [CWStructure X]

def graphEdgeLoopAtVertex [Subsingleton (GraphVertex X)] (b : GraphVertex X)
    (e : Cell X 1) : Path b.val b.val :=
  (graphEdgePath e).cast (congrArg Subtype.val (Subsingleton.elim b ((graphEndpoints X).source e)))
    (congrArg Subtype.val (Subsingleton.elim b ((graphEndpoints X).target e)))

private theorem whiskeredLoop_eq_edge {x a b : X} (p : Path x a) (e : Path a b)
    (q : Path x b) (ha : x = a) (hb : x = b)
    (hp : p.cast rfl ha = Path.refl x) (hq : q.cast rfl hb = Path.refl x) :
    loopClass ((p.trans e).trans q.symm) = loopClass (e.cast ha hb) := by
  cases ha
  cases hb
  change p = Path.refl x at hp
  change q = Path.refl x at hq
  rw [hp, hq]
  apply pathClass_injective
  change ((Path.Homotopic.Quotient.refl x).trans (Path.Homotopic.Quotient.mk e)).trans
    (Path.Homotopic.Quotient.refl x) = Path.Homotopic.Quotient.mk e
  rw [Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]

/-- On a one-vertex graph all edges are free generators with their actual
characteristic-disk orientation and with no tree paths in their formula. -/
theorem oneVertexGraphFundamentalGroup
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u})
    (hgraph : IsGraph X) [ConnectedSpace X] [Subsingleton (GraphVertex X)]
    (b : GraphVertex X) :
    ∃ Φ : FreeGroup (Cell X 1) ≃* Pi1 X b.val,
      ∀ e : Cell X 1, Φ (FreeGroup.of e) = loopClass (graphEdgeLoopAtVertex b e) := by
  obtain ⟨T, hspan, hmax, r, d, p, hp, Φ, hΦ⟩ := graph hgraph inferInstance b.val
  have hT : T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact hspan.1.1 e he (Subsingleton.elim _ _)
  subst T
  have hr : r = b := Subsingleton.elim _ _
  subst r
  have hpconst (v : GraphVertex X) :
      (p v).cast rfl (congrArg Subtype.val (Subsingleton.elim b v)) = Path.refl b.val := by
    apply Path.ext
    funext t
    have ht : p v t ∈ skeletonLT X 1 := by
      simpa [graphTreeCarrier] using hp v t
    exact congrArg Subtype.val (Subsingleton.elim (⟨p v t, ht⟩ : GraphVertex X) b)
  let E : Cell X 1 ≃ {e : Cell X 1 // e ∉ (∅ : Set (Cell X 1))} :=
    ⟨fun e => ⟨e, by simp⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  let Ψ := (FreeGroup.freeGroupCongr E).trans (Φ.trans (changeBasepoint d).symm)
  refine ⟨Ψ, ?_⟩
  intro e
  change (changeBasepoint d).symm (Φ (FreeGroup.of (E e))) = _
  apply (changeBasepoint d).injective
  rw [MulEquiv.apply_symm_apply, hΦ]
  have hedge := whiskeredLoop_eq_edge
    (p ((graphEndpoints X).source e)) (graphEdgePath e)
    (p ((graphEndpoints X).target e))
    (congrArg Subtype.val (Subsingleton.elim b ((graphEndpoints X).source e)))
    (congrArg Subtype.val (Subsingleton.elim b ((graphEndpoints X).target e)))
    (hpconst _) (hpconst _)
  change loopClass _ = changeBasepoint d (loopClass (graphEdgeLoopAtVertex b e))
  rw [show loopClass (graphEdgeLoopAtVertex b e) = _ from hedge.symm]
  apply pathClass_injective
  simp only [changeBasepoint_pathClass, pathClass_loopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rfl


/-- An explicit once-around attaching word supplies the single relation in a
two-disk adjunction, including the formula on the original generators. -/
theorem presentationOfAttachedTwoDisk
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {E : Type v}
    (a : C(Sphere 2, X)) (x : X) (d : Path x (a (boundarySpherePoint 0)))
    (Φ : FreeGroup E ≃* Pi1 X x) (word : FreeGroup E)
    (hword : Φ word = DiskAttachment.attachingHom a (boundarySpherePoint 0) d
      (loopClass boundarySphereLoop)) :
    ∃ e : PresentedGroup ({word} : Set _) ≃*
        Pi1 (DiskAttachment.Space a) (DiskAttachment.inclusion a x),
      ∀ j : E, e (PresentedGroup.of j) =
        (DiskAttachment.pointedInclusion a x).induced (Φ (FreeGroup.of j)) := by
  obtain ⟨η,hη⟩ := boundarySphereLoop_generator
  let i := DiskAttachment.attachingHom a (boundarySpherePoint 0) d
  obtain ⟨Q,hQ⟩ := DiskAttachmentProof.attachedDiskQuotientOfOldDeformation a (by omega)
    (DiskAttachmentProof.oldDeformation a) (DiskAttachmentProof.oldRetraction_induced_bijective a)
    (boundarySpherePoint 0) x d
  have hN : Subgroup.normalClosure (Set.range i) =
      Subgroup.normalClosure ({Φ word} : Set _) := by
    rw [normalClosureRangeOfIntegerEquiv η, hη]
    rw [← hword]
  let T : PresentedGroup ({word} : Set _) ≃*
      Pi1 X x ⧸ Subgroup.normalClosure (Set.range i) :=
    QuotientGroup.congr (Subgroup.normalClosure ({word} : Set _))
      (Subgroup.normalClosure (Set.range i)) Φ (by
        rw [Subgroup.map_normalClosure _ (Φ : FreeGroup E →* Pi1 X x) Φ.surjective,
          Set.image_singleton]
        exact hN.symm)
  refine ⟨T.trans Q, ?_⟩
  intro j
  change Q (T (QuotientGroup.mk (FreeGroup.of j))) = _
  change Q (QuotientGroup.mk (Φ (FreeGroup.of j))) = _
  exact hQ _


namespace UniverseLift
variable {X : Type} [TopologicalSpace X] [CWStructure X]

@[instance_reducible] def cellStructure : CellStructure (ULift.{u} X) where
  Cell n := ULift.{u} (Cell X n)
  characteristic n c :=
    ⟨fun z => ULift.up (characteristic X n c.down z),
      continuous_uliftUp.comp (characteristic X n c.down).continuous⟩

theorem openCell_eq (n : ℕ) (c : ULift.{u} (Cell X n)) :
    letI := cellStructure.{u} (X := X)
    openCell (ULift.{u} X) n c = ULift.down ⁻¹' openCell X n c.down := by
  letI := cellStructure.{u} (X := X)
  ext y
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg ULift.down hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, ULift.ext hz⟩

theorem skeletonLT_eq (n : ℕ) :
    letI := cellStructure.{u} (X := X)
    skeletonLT (ULift.{u} X) n = ULift.down ⁻¹' skeletonLT X n := by
  letI := cellStructure.{u} (X := X)
  ext y
  constructor
  · intro hy
    obtain ⟨m, hm, c, hc⟩ := by simpa only [skeletonLT, mem_iUnion] using hy
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hm, mem_iUnion.mpr
      ⟨c.down, by rwa [openCell_eq] at hc⟩⟩⟩
  · intro hy
    change y.down ∈ skeletonLT X n at hy
    obtain ⟨m, hm, c, hc⟩ := by simpa only [skeletonLT, mem_iUnion] using hy
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hm, mem_iUnion.mpr
      ⟨ULift.up c, by rwa [openCell_eq]⟩⟩⟩

theorem interior_embedding (n : ℕ) (c : ULift.{u} (Cell X n)) :
    letI := cellStructure.{u} (X := X)
    IsEmbedding (interiorMap (ULift.{u} X) n c) := by
  letI := cellStructure.{u} (X := X)
  exact Homeomorph.ulift.symm.isEmbedding.comp (CWStructure.interior_embedding n c.down)

theorem disjoint_interiors :
    letI := cellStructure.{u} (X := X)
    (univ : Set (Σ n, Cell (ULift.{u} X) n)).PairwiseDisjoint
      (fun c => openCell (ULift.{u} X) c.1 c.2) := by
  letI := cellStructure.{u} (X := X)
  intro a _ b _ hab
  change Disjoint (openCell (ULift.{u} X) a.1 a.2) (openCell (ULift.{u} X) b.1 b.2)
  rw [openCell_eq, openCell_eq]
  apply Disjoint.preimage
  apply CWStructure.disjoint_interiors (mem_univ ⟨a.1, a.2.down⟩)
    (mem_univ ⟨b.1, b.2.down⟩)
  intro h
  apply hab
  cases a with | mk n a =>
    cases b with | mk m b =>
      obtain rfl : n = m := congrArg Sigma.fst h
      have : a.down = b.down := by simpa using h
      simpa using ULift.ext this

theorem cover :
    letI := cellStructure.{u} (X := X)
    ⋃ (n : ℕ) (c : Cell (ULift.{u} X) n), openCell (ULift.{u} X) n c = univ := by
  letI := cellStructure.{u} (X := X)
  apply eq_univ_of_forall
  intro y
  have hy : y.down ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
    rw [CWStructure.cover]; trivial
  obtain ⟨n, c, hc⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨n, ULift.up c, by rwa [openCell_eq]⟩

theorem boundary_lands (n : ℕ) (c : ULift.{u} (Cell X n)) :
    letI := cellStructure.{u} (X := X)
    MapsTo (boundaryMap (ULift.{u} X) n c) univ (skeletonLT (ULift.{u} X) n) := by
  letI := cellStructure.{u} (X := X)
  intro z _
  rw [skeletonLT_eq]
  exact CWStructure.boundary_lands n c.down (mem_univ z)

theorem closure_finite (n : ℕ) (c : ULift.{u} (Cell X n)) :
    letI := cellStructure.{u} (X := X)
    ∃ F : Finset (Σ m, Cell (ULift.{u} X) m),
      closedCell (ULift.{u} X) n c ⊆ ⋃ d ∈ F, openCell (ULift.{u} X) d.1 d.2 := by
  classical
  letI := cellStructure.{u} (X := X)
  obtain ⟨F, hF⟩ := CWStructure.closure_finite n c.down
  let liftIndex : (Σ m, Cell X m) → (Σ m, Cell (ULift.{u} X) m) :=
    Sigma.map id (fun _ => ULift.up)
  refine ⟨F.image liftIndex, ?_⟩
  rintro y ⟨z, hz⟩
  have hy : y.down ∈ closedCell X n c.down := ⟨z, congrArg ULift.down hz⟩
  obtain ⟨d, hd, hy⟩ := mem_iUnion₂.mp (hF hy)
  refine mem_iUnion₂.mpr ⟨liftIndex d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
  change y ∈ openCell (ULift.{u} X) d.1 (ULift.up d.2)
  rwa [openCell_eq]

theorem weak_topology (A : Set (ULift.{u} X)) :
    letI := cellStructure.{u} (X := X)
    IsClosed A ↔ ∀ n (c : Cell (ULift.{u} X) n),
      IsClosed (characteristic (ULift.{u} X) n c ⁻¹' A) := by
  letI := cellStructure.{u} (X := X)
  constructor
  · intro hA n c
    exact hA.preimage (characteristic (ULift.{u} X) n c).continuous
  · intro hA
    have hclosed : IsClosed ((ULift.up : X → ULift.{u} X) ⁻¹' A) := by
      apply (CWStructure.weak_topology _).mpr
      intro n c
      exact hA n (ULift.up c)
    exact hclosed.preimage continuous_uliftDown

@[instance_reducible] def cwStructure : CWStructure (ULift.{u} X) := by
  letI := cellStructure.{u} (X := X)
  exact cwStructureOfWeak interior_embedding disjoint_interiors cover boundary_lands
    closure_finite weak_topology



local instance liftedCW : CWStructure (ULift.{u} X) := cwStructure.{u}

def vertexEquiv : GraphVertex (ULift.{u} X) ≃ GraphVertex X where
  toFun v := ⟨v.val.down, by
    have hv := v.property
    change v.val ∈ skeletonLT (ULift.{u} X) 1 at hv
    rw [skeletonLT_eq] at hv
    exact hv⟩
  invFun v := ⟨ULift.up v.val, by
    change ULift.up v.val ∈ skeletonLT (ULift.{u} X) 1
    rw [skeletonLT_eq]
    exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem isGraph (hgraph : IsGraph X) : IsGraph (ULift.{u} X) := by
  intro n hn
  exact ⟨fun c => (hgraph n hn).false c.down⟩

/-- The arbitrary-universe graph premise also computes any one-vertex graph
in Type 0, by applying it to the homeomorphic lifted CW complex. -/
theorem oneVertexGraphFundamentalGroup_zero
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u})
    (hgraph : IsGraph X) [ConnectedSpace X] [Subsingleton (GraphVertex X)]
    (b : GraphVertex X) :
    ∃ Φ : FreeGroup (Cell X 1) ≃* Pi1 X b.val,
      ∀ e : Cell X 1, Φ (FreeGroup.of e) = loopClass (graphEdgeLoopAtVertex b e) := by
  letI : ConnectedSpace (ULift.{u} X) :=
    Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
  letI : Subsingleton (GraphVertex (ULift.{u} X)) :=
    ⟨fun v w => vertexEquiv.injective (Subsingleton.elim _ _)⟩
  let b' := vertexEquiv.symm b
  obtain ⟨Φ, hΦ⟩ := oneVertexGraphFundamentalGroup graph (isGraph hgraph) b'
  let H : ULift.{u} X ≃ₜ X := Homeomorph.ulift
  let E := pointedHomeomorphEquiv H b'.val b.val rfl
  let labels : Cell X 1 ≃ Cell (ULift.{u} X) 1 := Equiv.ulift.symm
  refine ⟨(FreeGroup.freeGroupCongr labels).trans (Φ.trans E), ?_⟩
  intro e
  change E (Φ (FreeGroup.of (ULift.up e))) = _
  rw [hΦ]
  let P : PointedMap (ULift.{u} X) X b'.val b.val := ⟨⟨H, H.continuous⟩, rfl⟩
  change P.induced (loopClass (graphEdgeLoopAtVertex b' (ULift.up e))) = _
  rw [inducedFormula (ULift.{u} X) X b'.val b.val P]
  rfl

end UniverseLift

namespace SurfaceBouquet

abbrev PuncturedCircle := {z : Circle // z ≠ 1}

instance : LocallyCompactSpace PuncturedCircle :=
  (isOpen_compl_singleton : IsOpen ({1}ᶜ : Set Circle)).locallyCompactSpace

/-- The punctured circle is compactified by restoring its missing point. -/
def circleHomeomorph : OnePoint PuncturedCircle ≃ₜ Circle :=
  OnePoint.equivOfIsEmbeddingOfRangeEq (1 : Circle) (Subtype.val : PuncturedCircle → Circle)
    IsEmbedding.subtypeVal (by ext z; simp)

@[simp] theorem circleHomeomorph_infty : circleHomeomorph ∞ = 1 := rfl

@[simp] theorem circleHomeomorph_coe (z : PuncturedCircle) :
    circleHomeomorph (z : OnePoint PuncturedCircle) = z.val := rfl

@[simp] theorem circleHomeomorph_symm_one : circleHomeomorph.symm 1 = ∞ := by
  apply circleHomeomorph.injective
  simp

@[simp] theorem circleHomeomorph_symm_coe (z : PuncturedCircle) :
    circleHomeomorph.symm z.val = (z : OnePoint PuncturedCircle) := by
  apply circleHomeomorph.injective
  simp

abbrev Space (g : ℕ) := OnePoint (SurfaceGenerator g × PuncturedCircle)

def basepoint (g : ℕ) : Space g := ∞

theorem coordinate_isClosedEmbedding (g : ℕ) (j : SurfaceGenerator g) :
    IsClosedEmbedding (Prod.mk j : PuncturedCircle → SurfaceGenerator g × PuncturedCircle) := by
  refine ⟨isEmbedding_prodMkRight j, ?_⟩
  have he : Set.range (Prod.mk j : PuncturedCircle → SurfaceGenerator g × PuncturedCircle) =
      (Prod.fst : SurfaceGenerator g × PuncturedCircle → SurfaceGenerator g) ⁻¹' {j} := by
    ext p
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z,rfl⟩
      rfl
    · intro h
      exact ⟨p.2, Prod.ext h.symm rfl⟩
  rw [he]
  exact isClosed_singleton.preimage continuous_fst

theorem coordinate_onePoint_continuous (g : ℕ) (j : SurfaceGenerator g) :
    Continuous (OnePoint.map (Prod.mk j) : OnePoint PuncturedCircle → Space g) := by
  apply OnePoint.continuous_map (continuous_const.prodMk continuous_id)
  rw [Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
  exact (isProperMap_iff_tendsto_cocompact.mp
    (coordinate_isClosedEmbedding g j).isProperMap).2

/-- The actual circle in the selected summand of the finite bouquet. -/
def circleInclusion (g : ℕ) (j : SurfaceGenerator g) : C(Circle, Space g) :=
  ⟨fun z => OnePoint.map (Prod.mk j) (circleHomeomorph.symm z),
    (coordinate_onePoint_continuous g j).comp circleHomeomorph.symm.continuous⟩

@[simp] theorem circleInclusion_one (g : ℕ) (j : SurfaceGenerator g) :
    circleInclusion g j 1 = basepoint g := by
  simp [circleInclusion, basepoint]

@[simp] theorem circleInclusion_coe (g : ℕ) (j : SurfaceGenerator g) (z : PuncturedCircle) :
    circleInclusion g j z.val = ((j,z) : SurfaceGenerator g × PuncturedCircle) := by
  simp [circleInclusion]

theorem circleInclusion_injective (g : ℕ) (j : SurfaceGenerator g) :
    Function.Injective (circleInclusion g j) := by
  intro z w h
  apply circleHomeomorph.symm.injective
  change OnePoint.map (Prod.mk j) (circleHomeomorph.symm z) =
    OnePoint.map (Prod.mk j) (circleHomeomorph.symm w) at h
  have hmap : Function.Injective (OnePoint.map (Prod.mk j) :
      OnePoint PuncturedCircle → Space g) := by
    intro p q h
    cases p using OnePoint.rec <;> cases q using OnePoint.rec <;>
      simp_all only [OnePoint.map_infty, OnePoint.map_some,
        OnePoint.infty_ne_coe, OnePoint.coe_ne_infty, OnePoint.coe_eq_coe, Prod.mk.injEq,
        true_and]
  exact hmap h

theorem circleInclusion_range (g : ℕ) (j : SurfaceGenerator g) :
    Set.range (circleInclusion g j) =
      {basepoint g} ∪ OnePoint.some '' ({j} ×ˢ (Set.univ : Set PuncturedCircle)) := by
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    by_cases hz : z = 1
    · subst z
      exact Or.inl (by simp)
    · right
      exact ⟨(j,⟨z,hz⟩), ⟨rfl, trivial⟩, (circleInclusion_coe g j ⟨z,hz⟩).symm⟩
  · rintro (hp | ⟨⟨k,z⟩,⟨hk,_⟩,rfl⟩)
    · exact ⟨1, by simpa using hp.symm⟩
    · obtain rfl : k = j := hk
      exact ⟨z.val, circleInclusion_coe g k z⟩

theorem norm_oneDim (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  have he : x = EuclideanSpace.single 0 (x 0) := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [he, PiLp.norm_single, Real.norm_eq_abs]
  simp

def openDiskIntervalHomeomorph : OpenDisk 1 ≃ₜ Set.Ioo (0:ℝ) 1 where
  toFun x := ⟨(x.val 0 + 1) / 2, by
    have hx : |x.val 0| < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_oneDim] using x.property
    obtain ⟨hl,hr⟩ := abs_lt.mp hx
    constructor <;> linarith⟩
  invFun t := ⟨EuclideanSpace.single 0 (2 * t.val - 1), by
    rw [Metric.mem_ball, dist_zero_right, PiLp.norm_single, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [t.property.1,t.property.2]⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
    ring
  right_inv t := by
    apply Subtype.ext
    simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 1 => ℝ) 0).comp
      continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : Set.Ioo (0:ℝ) 1 => WithLp.toLp 2
      (Pi.single (M := fun _ : Fin 1 => ℝ) 0 (2 * t.val - 1)))
    apply (PiLp.continuous_toLp _ _).comp
    apply continuous_pi
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa using (show Continuous (fun t : Set.Ioo (0:ℝ) 1 => 2 * t.val - 1) by fun_prop)

/-- The normalized exponential traverses the punctured circle exactly once. -/
def intervalCircleHomeomorph : Set.Ioo (0:ℝ) 1 ≃ₜ PuncturedCircle := by
  let e := AddCircle.openPartialHomeomorphCoe (1:ℝ) 0
  let H := AddCircle.homeomorphCircle (T := 1) one_ne_zero
  let H' : {x : AddCircle (1:ℝ) // x ≠ 0} ≃ₜ PuncturedCircle :=
    H.subtype (fun x => by
      have h0 : H 0 = 1 := by simp [H, AddCircle.homeomorphCircle_apply]
      exact ⟨fun hx h => hx (H.injective (h.trans h0.symm)), fun hx h => hx (by rw [h,h0])⟩)
  exact (Homeomorph.setCongr (by simp [e])).trans
    (e.toHomeomorphSourceTarget.trans H')

@[simp] theorem intervalCircleHomeomorph_coe (t : Set.Ioo (0:ℝ) 1) :
    (intervalCircleHomeomorph t).val =
      P202Specs.Topology.BasicFundamentalGroups.circleCover t.val := by
  exact (circleCover_eq t.val).symm

def edgeCircle (z : Disk 1) : Circle :=
  P202Specs.Topology.BasicFundamentalGroups.circleCover ((z.val 0 + 1) / 2)

theorem edgeCircle_continuous : Continuous edgeCircle := by
  apply P202Specs.Topology.BasicFundamentalGroups.circleCover.continuous.comp
  exact (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 1 => ℝ) 0).comp
    continuous_subtype_val).add continuous_const).div_const 2

theorem edgeCircle_openDisk (z : OpenDisk 1) :
    edgeCircle (interiorInclusion 1 z) =
      (intervalCircleHomeomorph (openDiskIntervalHomeomorph z)).val :=
  (intervalCircleHomeomorph_coe (openDiskIntervalHomeomorph z)).symm

def edgeCharacteristic (g : ℕ) (j : SurfaceGenerator g) : C(Disk 1, Space g) :=
  ⟨fun z => circleInclusion g j (edgeCircle z),
    (circleInclusion g j).continuous.comp edgeCircle_continuous⟩

theorem edgeCharacteristic_openDisk (g : ℕ) (j : SurfaceGenerator g) (z : OpenDisk 1) :
    edgeCharacteristic g j (interiorInclusion 1 z) =
      ((j,intervalCircleHomeomorph (openDiskIntervalHomeomorph z)) :
        SurfaceGenerator g × PuncturedCircle) := by
  change circleInclusion g j (edgeCircle (interiorInclusion 1 z)) = _
  rw [edgeCircle_openDisk, circleInclusion_coe]

theorem edgeCharacteristic_isEmbedding (g : ℕ) (j : SurfaceGenerator g) :
    IsEmbedding (fun z : OpenDisk 1 => edgeCharacteristic g j (interiorInclusion 1 z)) := by
  have he : (fun z : OpenDisk 1 => edgeCharacteristic g j (interiorInclusion 1 z)) =
      OnePoint.some ∘ Prod.mk j ∘ intervalCircleHomeomorph ∘ openDiskIntervalHomeomorph := by
    funext z
    exact edgeCharacteristic_openDisk g j z
  rw [he]
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp
    ((isEmbedding_prodMkRight j).comp
      (intervalCircleHomeomorph.isEmbedding.comp openDiskIntervalHomeomorph.isEmbedding))

theorem edgeCharacteristic_boundary (g : ℕ) (j : SurfaceGenerator g) (z : Sphere 1) :
    edgeCharacteristic g j (boundaryInclusion 1 z) = basepoint g := by
  have hz : |z.val 0| = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_oneDim] using z.property
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hz with h | h
  · change circleInclusion g j
      (P202Specs.Topology.BasicFundamentalGroups.circleCover ((z.val 0 + 1) / 2)) = _
    rw [h]
    norm_num [P202Specs.Topology.BasicFundamentalGroups.circleCover, Circle.exp_two_pi]
  · change circleInclusion g j
      (P202Specs.Topology.BasicFundamentalGroups.circleCover ((z.val 0 + 1) / 2)) = _
    rw [h]
    norm_num [P202Specs.Topology.BasicFundamentalGroups.circleCover]

def circleProjection (g : ℕ) : C(SurfaceGenerator g × Circle, Space g) :=
  ⟨fun p => circleInclusion g p.1 p.2,
    continuous_prod_of_discrete_left.mpr (fun j => (circleInclusion g j).continuous)⟩

theorem circleProjection_surjective (g : ℕ) (hg : 0 < g) :
    Function.Surjective (circleProjection g) := by
  intro y
  cases y using OnePoint.rec with
  | infty => exact ⟨(⟨⟨0,hg⟩,false⟩,1), circleInclusion_one g _⟩
  | coe p => exact ⟨(p.1,p.2.val), circleInclusion_coe g p.1 p.2⟩

theorem circleProjection_isQuotientMap (g : ℕ) (hg : 0 < g) :
    IsQuotientMap (circleProjection g) :=
  IsQuotientMap.of_surjective_continuous (circleProjection_surjective g hg)
    (circleProjection g).continuous

theorem circleProjection_fiber (g : ℕ) (p q : SurfaceGenerator g × Circle)
    (h : circleProjection g p = circleProjection g q) :
    p = q ∨ p.2 = 1 ∧ q.2 = 1 := by
  by_cases hp : p.2 = 1
  · right
    refine ⟨hp, ?_⟩
    apply circleInclusion_injective g q.1
    have hh : circleInclusion g p.1 p.2 = circleInclusion g q.1 q.2 := h
    rw [hp, circleInclusion_one] at hh
    exact hh.symm.trans (circleInclusion_one g q.1).symm
  · by_cases hq : q.2 = 1
    · have hh : circleInclusion g p.1 p.2 = circleInclusion g q.1 q.2 := h
      rw [hq, circleInclusion_one] at hh
      exact False.elim (hp ((circleInclusion_injective g p.1)
        (hh.trans (circleInclusion_one g p.1).symm)))
    · left
      have hh : (((p.1,⟨p.2,hp⟩) : SurfaceGenerator g × PuncturedCircle) : Space g) =
          (((q.1,⟨q.2,hq⟩) : SurfaceGenerator g × PuncturedCircle) : Space g) := by
        simpa only [circleProjection, ContinuousMap.coe_mk,
          ← circleInclusion_coe g p.1 ⟨p.2,hp⟩,
          ← circleInclusion_coe g q.1 ⟨q.2,hq⟩] using h
      have hval := OnePoint.coe_injective hh
      exact Prod.ext (congrArg (fun r : SurfaceGenerator g × PuncturedCircle => r.1) hval)
        (congrArg (fun r : SurfaceGenerator g × PuncturedCircle => r.2.val) hval)

/-- The finite bouquet is the genuine topological quotient of its circles,
and a compatible continuous family therefore descends to it. -/
def descendCircles {Y : Type*} [TopologicalSpace Y] (g : ℕ) (hg : 0 < g)
    (f : SurfaceGenerator g → C(Circle,Y)) (b : Y) (hb : ∀ j, f j 1 = b) :
    C(Space g,Y) := by
  let raw : C(SurfaceGenerator g × Circle,Y) :=
    ⟨fun p => f p.1 p.2,
      continuous_prod_of_discrete_left.mpr (fun j => (f j).continuous)⟩
  apply (circleProjection_isQuotientMap g hg).lift raw
  intro p q h
  rcases circleProjection_fiber g p q h with rfl | ⟨hp,hq⟩
  · rfl
  · exact (by change f p.1 p.2 = f q.1 q.2; rw [hp,hq,hb,hb])

@[simp] theorem descendCircles_circle {Y : Type*} [TopologicalSpace Y] (g : ℕ) (hg : 0 < g)
    (f : SurfaceGenerator g → C(Circle,Y)) (b : Y) (hb : ∀ j, f j 1 = b)
    (j : SurfaceGenerator g) (z : Circle) :
    descendCircles g hg f b hb (circleInclusion g j z) = f j z := by
  unfold descendCircles
  exact DFunLike.congr_fun ((circleProjection_isQuotientMap g hg).lift_comp
    (⟨fun p : SurfaceGenerator g × Circle => f p.1 p.2,
      continuous_prod_of_discrete_left.mpr (fun j => (f j).continuous)⟩ :
        C(SurfaceGenerator g × Circle,Y)) (by
          intro p q h
          rcases circleProjection_fiber g p q h with rfl | ⟨hp,hq⟩
          · rfl
          · change f p.1 p.2 = f q.1 q.2
            rw [hp,hq,hb,hb])) (j,z)


theorem edgeCircle_surjective : Function.Surjective edgeCircle := by
  intro z
  by_cases hz : z = 1
  · subst z
    refine ⟨edgeDiskPoint 0, ?_⟩
    simp [edgeCircle, edgeDiskPoint, P202Specs.Topology.BasicFundamentalGroups.circleCover]
  · obtain ⟨t, ht⟩ := intervalCircleHomeomorph.surjective ⟨z,hz⟩
    obtain ⟨w, hw⟩ := openDiskIntervalHomeomorph.surjective t
    refine ⟨interiorInclusion 1 w, ?_⟩
    rw [edgeCircle_openDisk, hw, ht]

def edgeProjection (g : ℕ) : C(SurfaceGenerator g × Disk 1, Space g) :=
  ⟨fun p => edgeCharacteristic g p.1 p.2,
    continuous_prod_of_discrete_left.mpr (fun j => (edgeCharacteristic g j).continuous)⟩

theorem edgeProjection_surjective (g : ℕ) (hg : 0 < g) :
    Function.Surjective (edgeProjection g) := by
  intro y
  obtain ⟨⟨j,z⟩, h⟩ := circleProjection_surjective g hg y
  obtain ⟨w, hw⟩ := edgeCircle_surjective z
  exact ⟨(j,w), by change circleInclusion g j (edgeCircle w) = y; rw [hw]; exact h⟩

theorem edgeProjection_isQuotientMap (g : ℕ) (hg : 0 < g) :
    IsQuotientMap (edgeProjection g) :=
  IsQuotientMap.of_surjective_continuous (edgeProjection_surjective g hg)
    (edgeProjection g).continuous

def Cell (g : ℕ) : ℕ → Type
  | 0 => PUnit
  | 1 => SurfaceGenerator g
  | _ + 2 => PEmpty

def characteristic (g : ℕ) : ∀ n, Cell g n → C(Disk n, Space g)
  | 0, _ => ContinuousMap.const _ (basepoint g)
  | 1, j => edgeCharacteristic g j
  | _ + 2, j => PEmpty.elim j

@[instance_reducible] def cellStructure (g : ℕ) : CellStructure (Space g) where
  Cell := Cell g
  characteristic := characteristic g

theorem openCell_zero (g : ℕ) (c : Cell g 0) :
    letI := cellStructure g
    openCell (Space g) 0 c = {basepoint g} := by
  letI := cellStructure g
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    rfl
  · intro hx
    obtain rfl : x = basepoint g := hx
    exact ⟨⟨0, by simp [Metric.mem_ball]⟩,rfl⟩

theorem openCell_one (g : ℕ) (j : Cell g 1) :
    letI := cellStructure g
    openCell (Space g) 1 j =
      OnePoint.some '' ({j} ×ˢ (Set.univ : Set PuncturedCircle)) := by
  letI := cellStructure g
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨(j, intervalCircleHomeomorph (openDiskIntervalHomeomorph z)),
      ⟨rfl,trivial⟩, (edgeCharacteristic_openDisk g j z).symm⟩
  · rintro ⟨⟨k,z⟩,⟨hk,_⟩,rfl⟩
    obtain rfl : k = j := hk
    obtain ⟨t, ht⟩ := intervalCircleHomeomorph.surjective z
    obtain ⟨w, hw⟩ := openDiskIntervalHomeomorph.surjective t
    refine ⟨w, ?_⟩
    change edgeCharacteristic g k (interiorInclusion 1 w) = _
    rw [edgeCharacteristic_openDisk, hw, ht]

theorem skeletonLT_one (g : ℕ) :
    letI := cellStructure g
    skeletonLT (Space g) 1 = {basepoint g} := by
  letI := cellStructure g
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, c, hc⟩ := by simpa only [P202.Cellular.skeletonLT, mem_iUnion] using hx
    have hn0 : n = 0 := by omega
    subst n
    rwa [openCell_zero] at hc
  · intro hx
    exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by omega,
      mem_iUnion.mpr ⟨PUnit.unit, by rwa [openCell_zero]⟩⟩⟩

theorem interior_embedding (g : ℕ) (n : ℕ) (c : Cell g n) :
    letI := cellStructure g
    IsEmbedding (interiorMap (Space g) n c) := by
  letI := cellStructure g
  cases n with
  | zero => exact IsEmbedding.of_subsingleton _
  | succ n =>
    cases n with
    | zero => exact edgeCharacteristic_isEmbedding g c
    | succ n => exact PEmpty.elim c

theorem interiors_disjoint (g : ℕ) :
    letI := cellStructure g
    (univ : Set (Σ n, P202.Cellular.Cell (Space g) n)).PairwiseDisjoint
      (fun c => openCell (Space g) c.1 c.2) := by
  letI := cellStructure g
  rintro ⟨n,c⟩ _ ⟨m,d⟩ _ hne
  change Disjoint (openCell (Space g) n c) (openCell (Space g) m d)
  cases n with
  | zero =>
    cases m with
    | zero => exact False.elim (hne (by congr 1))
    | succ m =>
      cases m with
      | zero =>
        rw [openCell_zero, openCell_one]
        apply Set.disjoint_left.mpr
        intro x hx hy
        obtain rfl : x = basepoint g := hx
        obtain ⟨z,_,hz⟩ := hy
        exact OnePoint.coe_ne_infty z hz
      | succ m => exact PEmpty.elim d
  | succ n =>
    cases n with
    | zero =>
      cases m with
      | zero =>
        rw [openCell_one, openCell_zero]
        apply Set.disjoint_left.mpr
        intro x hx hy
        obtain rfl : x = basepoint g := hy
        obtain ⟨z,_,hz⟩ := hx
        exact OnePoint.coe_ne_infty z hz
      | succ m =>
        cases m with
        | zero =>
          rw [openCell_one, openCell_one]
          apply Set.disjoint_left.mpr
          rintro x ⟨⟨j,z⟩,⟨hj,_⟩,hx⟩ ⟨⟨k,w⟩,⟨hk,_⟩,hy⟩
          have hpair := OnePoint.coe_injective (hx.trans hy.symm)
          apply hne
          congr 1
          exact hj.symm.trans ((congrArg (fun p : SurfaceGenerator g × PuncturedCircle => p.1) hpair).trans hk)
        | succ m => exact PEmpty.elim d
    | succ n => exact PEmpty.elim c

theorem cells_cover (g : ℕ) :
    letI := cellStructure g
    ⋃ (n : ℕ) (c : P202.Cellular.Cell (Space g) n), openCell (Space g) n c = univ := by
  letI := cellStructure g
  apply eq_univ_of_forall
  intro x
  cases x using OnePoint.rec with
  | infty => exact mem_iUnion₂.mpr ⟨0,PUnit.unit,by rw [openCell_zero]; rfl⟩
  | coe p =>
    exact mem_iUnion₂.mpr ⟨1,p.1,by rw [openCell_one]; exact ⟨p,⟨rfl,trivial⟩,rfl⟩⟩

theorem boundary_lands (g : ℕ) (n : ℕ) (c : Cell g n) :
    letI := cellStructure g
    MapsTo (boundaryMap (Space g) n c) univ (P202.Cellular.skeletonLT (Space g) n) := by
  letI := cellStructure g
  intro z _
  cases n with
  | zero =>
    have he : z.val = 0 := Subsingleton.elim _ _
    have hz := z.property
    simp [Metric.mem_sphere, he] at hz
  | succ n =>
    cases n with
    | zero =>
      rw [skeletonLT_one]
      exact edgeCharacteristic_boundary g c z
    | succ n => exact PEmpty.elim c

theorem closure_finite (g : ℕ) (n : ℕ) (c : Cell g n) :
    letI := cellStructure g
    ∃ F : Finset (Σ m, P202.Cellular.Cell (Space g) m),
      closedCell (Space g) n c ⊆ ⋃ d ∈ F, openCell (Space g) d.1 d.2 := by
  classical
  letI := cellStructure g
  cases n with
  | zero =>
    refine ⟨{⟨0,PUnit.unit⟩}, ?_⟩
    rintro x ⟨z,rfl⟩
    exact mem_iUnion₂.mpr ⟨⟨0,PUnit.unit⟩, Finset.mem_singleton_self _, by
      rw [openCell_zero]; rfl⟩
  | succ n =>
    cases n with
    | zero =>
      refine ⟨{⟨0,PUnit.unit⟩,⟨1,c⟩}, ?_⟩
      rintro x ⟨z,rfl⟩
      have hx : edgeCharacteristic g c z ∈ Set.range (circleInclusion g c) := ⟨edgeCircle z,rfl⟩
      rw [circleInclusion_range] at hx
      rcases hx with hx | hx
      · exact mem_iUnion₂.mpr ⟨⟨0,PUnit.unit⟩, by simp, by rwa [openCell_zero]⟩
      · exact mem_iUnion₂.mpr ⟨⟨1,c⟩, by simp, by rwa [openCell_one]⟩
    | succ n => exact PEmpty.elim c

theorem weak_topology (g : ℕ) (hg : 0 < g) (A : Set (Space g)) :
    letI := cellStructure g
    IsClosed A ↔ ∀ n (c : P202.Cellular.Cell (Space g) n),
      IsClosed (P202.Cellular.characteristic (Space g) n c ⁻¹' A) := by
  letI := cellStructure g
  constructor
  · intro hA n c
    exact hA.preimage (P202.Cellular.characteristic (Space g) n c).continuous
  · intro hA
    apply (edgeProjection_isQuotientMap g hg).isClosed_preimage.mp
    have he : edgeProjection g ⁻¹' A =
        ⋃ j : SurfaceGenerator g, {j} ×ˢ (edgeCharacteristic g j ⁻¹' A) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro hp
        exact ⟨p.1,rfl,hp⟩
      · rintro ⟨j,hj,hp⟩
        subst j
        exact hp
    rw [he]
    exact isClosed_iUnion_of_finite (fun j => isClosed_singleton.prod (hA 1 j))

/-- A genuine finite CW bouquet, with its original oriented circle labels. -/
@[instance_reducible] def cwStructure (g : ℕ) (hg : 0 < g) : CWStructure (Space g) := by
  letI := cellStructure g
  exact cwStructureOfWeak (interior_embedding g) (interiors_disjoint g)
    (cells_cover g) (boundary_lands g) (closure_finite g) (weak_topology g hg)


theorem pathConnected (g : ℕ) : PathConnectedSpace (Space g) := by
  have hreach : ∀ x : Space g, Joined (basepoint g) x := by
    intro x
    induction x using OnePoint.rec with
    | infty => exact Joined.refl _
    | coe p =>
      simpa only [circleInclusion_one, circleInclusion_coe] using
        ((PathConnectedSpace.joined (1 : Circle) p.2.val).map (circleInclusion g p.1).continuous)
  exact {
    nonempty := ⟨basepoint g⟩
    joined := fun x y => (hreach x).symm.trans (hreach y) }

theorem edgeCharacteristic_edgeDiskPoint (g : ℕ) (j : SurfaceGenerator g)
    (t : unitInterval) :
    edgeCharacteristic g j (edgeDiskPoint t) =
      circleInclusion g j (P202Specs.Topology.BasicFundamentalGroups.circleCover t.val) := by
  change circleInclusion g j
    (P202Specs.Topology.BasicFundamentalGroups.circleCover _) = _
  congr 2
  simp only [edgeDiskPoint, PiLp.single_apply, Fin.isValue, ↓reduceIte]
  ring

def edgeLoop (g : ℕ) (j : SurfaceGenerator g) : Path (basepoint g) (basepoint g) where
  toFun t := circleInclusion g j (P202Specs.Topology.BasicFundamentalGroups.circleCover t.val)
  continuous_toFun := (circleInclusion g j).continuous.comp
    (P202Specs.Topology.BasicFundamentalGroups.circleCover.continuous.comp continuous_subtype_val)
  source' := by simp [P202Specs.Topology.BasicFundamentalGroups.circleCover]
  target' := by norm_num [P202Specs.Topology.BasicFundamentalGroups.circleCover, Circle.exp_two_pi]


theorem freeFundamentalGroup
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u})
    (g : ℕ) (hg : 0 < g) :
    ∃ Φ : FreeGroup (SurfaceGenerator g) ≃* Pi1 (Space g) (basepoint g),
      ∀ j, Φ (FreeGroup.of j) = loopClass (edgeLoop g j) := by
  letI := cwStructure g hg
  letI := pathConnected g
  have hb : basepoint g ∈ GraphVertex (Space g) := by
    change basepoint g ∈ skeletonLT (Space g) 1
    rw [skeletonLT_one]
    rfl
  let b : GraphVertex (Space g) := ⟨basepoint g, hb⟩
  letI : Subsingleton (GraphVertex (Space g)) := by
    constructor
    intro v w
    apply Subtype.ext
    have hv := v.property
    have hw := w.property
    change v.val ∈ skeletonLT (Space g) 1 at hv
    change w.val ∈ skeletonLT (Space g) 1 at hw
    rw [skeletonLT_one] at hv hw
    exact hv.trans hw.symm
  have hgraph : IsGraph (Space g) := by
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ n => exact ⟨fun c => PEmpty.elim c⟩
  obtain ⟨Φ, hΦ⟩ := UniverseLift.oneVertexGraphFundamentalGroup_zero graph hgraph b
  refine ⟨Φ, ?_⟩
  intro j
  refine (hΦ j).trans ?_
  congr 1
  apply Path.ext
  funext t
  exact edgeCharacteristic_edgeDiskPoint g j t


end SurfaceBouquet

namespace SurfacePolygonProof
open P202.Cellular.SurfacePolygon

theorem sidePoint_join (g : ℕ) (i : Fin g) (k l : Fin 4)
    (hkl : k.val + 1 = l.val) : sidePoint g i k 1 = sidePoint g i l 0 := by
  have hr : (k.val : ℝ) + 1 = l.val := by exact_mod_cast hkl
  simp only [sidePoint, Set.Icc.coe_one, Set.Icc.coe_zero, add_zero]
  rw [add_assoc, hr]

theorem handleVertices (g : ℕ) (i : Fin g) (k : Fin 4)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    projection g (sidePoint g i k t) = projection g (sidePoint g i 0 0) := by
  have ha0 : projection g (sidePoint g i 0 0) =
      projection g (sidePoint g i 2 1) := by
    simpa only [projection, Space, ContinuousMap.coe_mk, unitInterval.symm_zero] using
      (Quotient.sound (Relation.EqvGen.rel _ _ (SideRelation.a i 0)) :
      projection g (sidePoint g i 0 0) =
        projection g (sidePoint g i 2 (unitInterval.symm 0)))
  have ha1 : projection g (sidePoint g i 0 1) =
      projection g (sidePoint g i 2 0) := by
    simpa only [projection, Space, ContinuousMap.coe_mk, unitInterval.symm_one] using
      (Quotient.sound (Relation.EqvGen.rel _ _ (SideRelation.a i 1)) :
      projection g (sidePoint g i 0 1) =
        projection g (sidePoint g i 2 (unitInterval.symm 1)))
  have hb0 : projection g (sidePoint g i 1 0) =
      projection g (sidePoint g i 3 1) := by
    simpa only [projection, Space, ContinuousMap.coe_mk, unitInterval.symm_zero] using
      (Quotient.sound (Relation.EqvGen.rel _ _ (SideRelation.b i 0)) :
      projection g (sidePoint g i 1 0) =
        projection g (sidePoint g i 3 (unitInterval.symm 0)))
  have hb1 : projection g (sidePoint g i 1 1) =
      projection g (sidePoint g i 3 0) := by
    simpa only [projection, Space, ContinuousMap.coe_mk, unitInterval.symm_one] using
      (Quotient.sound (Relation.EqvGen.rel _ _ (SideRelation.b i 1)) :
      projection g (sidePoint g i 1 1) =
        projection g (sidePoint g i 3 (unitInterval.symm 1)))
  have hj0 := congrArg (projection g) (sidePoint_join g i 0 1 rfl)
  have hj1 := congrArg (projection g) (sidePoint_join g i 1 2 rfl)
  have hj2 := congrArg (projection g) (sidePoint_join g i 2 3 rfl)
  have h3 := hj2.symm.trans ha0.symm
  have h2 := hj1.symm.trans (hb1.trans h3)
  have h1 := hj0.symm.trans (ha1.trans h2)
  rcases ht with rfl | rfl
  · fin_cases k
    · rfl
    · exact h1
    · exact h2
    · exact h3
  · fin_cases k
    · exact hj0.trans h1
    · exact hj1.trans h2
    · exact ha0.symm
    · exact hb0.symm.trans h1

/-- All polygon vertices are identified by the specified side pairings.
No surface-group theorem is used in this point-set calculation. -/
theorem vertices (g : ℕ) (i : Fin g) (k : Fin 4)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    projection g (sidePoint g i k t) = basepoint g := by
  have hstart : ∀ (j : ℕ) (hj : j < g),
      projection g (sidePoint g ⟨j, hj⟩ 0 0) = basepoint g := by
    intro j
    induction j with
    | zero => intro hj; simp [sidePoint, basepoint]
    | succ j ih =>
      intro hj
      have hj' : j < g := by omega
      have he : sidePoint g ⟨j, hj'⟩ 3 1 = sidePoint g ⟨j + 1, hj⟩ 0 0 := by
        unfold sidePoint
        norm_num
        congr 1
        push_cast
        ring
      exact (congrArg (projection g) he.symm).trans
        ((handleVertices g ⟨j, hj'⟩ 3 1 (Or.inr rfl)).trans (ih hj'))
  exact (handleVertices g i k t ht).trans (hstart i.val i.isLt)

@[simp] theorem projection_side_a (g : ℕ) (i : Fin g) (t : unitInterval) :
    projection g (sidePoint g i 0 t) =
      projection g (sidePoint g i 2 (unitInterval.symm t)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SideRelation.a i t))

@[simp] theorem projection_side_b (g : ℕ) (i : Fin g) (t : unitInterval) :
    projection g (sidePoint g i 1 t) =
      projection g (sidePoint g i 3 (unitInterval.symm t)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SideRelation.b i t))

def sideLoop (g : ℕ) (i : Fin g) (k : Fin 4) : Path (basepoint g) (basepoint g) :=
  (sidePath g i k).cast (vertices g i k 0 (Or.inl rfl)).symm
    (vertices g i k 1 (Or.inr rfl)).symm

@[simp] theorem sideLoop_apply (g : ℕ) (i : Fin g) (k : Fin 4) (t : unitInterval) :
    sideLoop g i k t = projection g (sidePoint g i k t) := rfl

theorem sideLoop_opposite_a (g : ℕ) (i : Fin g) :
    sideLoop g i 2 = (sideLoop g i 0).symm := by
  ext t
  simpa only [sideLoop_apply, Path.symm_apply, Function.comp_apply,
    unitInterval.symm_symm] using
    (projection_side_a g i (unitInterval.symm t)).symm

theorem sideLoop_opposite_b (g : ℕ) (i : Fin g) :
    sideLoop g i 3 = (sideLoop g i 1).symm := by
  ext t
  simpa only [sideLoop_apply, Path.symm_apply, Function.comp_apply,
    unitInterval.symm_symm] using
    (projection_side_b g i (unitInterval.symm t)).symm

@[simp] theorem sideLoop_class_a_inverse (g : ℕ) (i : Fin g) :
    loopClass (sideLoop g i 2) = (loopClass (sideLoop g i 0))⁻¹ := by
  rw [sideLoop_opposite_a]
  rfl

@[simp] theorem sideLoop_class_b_inverse (g : ℕ) (i : Fin g) :
    loopClass (sideLoop g i 3) = (loopClass (sideLoop g i 1))⁻¹ := by
  rw [sideLoop_opposite_b]
  rfl

def boundaryLine (g : ℕ) : C(ℝ, Space g) :=
  ⟨fun t => projection g (boundaryPoint t), (projection g).continuous.comp (by
    apply Continuous.subtype_mk
    exact Complex.orthonormalBasisOneI.repr.continuous.comp
      (continuous_subtype_val.comp
        P202Specs.Topology.BasicFundamentalGroups.circleCover.continuous))⟩

theorem boundaryPoint_one : boundaryPoint 1 = boundaryPoint 0 := by
  apply Subtype.ext
  simp [boundaryPoint, P202Specs.Topology.BasicFundamentalGroups.circleCover,
    Circle.exp_two_pi]

def linearPath (s t : ℝ) : Path s t where
  toFun u := (1 - (u : ℝ)) * s + (u : ℝ) * t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

def segmentLoop (g : ℕ) (s t : ℝ)
    (hs : boundaryLine g s = basepoint g) (ht : boundaryLine g t = basepoint g) :
    Path (basepoint g) (basepoint g) :=
  ((linearPath s t).map (boundaryLine g).continuous).cast hs.symm ht.symm

theorem segmentLoop_mul (g : ℕ) (s t u : ℝ)
    (hs : boundaryLine g s = basepoint g) (ht : boundaryLine g t = basepoint g)
    (hu : boundaryLine g u = basepoint g) :
    loopClass (segmentLoop g s t hs ht) * loopClass (segmentLoop g t u ht hu) =
      loopClass (segmentLoop g s u hs hu) := by
  apply pathClass_injective
  rw [pathClass_mul, pathClass_loopClass, pathClass_loopClass, pathClass_loopClass]
  rw [← Path.Homotopic.Quotient.mk_trans]
  apply Path.Homotopic.Quotient.eq.mpr
  have h : ((linearPath s t).trans (linearPath t u)).Homotopic (linearPath s u) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hh := h.map (boundaryLine g)
  have hhh := hh.pathCast hs.symm hu.symm
  rw [Path.map_trans] at hhh
  exact hhh

@[simp] theorem segmentLoop_self (g : ℕ) (s : ℝ)
    (hs : boundaryLine g s = basepoint g) :
    segmentLoop g s s hs hs = Path.refl (basepoint g) := by
  ext t
  change boundaryLine g ((1 - (t : ℝ)) * s + (t : ℝ) * s) = basepoint g
  rw [show (1 - (t : ℝ)) * s + (t : ℝ) * s = s by ring]
  exact hs

theorem segmentLoop_prod (g n : ℕ) (s : Fin (n + 1) → ℝ)
    (hs : ∀ k, boundaryLine g (s k) = basepoint g) :
    (List.ofFn fun k : Fin n => loopClass
      (segmentLoop g (s k.castSucc) (s k.succ) (hs _) (hs _))).prod =
      loopClass (segmentLoop g (s 0) (s (Fin.last n)) (hs _) (hs _)) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Fin.last_zero, segmentLoop_self]
    exact ((groupConvention (Space g) (basepoint g)).2.1).symm
  | succ n ih =>
    rw [List.ofFn_succ', List.prod_concat]
    have hh := ih (s ∘ Fin.castSucc) (fun k => hs _)
    dsimp only [Function.comp_apply] at hh
    simp only [Fin.castSucc_succ] at hh
    rw [hh]
    exact segmentLoop_mul g (s 0) (s (Fin.last n).castSucc) (s (Fin.last (n + 1)))
      (hs _) (hs _) (hs _)

def sideAngle (g : ℕ) (i : Fin g) (k : ℕ) : ℝ :=
  (4 * (i.val : ℝ) + k) / (4 * (g : ℝ))

theorem sideAngle_vertex (g : ℕ) (i : Fin g) (k : ℕ) (hk : k ≤ 4) :
    boundaryLine g (sideAngle g i k) = basepoint g := by
  by_cases hlt : k < 4
  · simpa [boundaryLine, sideAngle, sidePoint] using
      vertices g i ⟨k,hlt⟩ 0 (Or.inl rfl)
  · have hkeq : k = 4 := by omega
    subst k
    convert vertices g i 3 1 (Or.inr rfl) using 1
    change projection g (boundaryPoint ((4 * (i.val:ℝ)+(4:ℝ))/(4*(g:ℝ)))) =
      projection g (boundaryPoint ((4 * (i.val:ℝ)+(3:ℝ)+1)/(4*(g:ℝ))))
    congr 2
    ring

theorem sideLoop_eq_segment (g : ℕ) (i : Fin g) (k : Fin 4) :
    sideLoop g i k = segmentLoop g (sideAngle g i k.val)
      (sideAngle g i (k.val + 1))
      (sideAngle_vertex g i k.val (by omega))
      (sideAngle_vertex g i (k.val+1) (by omega)) := by
  ext t
  change projection g (boundaryPoint ((4*(i.val:ℝ)+(k.val:ℝ)+(t:ℝ))/(4*(g:ℝ)))) =
    projection g (boundaryPoint
      ((1-(t:ℝ))*sideAngle g i k.val + (t:ℝ)*sideAngle g i (k.val+1)))
  congr 2
  simp only [sideAngle, Nat.cast_add, Nat.cast_one]
  ring

theorem handle_commutator_segment (g : ℕ) (i : Fin g) :
    loopClass (sideLoop g i 0) * loopClass (sideLoop g i 1) *
      (loopClass (sideLoop g i 0))⁻¹ * (loopClass (sideLoop g i 1))⁻¹ =
      loopClass (segmentLoop g (sideAngle g i 0) (sideAngle g i 4)
        (sideAngle_vertex g i 0 (by omega)) (sideAngle_vertex g i 4 (by omega))) := by
  rw [← sideLoop_class_a_inverse g i, ← sideLoop_class_b_inverse g i]
  simp only [sideLoop_eq_segment]
  change loopClass (segmentLoop g (sideAngle g i 0) (sideAngle g i 1) _ _) *
      loopClass (segmentLoop g (sideAngle g i 1) (sideAngle g i 2) _ _) *
      loopClass (segmentLoop g (sideAngle g i 2) (sideAngle g i 3) _ _) *
      loopClass (segmentLoop g (sideAngle g i 3) (sideAngle g i 4) _ _) = _
  rw [segmentLoop_mul, segmentLoop_mul, segmentLoop_mul]

theorem segmentLoop_full_boundary (g : ℕ)
    (h0 : boundaryLine g 0 = basepoint g) (h1 : boundaryLine g 1 = basepoint g) :
    loopClass (segmentLoop g 0 1 h0 h1) = 1 := by
  let p : Path (boundaryPoint 0) (boundaryPoint 0) := {
    toFun := fun t => boundaryPoint (t : ℝ)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact Complex.orthonormalBasisOneI.repr.continuous.comp
        (continuous_subtype_val.comp
          (P202Specs.Topology.BasicFundamentalGroups.circleCover.continuous.comp
            continuous_subtype_val))
    source' := by simp
    target' := by simpa using boundaryPoint_one }
  have hc : ContractibleSpace (Disk 2) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).contractibleSpace
      (Metric.nonempty_closedBall.mpr zero_le_one)
  letI := hc
  have hp : loopClass p = 1 := Subsingleton.elim _ _
  let f : PointedMap (Disk 2) (Space g) (boundaryPoint 0) (basepoint g) :=
    ⟨projection g, rfl⟩
  have hh := congrArg f.induced hp
  rw [map_one] at hh
  rw [inducedFormula] at hh
  convert hh using 1
  congr 1
  ext t
  change projection g (boundaryPoint ((1-(t:ℝ))*0+(t:ℝ)*1)) =
    projection g (boundaryPoint (t:ℝ))
  simp

def handleAngle (g j : ℕ) : ℝ := (j : ℝ) / (g : ℝ)

theorem handleAngle_vertex (g : ℕ) (hg : 0 < g) (j : ℕ) (hj : j ≤ g) :
    boundaryLine g (handleAngle g j) = basepoint g := by
  have hgn : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  by_cases hlt : j < g
  · convert sideAngle_vertex g ⟨j,hlt⟩ 0 (by omega) using 1
    congr 1
    dsimp [handleAngle, sideAngle]
    field_simp
    simp
  · have hjg : j = g := by omega
    subst j
    rw [handleAngle, div_self hgn]
    change projection g (boundaryPoint 1) = basepoint g
    rw [boundaryPoint_one]
    rfl

theorem sideAngle_start (g : ℕ) (hg : 0 < g) (i : Fin g) :
    sideAngle g i 0 = handleAngle g i.val := by
  have hgn : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  dsimp [sideAngle, handleAngle]
  field_simp
  simp

theorem sideAngle_end (g : ℕ) (hg : 0 < g) (i : Fin g) :
    sideAngle g i 4 = handleAngle g (i.val+1) := by
  have hgn : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  dsimp [sideAngle, handleAngle]
  push_cast
  field_simp

theorem polygon_commutator_relation (g : ℕ) (hg : 0 < g) :
    ((List.finRange g).map fun i =>
      loopClass (sideLoop g i 0) * loopClass (sideLoop g i 1) *
        (loopClass (sideLoop g i 0))⁻¹ * (loopClass (sideLoop g i 1))⁻¹).prod = 1 := by
  let s : Fin (g + 1) → ℝ := fun j => handleAngle g j.val
  have hs : ∀ j, boundaryLine g (s j) = basepoint g :=
    fun j => handleAngle_vertex g hg j.val (by omega)
  have hp := segmentLoop_prod g g s hs
  have hf : ∀ i : Fin g,
      loopClass (sideLoop g i 0) * loopClass (sideLoop g i 1) *
        (loopClass (sideLoop g i 0))⁻¹ * (loopClass (sideLoop g i 1))⁻¹ =
        loopClass (segmentLoop g (s i.castSucc) (s i.succ) (hs _) (hs _)) := by
    intro i
    rw [handle_commutator_segment]
    congr 2
    · exact sideAngle_start g hg i
    · exact sideAngle_end g hg i
  simp_rw [hf]
  rw [← List.ofFn_eq_map, hp]
  have hgn : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hs0 : s 0 = 0 := by simp [s, handleAngle]
  have hs1 : s (Fin.last g) = 1 := by simp [s, handleAngle, hgn]
  have hz : boundaryLine g 0 = basepoint g := by
    simpa only [hs0] using hs 0
  have ho : boundaryLine g 1 = basepoint g := by
    simpa only [hs1] using hs (Fin.last g)
  have he : segmentLoop g (s 0) (s (Fin.last g)) (hs _) (hs _) =
      segmentLoop g 0 1 hz ho := by
    ext t
    simp only [segmentLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
      linearPath, Path.coe_mk_mk, hs0, hs1]
  rw [he]
  exact segmentLoop_full_boundary g hz ho

def polygonGenerator (g : ℕ) (j : SurfaceGenerator g) :
    Pi1 (Space g) (basepoint g) :=
  loopClass (sideLoop g j.1 (if j.2 then 1 else 0))

theorem polygonGenerator_relator (g : ℕ) (hg : 0 < g) :
    FreeGroup.lift (polygonGenerator g) (surfaceRelator g) = 1 := by
  unfold surfaceRelator
  rw [map_list_prod, List.map_map]
  change ((List.finRange g).map fun i =>
    FreeGroup.lift (polygonGenerator g)
      (FreeGroup.of (i, false) * FreeGroup.of (i, true) *
        (FreeGroup.of (i, false))⁻¹ * (FreeGroup.of (i, true))⁻¹)).prod = 1
  simp_rw [map_mul, map_inv, FreeGroup.lift_apply_of]
  exact polygon_commutator_relation g hg

/-- This is a genuine geometric homomorphism, not an isomorphism certificate.
It sends the abstract generators to the original paired polygon sides. -/
def presentationToPolygon (g : ℕ) (hg : 0 < g) :
    SurfacePresentation g →* Pi1 (Space g) (basepoint g) :=
  PresentedGroup.toGroup (f := polygonGenerator g) (fun r hr => by
    rw [Set.mem_singleton_iff] at hr
    rw [hr]
    exact polygonGenerator_relator g hg)

@[simp] theorem presentationToPolygon_of (g : ℕ) (hg : 0 < g)
    (j : SurfaceGenerator g) :
    presentationToPolygon g hg (PresentedGroup.of j) = polygonGenerator g j :=
  PresentedGroup.toGroup.of _


local notation "circleCover" => P202Specs.Topology.BasicFundamentalGroups.circleCover

abbrev SideDomain (g : ℕ) := (Fin g × Fin 4) × unitInterval

def subdivisionBlock {g : ℕ} (p : SideDomain g) : ℕ := 4 * p.1.1.val + p.1.2.val

def subdivisionAngle (g : ℕ) (p : SideDomain g) : ℝ :=
  ((subdivisionBlock p : ℝ) + (p.2 : ℝ)) / ((4*g : ℕ) : ℝ)

def circleSideParam (g : ℕ) : C(SideDomain g, Circle) :=
  ⟨fun p => circleCover (subdivisionAngle g p), by
    apply (circleCover).continuous.comp
    have hb : Continuous (fun ik : Fin g × Fin 4 => ((4*ik.1.val+ik.2.val:ℕ):ℝ)) :=
      continuous_of_discreteTopology
    exact ((hb.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).div_const _⟩

theorem circleSideParam_surjective (g : ℕ) (hg : 0 < g) :
    Function.Surjective (circleSideParam g) := by
  intro z
  let H := AddCircle.homeomorphCircle (T := 1) one_ne_zero
  let s := AddCircle.equivIco (1:ℝ) 0 (H.symm z)
  have hs0 : 0 ≤ s.val := s.property.1
  have hs1 : s.val < 1 := by simpa using s.property.2
  have hcover : circleCover s.val = z := by
    rw [circleCover_eq]
    change H (s.val : AddCircle (1:ℝ)) = z
    rw [AddCircle.coe_equivIco]
    exact H.apply_symm_apply z
  let M : ℝ := ((4*g : ℕ) : ℝ)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast (show 0 < 4*g by omega)
  have hx0 : 0 ≤ M * s.val := mul_nonneg hM.le hs0
  have hxM : M * s.val < M := by nlinarith
  let j := Nat.floor (M * s.val)
  have hj : j < 4*g := (Nat.floor_lt hx0).mpr hxM
  let i : Fin g := ⟨j/4, by omega⟩
  let k : Fin 4 := ⟨j%4, Nat.mod_lt _ (by norm_num)⟩
  let t : unitInterval := ⟨M*s.val-(j:ℝ),
    sub_nonneg.mpr (Nat.floor_le hx0), by
      have hh := Nat.lt_floor_add_one (M*s.val)
      dsimp [j] at *
      linarith⟩
  refine ⟨((i,k),t), ?_⟩
  change circleCover (subdivisionAngle g ((i,k),t)) = z
  rw [← hcover]
  congr 1
  have hblock : subdivisionBlock ((i,k),t) = j := by dsimp [subdivisionBlock,i,k]; omega
  dsimp [subdivisionAngle]
  rw [hblock]
  apply (div_eq_iff (ne_of_gt hM)).mpr
  change (j:ℝ) + (M*s.val-(j:ℝ)) = s.val*M
  ring

theorem circleSideParam_isQuotientMap (g : ℕ) (hg : 0 < g) :
    IsQuotientMap (circleSideParam g) :=
  (circleSideParam g).continuous.isClosedMap.isQuotientMap
    (circleSideParam g).continuous (circleSideParam_surjective g hg)

/-- Equality of covering parameters on the closed fundamental interval, when
one parameter is interior, is ordinary equality. -/
theorem circleCover_eq_of_interior {s t : ℝ}
    (hs : s ∈ Set.Ioo (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (h : circleCover s = circleCover t) : s = t := by
  have hh : (s : AddCircle (1:ℝ)) = t :=
    (AddCircle.homeomorphCircle (T:=1) one_ne_zero).injective
      ((circleCover_eq s).symm.trans (h.trans (circleCover_eq t)))
  by_cases ht1 : t < 1
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a:=0) (by simpa using ⟨hs.1.le,hs.2⟩) (by simpa using ⟨ht.1,ht1⟩)).mp hh
  · have ht0 : 0 < t := by linarith [ht.2]
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (a:=0) (by simpa using ⟨hs.1,hs.2.le⟩) (by simpa using ⟨ht0,ht.2⟩)).mp hh


theorem subdivisionBlock_lt {g : ℕ} (p : SideDomain g) : subdivisionBlock p < 4*g := by
  dsimp [subdivisionBlock]
  have hi := p.1.1.isLt
  have hk := p.1.2.isLt
  omega

theorem subdivisionAngle_mem_Icc (g : ℕ) (hg : 0 < g) (p : SideDomain g) :
    subdivisionAngle g p ∈ Set.Icc (0:ℝ) 1 := by
  have hM : (0:ℝ) < ((4*g : ℕ):ℝ) := by exact_mod_cast (show 0 < 4*g by omega)
  have hb0 : (0:ℝ) ≤ (subdivisionBlock p : ℝ) := Nat.cast_nonneg _
  have hb1 : (subdivisionBlock p : ℝ) + 1 ≤ ((4*g:ℕ):ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (subdivisionBlock_lt p)
  constructor
  · exact div_nonneg (add_nonneg hb0 p.2.property.1) hM.le
  · apply (div_le_iff₀ hM).mpr
    nlinarith [p.2.property.2]

theorem subdivisionAngle_mem_Ioo (g : ℕ) (hg : 0 < g) (p : SideDomain g)
    (hp0 : p.2 ≠ 0) (hp1 : p.2 ≠ 1) :
    subdivisionAngle g p ∈ Set.Ioo (0:ℝ) 1 := by
  have hM : (0:ℝ) < ((4*g : ℕ):ℝ) := by exact_mod_cast (show 0 < 4*g by omega)
  have hb0 : (0:ℝ) ≤ (subdivisionBlock p : ℝ) := Nat.cast_nonneg _
  have hb1 : (subdivisionBlock p : ℝ) + 1 ≤ ((4*g:ℕ):ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (subdivisionBlock_lt p)
  have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (unitInterval.pos_iff_ne_zero.mpr hp0)
  have ht1 : (p.2:ℝ) < 1 := by exact_mod_cast (unitInterval.lt_one_iff_ne_one.mpr hp1)
  constructor
  · exact div_pos (by linarith) hM
  · apply (div_lt_iff₀ hM).mpr
    nlinarith

/-- A nonvertex point of a marked boundary side belongs to exactly one side. -/
theorem circleSideParam_fiber_of_interior (g : ℕ) (hg : 0 < g)
    (p q : SideDomain g) (hp0 : p.2 ≠ 0) (hp1 : p.2 ≠ 1)
    (h : circleSideParam g p = circleSideParam g q) : p = q := by
  have ha : subdivisionAngle g p = subdivisionAngle g q :=
    circleCover_eq_of_interior (subdivisionAngle_mem_Ioo g hg p hp0 hp1)
      (subdivisionAngle_mem_Icc g hg q) h
  have hM : (((4*g : ℕ):ℝ)) ≠ 0 := by exact_mod_cast (show 4*g ≠ 0 by omega)
  have hn : (subdivisionBlock p : ℝ) + (p.2:ℝ) =
      (subdivisionBlock q : ℝ) + (q.2:ℝ) :=
    (div_left_inj' hM).mp ha
  have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (unitInterval.pos_iff_ne_zero.mpr hp0)
  have ht1 : (p.2:ℝ) < 1 := by exact_mod_cast (unitInterval.lt_one_iff_ne_one.mpr hp1)
  have hpq : subdivisionBlock p < subdivisionBlock q + 1 := by
    have : (subdivisionBlock p : ℝ) < (subdivisionBlock q : ℝ) + 1 := by
      linarith [q.2.property.2]
    exact_mod_cast this
  have hqp : subdivisionBlock q < subdivisionBlock p + 1 := by
    have : (subdivisionBlock q : ℝ) < (subdivisionBlock p : ℝ) + 1 := by
      linarith [q.2.property.1]
    exact_mod_cast this
  have hblock : subdivisionBlock p = subdivisionBlock q := by omega
  have ht : p.2 = q.2 := by
    apply Subtype.ext
    rw [hblock] at hn
    linarith
  have hi : p.1 = q.1 := by
    apply Prod.ext
    · apply Fin.ext
      dsimp [subdivisionBlock] at hblock
      have hp := p.1.2.isLt
      have hq := q.1.2.isLt
      omega
    · apply Fin.ext
      dsimp [subdivisionBlock] at hblock
      have hp := p.1.2.isLt
      have hq := q.1.2.isLt
      omega
  exact Prod.ext hi ht

theorem circleSideParam_fiber (g : ℕ) (hg : 0 < g) (p q : SideDomain g)
    (h : circleSideParam g p = circleSideParam g q) :
    p = q ∨ (p.2 = 0 ∨ p.2 = 1) ∧ (q.2 = 0 ∨ q.2 = 1) := by
  by_cases hp0 : p.2 = 0
  · by_cases hq : q.2 = 0 ∨ q.2 = 1
    · exact Or.inr ⟨Or.inl hp0,hq⟩
    · exact Or.inl (circleSideParam_fiber_of_interior g hg q p
        (fun h0 => hq (Or.inl h0)) (fun h1 => hq (Or.inr h1)) h.symm).symm
  · by_cases hp1 : p.2 = 1
    · by_cases hq : q.2 = 0 ∨ q.2 = 1
      · exact Or.inr ⟨Or.inr hp1,hq⟩
      · exact Or.inl (circleSideParam_fiber_of_interior g hg q p
          (fun h0 => hq (Or.inl h0)) (fun h1 => hq (Or.inr h1)) h.symm).symm
    · exact Or.inl (circleSideParam_fiber_of_interior g hg p q hp0 hp1 h)

/-- Continuous maps on the marked sides which share their endpoint values
descend to a continuous map on the actual boundary circle. -/
theorem circleSideParam_factors (g : ℕ) (hg : 0 < g)
    {Y : Type u} (f : SideDomain g → Y) (b : Y)
    (h0 : ∀ ik, f (ik,0) = b) (h1 : ∀ ik, f (ik,1) = b) :
    Function.FactorsThrough f (circleSideParam g) := by
  intro p q hpq
  rcases circleSideParam_fiber g hg p q hpq with rfl | ⟨hp,hq⟩
  · rfl
  · rcases p with ⟨ik,t⟩
    rcases q with ⟨jl,u⟩
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (h0 ik).trans (h0 jl).symm
    · exact (h0 ik).trans (h1 jl).symm
    · exact (h1 ik).trans (h0 jl).symm
    · exact (h1 ik).trans (h1 jl).symm



def circleIntervalParam : C(unitInterval, Circle) :=
  ⟨fun t => circleCover (t:ℝ), (circleCover).continuous.comp continuous_subtype_val⟩

theorem circleIntervalParam_surjective : Function.Surjective circleIntervalParam := by
  intro z
  let H := AddCircle.homeomorphCircle (T := 1) one_ne_zero
  let s := AddCircle.equivIco (1:ℝ) 0 (H.symm z)
  refine ⟨⟨s.val,s.property.1,by simpa using s.property.2.le⟩, ?_⟩
  change circleCover s.val = z
  rw [circleCover_eq]
  change H (s.val : AddCircle (1:ℝ)) = z
  rw [AddCircle.coe_equivIco]
  exact H.apply_symm_apply z

theorem circleIntervalParam_isQuotientMap : IsQuotientMap circleIntervalParam :=
  circleIntervalParam.continuous.isClosedMap.isQuotientMap
    circleIntervalParam.continuous circleIntervalParam_surjective

theorem circleIntervalParam_factors {Y : Type u} [TopologicalSpace Y] {y : Y}
    (p : Path y y) : Function.FactorsThrough p circleIntervalParam := by
  have hinterior : ∀ t u : unitInterval, t ≠ 0 → t ≠ 1 →
      circleIntervalParam t = circleIntervalParam u → t = u := by
    intro t u ht0 ht1 h
    apply Subtype.ext
    apply circleCover_eq_of_interior _ u.property h
    exact ⟨by exact_mod_cast unitInterval.pos_iff_ne_zero.mpr ht0,
      by exact_mod_cast unitInterval.lt_one_iff_ne_one.mpr ht1⟩
  intro t u h
  by_cases ht : t = 0 ∨ t = 1
  · by_cases hu : u = 0 ∨ u = 1
    · rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;> simp
    · rw [hinterior u t (fun h0 => hu (Or.inl h0)) (fun h1 => hu (Or.inr h1)) h.symm]
  · rw [hinterior t u (fun h0 => ht (Or.inl h0)) (fun h1 => ht (Or.inr h1)) h]

/-- A continuous loop as a map from the actual complex unit circle. -/
def loopCircle {Y : Type u} [TopologicalSpace Y] {y : Y} (p : Path y y) : C(Circle,Y) :=
  circleIntervalParam_isQuotientMap.lift p.toContinuousMap (circleIntervalParam_factors p)

@[simp] theorem loopCircle_cover {Y : Type u} [TopologicalSpace Y] {y : Y}
    (p : Path y y) (t : unitInterval) : loopCircle p (circleCover (t:ℝ)) = p t :=
  DFunLike.congr_fun (circleIntervalParam_isQuotientMap.lift_comp p.toContinuousMap
    (circleIntervalParam_factors p)) t

@[simp] theorem boundaryCover_zero : circleCover 0 = 1 := by
  simp [P202Specs.Topology.BasicFundamentalGroups.circleCover]

@[simp] theorem boundaryCover_one : circleCover 1 = 1 := by
  simp [P202Specs.Topology.BasicFundamentalGroups.circleCover, Circle.exp_two_pi]

@[simp] theorem loopCircle_one {Y : Type u} [TopologicalSpace Y] {y : Y}
    (p : Path y y) : loopCircle p 1 = y := by
  simpa only [Set.Icc.coe_zero, boundaryCover_zero, Path.source] using loopCircle_cover p 0

def sideLabel {g : ℕ} (ik : Fin g × Fin 4) : SurfaceGenerator g :=
  (ik.1, decide (ik.2.val % 2 = 1))

def sidePhase {g : ℕ} (ik : Fin g × Fin 4) : C(unitInterval,ℝ) :=
  if ik.2.val < 2 then ⟨Subtype.val,continuous_subtype_val⟩
  else ⟨fun t => 1-(t:ℝ),continuous_const.sub continuous_subtype_val⟩

def sideBouquetRaw (g : ℕ) : C(SideDomain g, SurfaceBouquet.Space g) :=
  ⟨fun p => SurfaceBouquet.circleInclusion g (sideLabel p.1)
    (circleCover (sidePhase p.1 p.2)), by
    apply continuous_prod_of_discrete_left.mpr
    intro ik
    exact (SurfaceBouquet.circleInclusion g (sideLabel ik)).continuous.comp
      ((circleCover).continuous.comp (sidePhase ik).continuous)⟩

@[simp] theorem sideBouquetRaw_zero (g : ℕ) (ik : Fin g × Fin 4) :
    sideBouquetRaw g (ik,0) = SurfaceBouquet.basepoint g := by
  rcases ik with ⟨i,k⟩
  fin_cases k <;> simp [sideBouquetRaw,sidePhase,sideLabel]

@[simp] theorem sideBouquetRaw_one (g : ℕ) (ik : Fin g × Fin 4) :
    sideBouquetRaw g (ik,1) = SurfaceBouquet.basepoint g := by
  rcases ik with ⟨i,k⟩
  fin_cases k <;> simp [sideBouquetRaw,sidePhase,sideLabel]

def attachingCircle (g : ℕ) (hg : 0 < g) : C(Circle, SurfaceBouquet.Space g) :=
  (circleSideParam_isQuotientMap g hg).lift (sideBouquetRaw g)
    (circleSideParam_factors g hg (sideBouquetRaw g) (SurfaceBouquet.basepoint g)
      (sideBouquetRaw_zero g) (sideBouquetRaw_one g))

@[simp] theorem attachingCircle_side (g : ℕ) (hg : 0 < g) (p : SideDomain g) :
    attachingCircle g hg (circleSideParam g p) = sideBouquetRaw g p :=
  DFunLike.congr_fun ((circleSideParam_isQuotientMap g hg).lift_comp (sideBouquetRaw g)
    (circleSideParam_factors g hg (sideBouquetRaw g) (SurfaceBouquet.basepoint g)
      (sideBouquetRaw_zero g) (sideBouquetRaw_one g))) p

def polygonAttachingMap (g : ℕ) (hg : 0 < g) : C(Sphere 2, SurfaceBouquet.Space g) :=
  (attachingCircle g hg).comp
    ⟨euclideanBoundaryCircleHomeomorph,euclideanBoundaryCircleHomeomorph.continuous⟩

def markedSphere (g : ℕ) (p : SideDomain g) : Sphere 2 :=
  euclideanBoundaryCircleHomeomorph.symm (circleSideParam g p)

@[simp] theorem polygonAttachingMap_markedSphere (g : ℕ) (hg : 0 < g) (p : SideDomain g) :
    polygonAttachingMap g hg (markedSphere g p) = sideBouquetRaw g p := by
  change attachingCircle g hg
    (euclideanBoundaryCircleHomeomorph (euclideanBoundaryCircleHomeomorph.symm _)) = _
  rw [Homeomorph.apply_symm_apply,attachingCircle_side]

theorem markedSphere_surjective (g : ℕ) (hg : 0 < g) : Function.Surjective (markedSphere g) :=
  euclideanBoundaryCircleHomeomorph.symm.surjective.comp (circleSideParam_surjective g hg)

@[simp] theorem markedSphere_boundary (g : ℕ) (i : Fin g) (k : Fin 4) (t : unitInterval) :
    boundaryInclusion 2 (markedSphere g ((i,k),t)) = SurfacePolygon.sidePoint g i k t := by
  apply Subtype.ext
  change Complex.orthonormalBasisOneI.repr
    (circleCover (subdivisionAngle g ((i,k),t)) : ℂ) =
    Complex.orthonormalBasisOneI.repr
    (circleCover ((4*(i.val:ℝ)+(k.val:ℝ)+(t:ℝ))/(4*(g:ℝ))) : ℂ)
  congr 2
  simp [subdivisionAngle,subdivisionBlock,Nat.cast_add,Nat.cast_mul]


def bouquetToPolygon (g : ℕ) (hg : 0 < g) : C(SurfaceBouquet.Space g, Space g) :=
  SurfaceBouquet.descendCircles g hg
    (fun j => loopCircle (sideLoop g j.1 (if j.2 then 1 else 0)))
    (basepoint g) (fun _ => loopCircle_one _)

@[simp] theorem bouquetToPolygon_a (g : ℕ) (hg : 0 < g) (i : Fin g) (t : unitInterval) :
    bouquetToPolygon g hg (SurfaceBouquet.circleInclusion g (i,false) (circleCover (t:ℝ))) =
      projection g (sidePoint g i 0 t) := by
  simp [bouquetToPolygon]

@[simp] theorem bouquetToPolygon_b (g : ℕ) (hg : 0 < g) (i : Fin g) (t : unitInterval) :
    bouquetToPolygon g hg (SurfaceBouquet.circleInclusion g (i,true) (circleCover (t:ℝ))) =
      projection g (sidePoint g i 1 t) := by
  simp [bouquetToPolygon]

theorem bouquetToPolygon_attaching (g : ℕ) (hg : 0 < g) (z : Sphere 2) :
    bouquetToPolygon g hg (polygonAttachingMap g hg z) = projection g (boundaryInclusion 2 z) := by
  obtain ⟨⟨⟨i,k⟩,t⟩,rfl⟩ := markedSphere_surjective g hg z
  rw [polygonAttachingMap_markedSphere,markedSphere_boundary]
  fin_cases k
  · simpa [sideBouquetRaw,sidePhase,sideLabel] using bouquetToPolygon_a g hg i t
  · simpa [sideBouquetRaw,sidePhase,sideLabel] using bouquetToPolygon_b g hg i t
  · simpa [sideBouquetRaw,sidePhase,sideLabel,unitInterval.coe_symm_eq] using
      (bouquetToPolygon_a g hg i (unitInterval.symm t)).trans
        (projection_side_a g i (unitInterval.symm t))
  · simpa [sideBouquetRaw,sidePhase,sideLabel,unitInterval.coe_symm_eq] using
      (bouquetToPolygon_b g hg i (unitInterval.symm t)).trans
        (projection_side_b g i (unitInterval.symm t))

@[simp] theorem characteristic_marked_side (g : ℕ) (hg : 0 < g)
    (i : Fin g) (k : Fin 4) (t : unitInterval) :
    DiskAttachment.characteristic (polygonAttachingMap g hg) (sidePoint g i k t) =
      DiskAttachment.inclusion (polygonAttachingMap g hg) (sideBouquetRaw g ((i,k),t)) := by
  rw [← markedSphere_boundary, ← DiskAttachmentProof.glue,
    polygonAttachingMap_markedSphere]

theorem characteristic_sides_a (g : ℕ) (hg : 0 < g) (i : Fin g) (t : unitInterval) :
    DiskAttachment.characteristic (polygonAttachingMap g hg) (sidePoint g i 0 t) =
      DiskAttachment.characteristic (polygonAttachingMap g hg)
        (sidePoint g i 2 (unitInterval.symm t)) := by
  rw [characteristic_marked_side,characteristic_marked_side]
  congr 1
  simp [sideBouquetRaw,sidePhase,sideLabel,unitInterval.coe_symm_eq]

theorem characteristic_sides_b (g : ℕ) (hg : 0 < g) (i : Fin g) (t : unitInterval) :
    DiskAttachment.characteristic (polygonAttachingMap g hg) (sidePoint g i 1 t) =
      DiskAttachment.characteristic (polygonAttachingMap g hg)
        (sidePoint g i 3 (unitInterval.symm t)) := by
  rw [characteristic_marked_side,characteristic_marked_side]
  congr 1
  simp [sideBouquetRaw,sidePhase,sideLabel,unitInterval.coe_symm_eq]

theorem characteristic_factors (g : ℕ) (hg : 0 < g) :
    Function.FactorsThrough (DiskAttachment.characteristic (polygonAttachingMap g hg))
      (projection g) := by
  intro p q h
  have hh : setoid g p q := Quotient.exact h
  clear h
  induction hh with
  | rel p q h =>
    cases h with
    | a i t => exact characteristic_sides_a g hg i t
    | b i t => exact characteristic_sides_b g hg i t
  | refl p => rfl
  | symm p q h ih => exact ih.symm
  | trans p q r h h' ih ih' => exact ih.trans ih'

def polygonToAttachment (g : ℕ) (hg : 0 < g) :
    C(Space g, DiskAttachment.Space (polygonAttachingMap g hg)) :=
  (isQuotientMap_quotient_mk' : IsQuotientMap (projection g)).lift
    (DiskAttachment.characteristic (polygonAttachingMap g hg)) (characteristic_factors g hg)

@[simp] theorem polygonToAttachment_projection (g : ℕ) (hg : 0 < g) (z : Disk 2) :
    polygonToAttachment g hg (projection g z) =
      DiskAttachment.characteristic (polygonAttachingMap g hg) z :=
  DFunLike.congr_fun ((isQuotientMap_quotient_mk' : IsQuotientMap (projection g)).lift_comp
    (DiskAttachment.characteristic (polygonAttachingMap g hg)) (characteristic_factors g hg)) z

def attachmentToPolygon (g : ℕ) (hg : 0 < g) :
    C(DiskAttachment.Space (polygonAttachingMap g hg), Space g) :=
  DiskAttachmentProof.descend (polygonAttachingMap g hg) (bouquetToPolygon g hg) (projection g)
    (bouquetToPolygon_attaching g hg)

@[simp] theorem attachmentToPolygon_characteristic (g : ℕ) (hg : 0 < g) (z : Disk 2) :
    attachmentToPolygon g hg (DiskAttachment.characteristic (polygonAttachingMap g hg) z) =
      projection g z := rfl

@[simp] theorem attachmentToPolygon_inclusion (g : ℕ) (hg : 0 < g) (y : SurfaceBouquet.Space g) :
    attachmentToPolygon g hg (DiskAttachment.inclusion (polygonAttachingMap g hg) y) =
      bouquetToPolygon g hg y := rfl



theorem polygonToAttachment_bouquet (g : ℕ) (hg : 0 < g) (y : SurfaceBouquet.Space g) :
    polygonToAttachment g hg (bouquetToPolygon g hg y) =
      DiskAttachment.inclusion (polygonAttachingMap g hg) y := by
  obtain ⟨⟨⟨i,b⟩,z⟩,hz⟩ := SurfaceBouquet.circleProjection_surjective g hg y
  rw [← hz]
  change polygonToAttachment g hg
    (bouquetToPolygon g hg (SurfaceBouquet.circleInclusion g (i,b) z)) =
      DiskAttachment.inclusion (polygonAttachingMap g hg)
        (SurfaceBouquet.circleInclusion g (i,b) z)
  obtain ⟨t,ht⟩ := circleIntervalParam_surjective z
  rw [← ht]
  change polygonToAttachment g hg
    (bouquetToPolygon g hg (SurfaceBouquet.circleInclusion g (i,b) (circleCover (t:ℝ)))) = _
  cases b
  · rw [bouquetToPolygon_a,polygonToAttachment_projection,characteristic_marked_side]
    congr 1
  · rw [bouquetToPolygon_b,polygonToAttachment_projection,characteristic_marked_side]
    congr 1

@[simp] theorem attachmentToPolygon_polygonToAttachment (g : ℕ) (hg : 0 < g) (y : Space g) :
    attachmentToPolygon g hg (polygonToAttachment g hg y) = y := by
  induction y using Quotient.inductionOn with
  | h z =>
    change attachmentToPolygon g hg (polygonToAttachment g hg (projection g z)) = projection g z
    rw [polygonToAttachment_projection,attachmentToPolygon_characteristic]

@[simp] theorem polygonToAttachment_attachmentToPolygon (g : ℕ) (hg : 0 < g)
    (y : DiskAttachment.Space (polygonAttachingMap g hg)) :
    polygonToAttachment g hg (attachmentToPolygon g hg y) = y := by
  induction y using Quotient.inductionOn with
  | h p =>
    cases p with
    | inl b =>
      change polygonToAttachment g hg
        (attachmentToPolygon g hg (DiskAttachment.inclusion (polygonAttachingMap g hg) b)) = _
      rw [attachmentToPolygon_inclusion,polygonToAttachment_bouquet]
      rfl
    | inr z =>
      change polygonToAttachment g hg
        (attachmentToPolygon g hg (DiskAttachment.characteristic (polygonAttachingMap g hg) z)) = _
      rw [attachmentToPolygon_characteristic,polygonToAttachment_projection]
      rfl

/-- The original paired polygon quotient is exactly a disk attached to the
actual finite bouquet, with the specified boundary parametrization. -/
def polygonAttachmentHomeomorph (g : ℕ) (hg : 0 < g) :
    Space g ≃ₜ DiskAttachment.Space (polygonAttachingMap g hg) where
  toFun := polygonToAttachment g hg
  invFun := attachmentToPolygon g hg
  left_inv := attachmentToPolygon_polygonToAttachment g hg
  right_inv := polygonToAttachment_attachmentToPolygon g hg
  continuous_toFun := (polygonToAttachment g hg).continuous
  continuous_invFun := (attachmentToPolygon g hg).continuous

@[simp] theorem bouquetToPolygon_basepoint (g : ℕ) (hg : 0 < g) :
    bouquetToPolygon g hg (SurfaceBouquet.basepoint g) = basepoint g := by
  rw [← SurfaceBouquet.circleInclusion_one g (⟨0,hg⟩,false)]
  unfold bouquetToPolygon
  rw [SurfaceBouquet.descendCircles_circle,loopCircle_one]

@[simp] theorem polygonAttachmentHomeomorph_basepoint (g : ℕ) (hg : 0 < g) :
    polygonAttachmentHomeomorph g hg (basepoint g) =
      DiskAttachment.inclusion (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g) := by
  change polygonToAttachment g hg (projection g (boundaryPoint 0)) = _
  rw [polygonToAttachment_projection]
  have he : boundaryPoint 0 = sidePoint g ⟨0,hg⟩ 0 0 := by simp [sidePoint]
  rw [he,characteristic_marked_side,sideBouquetRaw_zero]

@[simp] theorem attachmentToPolygon_circle_a (g : ℕ) (hg : 0 < g)
    (i : Fin g) (t : unitInterval) :
    attachmentToPolygon g hg (DiskAttachment.inclusion (polygonAttachingMap g hg)
      (SurfaceBouquet.circleInclusion g (i,false) (circleCover (t:ℝ)))) =
      projection g (sidePoint g i 0 t) := by
  rw [attachmentToPolygon_inclusion,bouquetToPolygon_a]

@[simp] theorem attachmentToPolygon_circle_b (g : ℕ) (hg : 0 < g)
    (i : Fin g) (t : unitInterval) :
    attachmentToPolygon g hg (DiskAttachment.inclusion (polygonAttachingMap g hg)
      (SurfaceBouquet.circleInclusion g (i,true) (circleCover (t:ℝ)))) =
      projection g (sidePoint g i 1 t) := by
  rw [attachmentToPolygon_inclusion,bouquetToPolygon_b]


def polygonAttachmentPi1Equiv (g : ℕ) (hg : 0 < g) :
    Pi1 (DiskAttachment.Space (polygonAttachingMap g hg))
      (DiskAttachment.inclusion (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g)) ≃*
        Pi1 (Space g) (basepoint g) :=
  pointedHomeomorphEquiv (polygonAttachmentHomeomorph g hg).symm
    (DiskAttachment.inclusion (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g))
    (basepoint g) (by
      change attachmentToPolygon g hg
        (DiskAttachment.inclusion (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g)) = _
      rw [attachmentToPolygon_inclusion,bouquetToPolygon_basepoint])

@[simp] theorem polygonAttachmentPi1Equiv_generator (g : ℕ) (hg : 0 < g)
    (j : SurfaceGenerator g) :
    polygonAttachmentPi1Equiv g hg
      ((DiskAttachment.pointedInclusion (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g)).induced
        (loopClass (SurfaceBouquet.edgeLoop g j))) = polygonGenerator g j := by
  change (⟨⟨(polygonAttachmentHomeomorph g hg).symm,
      (polygonAttachmentHomeomorph g hg).symm.continuous⟩, _⟩ :
        PointedMap (DiskAttachment.Space (polygonAttachingMap g hg)) (Space g)
          (DiskAttachment.inclusion (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g))
          (basepoint g)).induced
    ((DiskAttachment.pointedInclusion (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g)).induced
      (loopClass (SurfaceBouquet.edgeLoop g j))) = _
  rw [← MonoidHom.comp_apply, ← induced_comp, inducedFormula]
  unfold polygonGenerator
  congr 1
  ext t
  rcases j with ⟨i,b⟩
  cases b
  · exact attachmentToPolygon_circle_a g hg i t
  · exact attachmentToPolygon_circle_b g hg i t


end SurfacePolygonProof

namespace MappedSegments
variable {Y : Type u} [TopologicalSpace Y]

def loop (f : C(ℝ,Y)) (b : Y) (s t : ℝ) (hs : f s = b) (ht : f t = b) : Path b b :=
  ((SurfacePolygonProof.linearPath s t).map f.continuous).cast hs.symm ht.symm

theorem mul (f : C(ℝ,Y)) (b : Y) (s t r : ℝ)
    (hs : f s = b) (ht : f t = b) (hr : f r = b) :
    loopClass (loop f b s t hs ht) * loopClass (loop f b t r ht hr) =
      loopClass (loop f b s r hs hr) := by
  apply pathClass_injective
  rw [pathClass_mul, pathClass_loopClass, pathClass_loopClass, pathClass_loopClass,
    ← Path.Homotopic.Quotient.mk_trans]
  apply Path.Homotopic.Quotient.eq.mpr
  have h : ((SurfacePolygonProof.linearPath s t).trans
      (SurfacePolygonProof.linearPath t r)).Homotopic (SurfacePolygonProof.linearPath s r) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hh := (h.map f).pathCast hs.symm hr.symm
  rw [Path.map_trans] at hh
  exact hh

@[simp] theorem self (f : C(ℝ,Y)) (b : Y) (s : ℝ) (hs : f s = b) :
    loop f b s s hs hs = Path.refl b := by
  ext t
  change f ((1-(t:ℝ))*s+(t:ℝ)*s) = b
  rw [show (1-(t:ℝ))*s+(t:ℝ)*s=s by ring]
  exact hs

theorem prod (f : C(ℝ,Y)) (b : Y) (n : ℕ) (s : Fin (n+1) → ℝ)
    (hs : ∀ k, f (s k) = b) :
    (List.ofFn fun k : Fin n => loopClass
      (loop f b (s k.castSucc) (s k.succ) (hs _) (hs _))).prod =
      loopClass (loop f b (s 0) (s (Fin.last n)) (hs _) (hs _)) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Fin.last_zero, self]
    exact ((groupConvention Y b).2.1).symm
  | succ n ih =>
    rw [List.ofFn_succ',List.prod_concat]
    have hh := ih (s ∘ Fin.castSucc) (fun k => hs _)
    dsimp only [Function.comp_apply] at hh
    simp only [Fin.castSucc_succ] at hh
    rw [hh]
    exact mul f b _ _ _ (hs _) (hs _) (hs _)

end MappedSegments

namespace SurfacePolygonProof
open P202Specs.Topology.BasicFundamentalGroups

def attachingCurve (g : ℕ) (hg : 0 < g) : C(ℝ,SurfaceBouquet.Space g) :=
  (attachingCircle g hg).comp circleCover

theorem attachingCurve_side (g : ℕ) (hg : 0 < g) (i : Fin g) (k : Fin 4)
    (t : unitInterval) :
    attachingCurve g hg ((4*(i.val:ℝ)+(k.val:ℝ)+(t:ℝ))/(4*(g:ℝ))) =
      sideBouquetRaw g ((i,k),t) := by
  have he : (4*(i.val:ℝ)+(k.val:ℝ)+(t:ℝ))/(4*(g:ℝ)) =
      subdivisionAngle g ((i,k),t) := by
    simp [subdivisionAngle,subdivisionBlock,Nat.cast_add,Nat.cast_mul]
  change attachingCircle g hg (circleCover _) = _
  rw [he]
  exact attachingCircle_side g hg ((i,k),t)

def bouquetSideLoop (g : ℕ) (i : Fin g) (k : Fin 4) :
    Path (SurfaceBouquet.basepoint g) (SurfaceBouquet.basepoint g) where
  toFun t := sideBouquetRaw g ((i,k),t)
  continuous_toFun := (sideBouquetRaw g).continuous.comp
    (continuous_const.prodMk continuous_id)
  source' := sideBouquetRaw_zero g (i,k)
  target' := sideBouquetRaw_one g (i,k)

@[simp] theorem bouquetSideLoop_a (g : ℕ) (i : Fin g) :
    bouquetSideLoop g i 0 = SurfaceBouquet.edgeLoop g (i,false) := by
  ext t
  simp [bouquetSideLoop,sideBouquetRaw,sideLabel,sidePhase,SurfaceBouquet.edgeLoop]

@[simp] theorem bouquetSideLoop_b (g : ℕ) (i : Fin g) :
    bouquetSideLoop g i 1 = SurfaceBouquet.edgeLoop g (i,true) := by
  ext t
  simp [bouquetSideLoop,sideBouquetRaw,sideLabel,sidePhase,SurfaceBouquet.edgeLoop]

@[simp] theorem bouquetSideLoop_a_inv (g : ℕ) (i : Fin g) :
    bouquetSideLoop g i 2 = (SurfaceBouquet.edgeLoop g (i,false)).symm := by
  ext t
  simp [bouquetSideLoop,sideBouquetRaw,sideLabel,sidePhase,SurfaceBouquet.edgeLoop,
    Path.symm_apply, Function.comp_apply]

@[simp] theorem bouquetSideLoop_b_inv (g : ℕ) (i : Fin g) :
    bouquetSideLoop g i 3 = (SurfaceBouquet.edgeLoop g (i,true)).symm := by
  ext t
  simp [bouquetSideLoop,sideBouquetRaw,sideLabel,sidePhase,SurfaceBouquet.edgeLoop,
    Path.symm_apply, Function.comp_apply]

theorem attachingCurve_sideAngle (g : ℕ) (hg : 0 < g) (i : Fin g)
    (k : ℕ) (hk : k ≤ 4) :
    attachingCurve g hg (sideAngle g i k) = SurfaceBouquet.basepoint g := by
  by_cases hlt : k < 4
  · have hh := attachingCurve_side g hg i ⟨k,hlt⟩ 0
    simpa [sideAngle] using hh.trans (sideBouquetRaw_zero g (i,⟨k,hlt⟩))
  · have hkeq : k = 4 := by omega
    subst k
    have hh := attachingCurve_side g hg i 3 1
    have he : (4*(i.val:ℝ)+(3:ℝ)+(1:ℝ))/(4*(g:ℝ)) = sideAngle g i 4 := by
      unfold sideAngle
      push_cast
      ring
    have hhh := hh.trans (sideBouquetRaw_one g (i,3))
    change attachingCurve g hg ((4*(i.val:ℝ)+(3:ℝ)+(1:ℝ))/(4*(g:ℝ))) = _ at hhh
    rw [he] at hhh
    exact hhh

theorem bouquetSideLoop_segment (g : ℕ) (hg : 0 < g) (i : Fin g) (k : Fin 4) :
    bouquetSideLoop g i k = MappedSegments.loop (attachingCurve g hg)
      (SurfaceBouquet.basepoint g) (sideAngle g i k.val) (sideAngle g i (k.val+1))
      (attachingCurve_sideAngle g hg i k.val (by omega))
      (attachingCurve_sideAngle g hg i (k.val+1) (by omega)) := by
  ext t
  change sideBouquetRaw g ((i,k),t) = attachingCurve g hg
    ((1-(t:ℝ))*sideAngle g i k.val+(t:ℝ)*sideAngle g i (k.val+1))
  have he : (1-(t:ℝ))*sideAngle g i k.val+(t:ℝ)*sideAngle g i (k.val+1) =
      (4*(i.val:ℝ)+(k.val:ℝ)+(t:ℝ))/(4*(g:ℝ)) := by
    simp only [sideAngle,Nat.cast_add,Nat.cast_one]
    ring
  rw [he]
  exact (attachingCurve_side g hg i k t).symm

theorem bouquet_commutator_segment (g : ℕ) (hg : 0 < g) (i : Fin g) :
    loopClass (SurfaceBouquet.edgeLoop g (i,false)) *
      loopClass (SurfaceBouquet.edgeLoop g (i,true)) *
      (loopClass (SurfaceBouquet.edgeLoop g (i,false)))⁻¹ *
      (loopClass (SurfaceBouquet.edgeLoop g (i,true)))⁻¹ =
      loopClass (MappedSegments.loop (attachingCurve g hg) (SurfaceBouquet.basepoint g)
        (sideAngle g i 0) (sideAngle g i 4)
        (attachingCurve_sideAngle g hg i 0 (by omega))
        (attachingCurve_sideAngle g hg i 4 (by omega))) := by
  rw [← loopClass_inv, ← loopClass_inv]
  rw [← bouquetSideLoop_a_inv, ← bouquetSideLoop_b_inv]
  rw [← bouquetSideLoop_a, ← bouquetSideLoop_b]
  simp only [bouquetSideLoop_segment g hg]
  change loopClass (MappedSegments.loop _ _ (sideAngle g i 0) (sideAngle g i 1) _ _) *
      loopClass (MappedSegments.loop _ _ (sideAngle g i 1) (sideAngle g i 2) _ _) *
      loopClass (MappedSegments.loop _ _ (sideAngle g i 2) (sideAngle g i 3) _ _) *
      loopClass (MappedSegments.loop _ _ (sideAngle g i 3) (sideAngle g i 4) _ _) = _
  rw [MappedSegments.mul, MappedSegments.mul, MappedSegments.mul]

theorem attachingCurve_handleAngle (g : ℕ) (hg : 0 < g) (j : ℕ) (hj : j ≤ g) :
    attachingCurve g hg (handleAngle g j) = SurfaceBouquet.basepoint g := by
  have hgn : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  by_cases hlt : j < g
  · convert attachingCurve_sideAngle g hg ⟨j,hlt⟩ 0 (by omega) using 1
    congr 1
    dsimp [handleAngle,sideAngle]
    field_simp
    simp
  · have hjg : j = g := by omega
    subst j
    rw [handleAngle,div_self hgn]
    have he : attachingCurve g hg 1 = attachingCurve g hg 0 := by
      unfold attachingCurve
      simp [circleCover,Circle.exp_two_pi]
    rw [he]
    simpa [sideAngle] using attachingCurve_sideAngle g hg ⟨0,hg⟩ 0 (by omega)

theorem bouquet_boundary_word (g : ℕ) (hg : 0 < g)
    (Φ : FreeGroup (SurfaceGenerator g) ≃*
      Pi1 (SurfaceBouquet.Space g) (SurfaceBouquet.basepoint g))
    (hΦ : ∀ j, Φ (FreeGroup.of j) = loopClass (SurfaceBouquet.edgeLoop g j)) :
    Φ (surfaceRelator g) = loopClass
      (MappedSegments.loop (attachingCurve g hg) (SurfaceBouquet.basepoint g) 0 1
        (by simpa [handleAngle] using attachingCurve_handleAngle g hg 0 (by omega))
        (by
          have hgn : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
          simpa [handleAngle,hgn] using attachingCurve_handleAngle g hg g (by omega))) := by
  let s : Fin (g+1) → ℝ := fun j => handleAngle g j.val
  have hs : ∀ j, attachingCurve g hg (s j) = SurfaceBouquet.basepoint g :=
    fun j => attachingCurve_handleAngle g hg j.val (by omega)
  have hp := MappedSegments.prod (attachingCurve g hg) (SurfaceBouquet.basepoint g) g s hs
  have hf : ∀ i : Fin g,
      loopClass (SurfaceBouquet.edgeLoop g (i,false)) *
        loopClass (SurfaceBouquet.edgeLoop g (i,true)) *
        (loopClass (SurfaceBouquet.edgeLoop g (i,false)))⁻¹ *
        (loopClass (SurfaceBouquet.edgeLoop g (i,true)))⁻¹ =
        loopClass (MappedSegments.loop (attachingCurve g hg) (SurfaceBouquet.basepoint g)
          (s i.castSucc) (s i.succ) (hs _) (hs _)) := by
    intro i
    rw [bouquet_commutator_segment g hg i]
    congr 2
    · exact sideAngle_start g hg i
    · exact sideAngle_end g hg i
  unfold surfaceRelator
  rw [map_list_prod,List.map_map]
  change ((List.finRange g).map fun i =>
    Φ (FreeGroup.of (i,false) * FreeGroup.of (i,true) *
      (FreeGroup.of (i,false))⁻¹ * (FreeGroup.of (i,true))⁻¹)).prod = _
  simp_rw [map_mul,map_inv,hΦ,hf]
  rw [← List.ofFn_eq_map,hp]
  have hgn : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  congr 2 <;> simp [s,handleAngle,hgn]

theorem changeBasepoint_constantPath {Y : Type*} [TopologicalSpace Y]
    {b c : Y} (h : c = b) (p : Path c c) :
    changeBasepoint ((Path.refl b).cast rfl h) (loopClass p) =
      loopClass (p.cast h.symm h.symm) := by
  subst c
  apply pathClass_injective
  rw [changeBasepoint_pathClass, pathClass_loopClass]
  simp

theorem polygonAttachingMap_basepoint (g : ℕ) (hg : 0 < g) :
    polygonAttachingMap g hg (boundarySpherePoint 0) = SurfaceBouquet.basepoint g := by
  have hh := attachingCurve_handleAngle g hg 0 (by omega)
  simpa [attachingCurve,handleAngle,polygonAttachingMap,boundarySpherePoint_circle]
    using hh

def polygonAttachingBasepath (g : ℕ) (hg : 0 < g) :
    Path (SurfaceBouquet.basepoint g)
      (polygonAttachingMap g hg (boundarySpherePoint 0)) :=
  (Path.refl _).cast rfl (polygonAttachingMap_basepoint g hg)

theorem polygonAttachingHom_boundaryLoop (g : ℕ) (hg : 0 < g) :
    DiskAttachment.attachingHom (polygonAttachingMap g hg) (boundarySpherePoint 0)
      (polygonAttachingBasepath g hg) (loopClass boundarySphereLoop) =
      loopClass (MappedSegments.loop (attachingCurve g hg) (SurfaceBouquet.basepoint g) 0 1
        (by simpa [handleAngle] using attachingCurve_handleAngle g hg 0 (by omega))
        (by
          have hgn : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
          simpa [handleAngle,hgn] using attachingCurve_handleAngle g hg g (by omega))) := by
  change changeBasepoint (polygonAttachingBasepath g hg)
    ((DiskAttachment.pointedAttachingMap (polygonAttachingMap g hg) (boundarySpherePoint 0)).induced
      (loopClass boundarySphereLoop)) = _
  rw [inducedFormula]
  change changeBasepoint ((Path.refl _).cast rfl (polygonAttachingMap_basepoint g hg))
    (loopClass (boundarySphereLoop.map (polygonAttachingMap g hg).continuous)) = _
  rw [changeBasepoint_constantPath]
  congr 1
  ext t
  change polygonAttachingMap g hg (boundarySpherePoint (t:ℝ)) =
    attachingCurve g hg ((1-(t:ℝ))*0+(t:ℝ)*1)
  simp [polygonAttachingMap,attachingCurve,boundarySpherePoint_circle]

/-- The polygon's once-around attaching loop has the exact oriented product
of commutators in its actual bouquet. The basepoint path is explicitly constant. -/
theorem polygon_attaching_word (g : ℕ) (hg : 0 < g)
    (Φ : FreeGroup (SurfaceGenerator g) ≃*
      Pi1 (SurfaceBouquet.Space g) (SurfaceBouquet.basepoint g))
    (hΦ : ∀ j, Φ (FreeGroup.of j) = loopClass (SurfaceBouquet.edgeLoop g j)) :
    Φ (surfaceRelator g) =
      DiskAttachment.attachingHom (polygonAttachingMap g hg) (boundarySpherePoint 0)
        (polygonAttachingBasepath g hg) (loopClass boundarySphereLoop) :=
  (bouquet_boundary_word g hg Φ hΦ).trans (polygonAttachingHom_boundaryLoop g hg).symm

end SurfacePolygonProof

namespace SurfaceAlgebra

abbrev a : SurfacePresentation 1 := PresentedGroup.of (0, false)
abbrev b : SurfacePresentation 1 := PresentedGroup.of (0, true)

theorem surfaceRelator_one : surfaceRelator 1 =
    FreeGroup.of (0, false) * FreeGroup.of (0, true) *
      (FreeGroup.of (0, false))⁻¹ * (FreeGroup.of (0, true))⁻¹ := by
  simp [surfaceRelator, List.finRange_succ]

theorem generators_commute : Commute a b := by
  have h := PresentedGroup.one_of_mem (rels := {surfaceRelator 1})
    (Set.mem_singleton (surfaceRelator 1))
  have hw := congrArg (PresentedGroup.mk ({surfaceRelator 1} : Set _)) surfaceRelator_one
  apply commutatorElement_eq_one_iff_commute.mp
  simpa only [commutatorElement_def, map_mul, map_inv, a, b, PresentedGroup.of] using
    hw.symm.trans h

def coordinateGenerator (i : SurfaceGenerator 1) : Multiplicative (ℤ × ℤ) :=
  Multiplicative.ofAdd (if i.2 then (0, 1) else (1, 0))

def forward : SurfacePresentation 1 →* Multiplicative (ℤ × ℤ) :=
  PresentedGroup.toGroup (f := coordinateGenerator) (by
    rintro _ (rfl : _ = _)
    simp [surfaceRelator_one, coordinateGenerator])

@[simp] theorem forward_of (i : SurfaceGenerator 1) :
    forward (PresentedGroup.of i) = coordinateGenerator i :=
  PresentedGroup.toGroup.of _

/-- The inverse sends an integer pair to the corresponding two powers.
Commutativity is proved from the relator before defining this homomorphism. -/
def backward : Multiplicative (ℤ × ℤ) →* SurfacePresentation 1 where
  toFun z := a ^ z.toAdd.1 * b ^ z.toAdd.2
  map_one' := by simp
  map_mul' x y := by
    change a ^ (x.toAdd.1 + y.toAdd.1) * b ^ (x.toAdd.2 + y.toAdd.2) =
      (a ^ x.toAdd.1 * b ^ x.toAdd.2) * (a ^ y.toAdd.1 * b ^ y.toAdd.2)
    rw [zpow_add, zpow_add]
    exact (generators_commute.zpow_zpow y.toAdd.1 x.toAdd.2).mul_mul_mul_comm _ _

theorem backward_forward : backward.comp forward = MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨i, j⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  cases j <;> simp [coordinateGenerator, backward, a, b]

theorem forward_backward : forward.comp backward = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro z
  change forward (a ^ z.toAdd.1 * b ^ z.toAdd.2) = z
  rw [map_mul, map_zpow, map_zpow]
  simp only [a, b, forward_of, coordinateGenerator, Bool.false_eq_true, ↓reduceIte]
  change ((Multiplicative.ofAdd (1, 0) : Multiplicative (ℤ × ℤ)) ^ z.toAdd.1 *
    Multiplicative.ofAdd (0, 1) ^ z.toAdd.2).toAdd = z.toAdd
  simp

def torusPresentationEquiv : SurfacePresentation 1 ≃* Multiplicative (ℤ × ℤ) where
  toFun := forward
  invFun := backward
  left_inv z := DFunLike.congr_fun backward_forward z
  right_inv z := DFunLike.congr_fun forward_backward z
  map_mul' := forward.map_mul

end SurfaceAlgebra

/-- This algebraic calculation supplements the geometric cell-attachment proof. The ordered
conditional parameter is the full frozen graph proposition, without any
restriction to finite graphs. This does not identify a geometric surface. -/
theorem torusPresentationAlgebra_conditional
    (_graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u}) :
    P202Specs.Topology.AttachedCellPresentations.torusPresentationAlgebra := by
  exact ⟨SurfaceAlgebra.torusPresentationEquiv, rfl, rfl⟩


open SurfacePolygonProof

/-- Transport the actual disk-adjunction presentation to the original polygon
quotient, preserving its original oriented side generators. -/
theorem surfacePolygonPresentationOfWord
    (g : ℕ) (hg : 0 < g)
    (Φ : FreeGroup (SurfaceGenerator g) ≃* Pi1 (SurfaceBouquet.Space g) (SurfaceBouquet.basepoint g))
    (hΦ : ∀ j, Φ (FreeGroup.of j) = loopClass (SurfaceBouquet.edgeLoop g j))
    (d : Path (SurfaceBouquet.basepoint g)
      (polygonAttachingMap g hg (boundarySpherePoint 0)))
    (hword : Φ (surfaceRelator g) =
      DiskAttachment.attachingHom (polygonAttachingMap g hg) (boundarySpherePoint 0) d
        (loopClass boundarySphereLoop)) :
    ∃ e : SurfacePresentation g ≃* Pi1 (SurfacePolygon.Space g) (SurfacePolygon.basepoint g),
      ∀ j, e (PresentedGroup.of j) = polygonGenerator g j := by
  letI := SurfaceBouquet.pathConnected g
  obtain ⟨Q, hQ⟩ := presentationOfAttachedTwoDisk
    (polygonAttachingMap g hg) (SurfaceBouquet.basepoint g) d Φ (surfaceRelator g) hword
  let E := polygonAttachmentPi1Equiv g hg
  refine ⟨Q.trans E, ?_⟩
  intro j
  change E (Q (PresentedGroup.of j)) = _
  rw [hQ, hΦ]
  exact polygonAttachmentPi1Equiv_generator g hg j

theorem surfacePolygonPresentation_conditional
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u}) :
    P202Specs.Topology.AttachedCellPresentations.surfacePolygonPresentation := by
  intro g hg
  have hg' : 0 < g := by omega
  obtain ⟨Φ, hΦ⟩ := SurfaceBouquet.freeFundamentalGroup graph g hg'
  let d := polygonAttachingBasepath g hg'
  have hword := polygon_attaching_word g hg' Φ hΦ
  obtain ⟨e, he⟩ := surfacePolygonPresentationOfWord g hg' Φ hΦ d hword
  refine ⟨vertices g, e, ?_⟩
  intro i
  exact ⟨he (i, false), he (i, true)⟩

theorem torusPolygonGroup_conditional
    (graph : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u}) :
    P202Specs.Topology.AttachedCellPresentations.torusPolygonGroup := by
  obtain ⟨_, e, _⟩ := surfacePolygonPresentation_conditional graph 1 (by decide)
  exact ⟨e.symm.trans SurfaceAlgebra.torusPresentationEquiv⟩

theorem attachedDiskQuotient :
    P202Specs.Topology.AttachedCellPresentations.attachedDiskQuotient.{u} :=
  attachedDiskQuotient_conditional graphFundamentalGroup

theorem attachedTwoCell :
    P202Specs.Topology.AttachedCellPresentations.attachedTwoCell.{u} :=
  attachedTwoCell_conditional graphFundamentalGroup

theorem attachedHigherCell :
    P202Specs.Topology.AttachedCellPresentations.attachedHigherCell.{u} :=
  attachedHigherCell_conditional graphFundamentalGroup

theorem finiteCWPresentation :
    P202Specs.Topology.AttachedCellPresentations.finiteCWPresentation.{u} :=
  finiteCWPresentation_conditional graphFundamentalGroup

theorem surfacePolygonPresentation :
    P202Specs.Topology.AttachedCellPresentations.surfacePolygonPresentation :=
  surfacePolygonPresentation_conditional graphFundamentalGroup.{0}

theorem torusPolygonGroup :
    P202Specs.Topology.AttachedCellPresentations.torusPolygonGroup :=
  torusPolygonGroup_conditional graphFundamentalGroup.{0}

theorem torusPresentationAlgebra :
    P202Specs.Topology.AttachedCellPresentations.torusPresentationAlgebra :=
  torusPresentationAlgebra_conditional graphFundamentalGroup.{0}


end P202.Topology
