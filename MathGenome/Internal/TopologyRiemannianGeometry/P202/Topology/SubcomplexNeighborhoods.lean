import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SubcomplexNeighborhoods
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
The first assertion of `prop:p202-cw-neighborhood`, for arbitrary CW complexes.
The collar construction produces compatible neighborhoods and strong
deformations on all skeleta, then assembles them using the characteristic-disk
quotient and its product with the parameter interval. The construction uses
the proved structural CW results and needs no compactness assumption.
-/

noncomputable section
open Set Topology
universe u v w

namespace P202.Cellular

namespace StrongDeformationRetracts

variable {X : Type u} [TopologicalSpace X] {A W : Set X}

theorem self (A : Set X) : StrongDeformationRetracts A A := by
  refine ⟨Subset.rfl, ⟨⟨Prod.fst, continuous_fst⟩, ?_, ?_, ?_⟩⟩
  · intro x; rfl
  · intro x; exact x.2
  · intro x t _; rfl

theorem empty : StrongDeformationRetracts (∅ : Set X) ∅ := self ∅

/-- The endpoint of the homotopy is a continuous retraction with its actual
subspace codomain, including when the spaces are empty. -/
theorem exists_retraction (h : StrongDeformationRetracts A W) :
    ∃ r : C(W, A), ∀ (x : W), x.1 ∈ A → (r x).1 = x.1 := by
  rcases h with ⟨_, H, _, hone, hfix⟩
  refine ⟨⟨fun x => ⟨(H (x, 1)).1, hone x⟩, ?_⟩, ?_⟩
  · exact (continuous_subtype_val.comp
      (H.continuous.comp (continuous_id.prodMk continuous_const))).subtype_mk _
  · intro x hx
    exact congrArg Subtype.val (hfix x 1 hx)

end StrongDeformationRetracts

end P202.Cellular

namespace P202.Topology
open P202.Cellular

theorem subcomplexNeighborhood_of_isOpen
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (hA : IsOpen A.carrier) :
    ∃ W : Set X, IsOpen W ∧ StrongDeformationRetracts A.carrier W :=
  ⟨A.carrier, hA, StrongDeformationRetracts.self _⟩

theorem subcomplexNeighborhood_of_empty
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (hA : A.carrier = ∅) :
    ∃ W : Set X, IsOpen W ∧ StrongDeformationRetracts A.carrier W := by
  apply subcomplexNeighborhood_of_isOpen A
  rw [hA]
  exact isOpen_empty

theorem subcomplexNeighborhood_of_univ
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (hA : A.carrier = univ) :
    ∃ W : Set X, IsOpen W ∧ StrongDeformationRetracts A.carrier W := by
  apply subcomplexNeighborhood_of_isOpen A
  rw [hA]
  exact isOpen_univ

/-- The open-set form of the CW weak topology, derived from the actual CW
axiom rather than assuming an extra topology on the space. -/
theorem isOpen_iff_characteristic
    {X : Type u} [TopologicalSpace X] [CWStructure X] (W : Set X) :
    IsOpen W ↔ ∀ n (c : Cell X n), IsOpen (characteristic X n c ⁻¹' W) := by
  simpa only [← isClosed_compl_iff, preimage_compl] using
    (CWStructure.weak_topology (X := X) Wᶜ)

/-- A whole characteristic disk is contained in the next skeleton. -/
theorem characteristic_mem_skeletonLT
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) (x : Disk n) :
    characteristic X n c x ∈ skeletonLT X (n + 1) :=
  (diskToSkeleton X CWStructure.boundary_lands n c x).2

theorem continuous_diskToSkeleton
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) :
    Continuous (diskToSkeleton X CWStructure.boundary_lands n c) :=
  (characteristic X n c).continuous.subtype_mk _

/-- Every point lies in some finite-dimensional skeleton. No finiteness of the
number of cells is required. -/
theorem exists_mem_skeletonLT
    {X : Type u} [TopologicalSpace X] [CWStructure X] (x : X) :
    ∃ n, x ∈ skeletonLT X n := by
  have hx : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
    rw [CWStructure.cover]; trivial
  rcases mem_iUnion.mp hx with ⟨n, hx⟩
  rcases mem_iUnion.mp hx with ⟨c, hx⟩
  exact ⟨n + 1, mem_iUnion.mpr ⟨n, mem_iUnion.mpr
    ⟨Nat.lt_succ_self n, mem_iUnion.mpr ⟨c, hx⟩⟩⟩⟩

/-- Openness on every skeleton implies openness in the whole CW complex. -/
theorem isOpen_of_skeletonLT
    {X : Type u} [TopologicalSpace X] [CWStructure X] {W : Set X}
    (hW : ∀ n, IsOpen ((Subtype.val : skeletonLT X n → X) ⁻¹' W)) :
    IsOpen W := by
  apply (isOpen_iff_characteristic W).mpr
  intro n c
  exact (hW (n + 1)).preimage (continuous_diskToSkeleton n c)

/-- On an open subset of a disjoint union, continuity can be checked on each
summand. The open hypothesis permits the same argument after taking a product
with the parameter interval. -/
theorem continuousOn_sigma_iff_of_isOpen
    {ι : Type u} {D : ι → Type v} [∀ i, TopologicalSpace (D i)]
    {Y : Type w} [TopologicalSpace Y]
    {s : Set (Σ i, D i)} (hs : IsOpen s) (f : (Σ i, D i) → Y) :
    ContinuousOn f s ↔
      ∀ i, ContinuousOn (f ∘ Sigma.mk i) (Sigma.mk i ⁻¹' s) := by
  constructor
  · intro hf i
    exact hf.comp continuous_sigmaMk.continuousOn (fun _ hx => hx)
  · intro hf x hx
    rcases x with ⟨i, x⟩
    apply ContinuousAt.continuousWithinAt
    apply IsOpenEmbedding.sigmaMk.continuousAt_iff.mp
    exact (hf i).continuousAt ((hs.preimage continuous_sigmaMk).mem_nhds hx)

theorem continuousOn_sigma_prod_iff_of_isOpen
    {ι : Type u} {D : ι → Type v} [∀ i, TopologicalSpace (D i)]
    {T : Type w} [TopologicalSpace T] {Y : Type*} [TopologicalSpace Y]
    {s : Set ((Σ i, D i) × T)} (hs : IsOpen s) (f : (Σ i, D i) × T → Y) :
    ContinuousOn f s ↔ ∀ i,
      ContinuousOn (f ∘ Prod.map (Sigma.mk i) id)
        (Prod.map (Sigma.mk i) id ⁻¹' s) := by
  constructor
  · intro hf i
    exact hf.comp (continuous_sigmaMk.prodMap continuous_id).continuousOn (fun _ hx => hx)
  · intro hf x hx
    rcases x with ⟨⟨i, x⟩, t⟩
    apply ContinuousAt.continuousWithinAt
    have he : IsOpenEmbedding
        (Prod.map (Sigma.mk i : D i → Σ j, D j) (id : T → T)) :=
      IsOpenEmbedding.sigmaMk.prodMap (.id)
    apply (he.continuousAt_iff (g := f) (x := (x, t))).mp
    exact (hf i).continuousAt
      ((hs.preimage (continuous_sigmaMk.prodMap continuous_id)).mem_nhds hx)

/-- The weak topology also tests maps defined only on an open subset. This is
needed because the neighborhood being constructed need not be a subcomplex. -/
theorem continuousOn_iff_characteristic
    (hquot : P202Specs.Topology.CellStructures.characteristicProjectionQuotient.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    {Y : Type v} [TopologicalSpace Y] {W : Set X} (hW : IsOpen W) (f : X → Y) :
    ContinuousOn f W ↔ ∀ n (c : Cell X n),
      ContinuousOn (f ∘ characteristic X n c) (characteristic X n c ⁻¹' W) := by
  rw [(hquot (X := X)).continuousOn_isOpen_iff hW]
  rw [continuousOn_sigma_iff_of_isOpen (hW.preimage (hquot (X := X)).continuous)]
  apply forall_congr'
  intro n
  exact continuousOn_sigma_iff_of_isOpen
    (hW.preimage ((hquot (X := X)).continuous.comp continuous_sigmaMk)) _

/-- Local compactness of the parameter space is sufficient for products of
quotient maps with its identity. This uses the compact-open adjunction and
does not assume that the quotient map is open. -/
theorem quotientMap_prod_locallyCompact
    {P : Type u} {Q : Type v} {T : Type w}
    [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace T]
    [LocallyCompactSpace T] {q : P → Q} (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map q (id : T → T)) := by
  refine ⟨.of_isOpen_preimage_iff_isOpen (fun s => ⟨?_, ?_⟩), ?_⟩
  · intro hs
    apply isOpen_iff_continuous_mem.mpr
    apply hq.continuous_lift_prod_left
    exact isOpen_iff_continuous_mem.mp hs
  · intro hs
    exact hs.preimage (hq.continuous.prodMap continuous_id)
  · exact hq.surjective.prodMap Function.surjective_id

/-- Product version of the preceding local weak-topology test, in the ordinary
product topology. -/
theorem continuousOn_iff_characteristic_prod
    (hquot : P202Specs.Topology.CellStructures.characteristicProjectionQuotient.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    {Y : Type v} [TopologicalSpace Y] {W : Set X} (hW : IsOpen W)
    (H : X × Interval → Y) :
    ContinuousOn H (W ×ˢ univ) ↔ ∀ n (c : Cell X n),
      ContinuousOn (H ∘ Prod.map (characteristic X n c) id)
        ((characteristic X n c ⁻¹' W) ×ˢ univ) := by
  have hq := quotientMap_prod_locallyCompact (T := Interval) (hquot (X := X))
  have hWo : IsOpen (W ×ˢ (univ : Set Interval)) := hW.prod isOpen_univ
  rw [hq.continuousOn_isOpen_iff hWo]
  rw [continuousOn_sigma_prod_iff_of_isOpen (hWo.preimage hq.continuous)]
  apply forall_congr'
  intro n
  exact continuousOn_sigma_prod_iff_of_isOpen
    (hWo.preimage (hq.continuous.comp
      (continuous_sigmaMk.prodMap continuous_id))) _

/-- Data for the dimension-by-dimension construction. This is only an internal
construction interface: existence of these data is not assumed in the target
Spec. The codomain `W` records that each deformation
stays inside the eventual neighborhood. -/
structure SkeletalNeighborhoodData
    {X : Type u} [TopologicalSpace X] [CWStructure X] (A W : Set X) where
  contains : A ⊆ W
  open_on_skeleton : ∀ n, IsOpen ((Subtype.val : skeletonLT X n → X) ⁻¹' W)
  homotopy : ∀ n, C(↥(W ∩ skeletonLT X n) × Interval, W)
  compatible : ∀ m n (x : X) (hm : x ∈ W ∩ skeletonLT X m)
    (hn : x ∈ W ∩ skeletonLT X n) (t : Interval),
    homotopy m (⟨x, hm⟩, t) = homotopy n (⟨x, hn⟩, t)
  initial : ∀ n (x : ↥(W ∩ skeletonLT X n)), (homotopy n (x, 0)).1 = x.1
  terminal : ∀ n (x : ↥(W ∩ skeletonLT X n)), (homotopy n (x, 1)).1 ∈ A
  fixed : ∀ n (x : ↥(W ∩ skeletonLT X n)) (t : Interval), x.1 ∈ A →
    (homotopy n (x, t)).1 = x.1

namespace SkeletalNeighborhoodData

variable {X : Type u} [TopologicalSpace X] [CWStructure X] {A W : Set X}
    (S : SkeletalNeighborhoodData A W)

include S

theorem isOpen : IsOpen W := isOpen_of_skeletonLT S.open_on_skeleton

/-- A set-theoretic assembly, with continuity proved below. The choice of a
skeleton is immaterial by `compatible`. -/
def assembled (p : W × Interval) : W :=
  S.homotopy (Classical.choose (exists_mem_skeletonLT p.1.1))
    (⟨p.1.1, p.1.2, Classical.choose_spec (exists_mem_skeletonLT p.1.1)⟩, p.2)

theorem assembled_eq (n : ℕ) (x : ↥(W ∩ skeletonLT X n)) (t : Interval) :
    S.assembled (⟨x.1, x.2.1⟩, t) = S.homotopy n (x, t) :=
  S.compatible _ _ _ _ _ _

/-- Weak pasting on the open neighborhood. The proof tests each restricted
characteristic disk times the interval. It does not use a claim that arbitrary
products of CW complexes have the CW weak topology. -/
theorem continuous_assembled
    (hquot : P202Specs.Topology.CellStructures.characteristicProjectionQuotient.{u}) :
    Continuous S.assembled := by
  classical
  let E : X × Interval → X := fun p =>
    if hx : p.1 ∈ W then (S.assembled (⟨p.1, hx⟩, p.2)).1 else p.1
  have hE : ContinuousOn E (W ×ˢ univ) := by
    apply (continuousOn_iff_characteristic_prod hquot S.isOpen E).mpr
    intro n c
    apply continuousOn_iff_continuous_domRestrict.mpr
    let G : ((characteristic X n c ⁻¹' W) ×ˢ (univ : Set Interval)) →
        ↥(W ∩ skeletonLT X (n + 1)) × Interval := fun p =>
      (⟨characteristic X n c p.1.1,
        p.2.1, characteristic_mem_skeletonLT n c p.1.1⟩, p.1.2)
    have hG : Continuous G := by
      apply Continuous.prodMk
      · exact ((characteristic X n c).continuous.comp
          (continuous_fst.comp continuous_subtype_val)).subtype_mk _
      · exact continuous_snd.comp continuous_subtype_val
    have h := continuous_subtype_val.comp ((S.homotopy (n + 1)).continuous.comp hG)
    apply h.congr
    intro p
    simp only [domRestrict, Function.comp_apply, Prod.map, id_eq, E]
    have hp : characteristic X n c p.1.1 ∈ W := p.2.1
    rw [dite_eq_left hp]
    exact (congrArg Subtype.val (S.assembled_eq (n + 1) (G p).1 p.1.2)).symm
  have hval : Continuous (fun p : W × Interval => (S.assembled p).1) := by
    have h := hE.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.2, mem_univ _⟩)
    apply h.congr
    intro p
    dsimp [E]
    rw [dite_eq_left p.1.2]
  exact IsInducing.subtypeVal.continuous_iff.mpr hval

/-- Complete assembly from compatible skeletal data, including all endpoint,
fixed-point, and range conditions. The CW-specific collar construction below
produces these data. -/
theorem strongDeformationRetracts
    (hquot : P202Specs.Topology.CellStructures.characteristicProjectionQuotient.{u}) :
    StrongDeformationRetracts A W := by
  refine ⟨S.contains, ⟨⟨S.assembled, S.continuous_assembled hquot⟩, ?_, ?_, ?_⟩⟩
  · intro x
    apply Subtype.ext
    exact S.initial _ _
  · intro x
    exact S.terminal _ _
  · intro x t hx
    apply Subtype.ext
    exact S.fixed _ _ _ hx

end SkeletalNeighborhoodData

/-- A coherent sequence of the neighborhoods and deformations constructed on
successive skeleta. `restrict` prevents later cells from adding points of an
earlier skeleton. All topology fields use the actual ambient subspaces. -/
structure CompatibleSkeletalNeighborhoods
    {X : Type u} [TopologicalSpace X] [CWStructure X] (A : Set X) where
  carrier : ℕ → Set X
  subset_skeleton : ∀ n, carrier n ⊆ skeletonLT X n
  monotone : Monotone carrier
  restrict : ∀ m n, m ≤ n → carrier n ∩ skeletonLT X m = carrier m
  open_on_skeleton : ∀ n,
    IsOpen ((Subtype.val : skeletonLT X n → X) ⁻¹' carrier n)
  contains : ∀ n, A ∩ skeletonLT X n ⊆ carrier n
  homotopy : ∀ n, C(carrier n × Interval, carrier n)
  initial : ∀ n (x : carrier n), homotopy n (x, 0) = x
  terminal : ∀ n (x : carrier n), (homotopy n (x, 1)).1 ∈ A
  fixed : ∀ n (x : carrier n) (t : Interval), x.1 ∈ A → homotopy n (x, t) = x
  compatible : ∀ m n (hmn : m ≤ n) (x : carrier m) (t : Interval),
    (homotopy n (⟨x.1, monotone hmn x.2⟩, t)).1 = (homotopy m (x, t)).1

namespace CompatibleSkeletalNeighborhoods

variable {X : Type u} [TopologicalSpace X] [CWStructure X] {A : Set X}
    (S : CompatibleSkeletalNeighborhoods A)

include S

def unionCarrier : Set X := ⋃ n, S.carrier n

theorem subset_union (n : ℕ) : S.carrier n ⊆ S.unionCarrier :=
  subset_iUnion S.carrier n

theorem union_inter_skeleton (n : ℕ) :
    S.unionCarrier ∩ skeletonLT X n = S.carrier n := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxn⟩
    rcases mem_iUnion.mp hx with ⟨m, hxm⟩
    rcases le_total m n with hmn | hnm
    · exact S.monotone hmn hxm
    · have h : x ∈ S.carrier m ∩ skeletonLT X n := ⟨hxm, hxn⟩
      rwa [S.restrict n m hnm] at h
  · intro x hx
    exact ⟨S.subset_union n hx, S.subset_skeleton n hx⟩

theorem mem_carrier (n : ℕ) {x : X} (hx : x ∈ S.unionCarrier ∩ skeletonLT X n) :
    x ∈ S.carrier n := by
  rwa [← S.union_inter_skeleton n]

def toSkeletalData : SkeletalNeighborhoodData A S.unionCarrier where
  contains x hx := by
    obtain ⟨n, hn⟩ := exists_mem_skeletonLT x
    exact S.subset_union n (S.contains n ⟨hx, hn⟩)
  open_on_skeleton n := by
    have he : (Subtype.val : skeletonLT X n → X) ⁻¹' S.unionCarrier =
        (Subtype.val : skeletonLT X n → X) ⁻¹' S.carrier n := by
      ext x
      exact ⟨fun hx => S.mem_carrier n ⟨hx, x.2⟩, fun hx => S.subset_union n hx⟩
    rw [he]
    exact S.open_on_skeleton n
  homotopy n :=
    ⟨fun p => ⟨(S.homotopy n (⟨p.1.1, S.mem_carrier n p.1.2⟩, p.2)).1,
      S.subset_union n (S.homotopy n (⟨p.1.1, S.mem_carrier n p.1.2⟩, p.2)).2⟩, by
      apply Continuous.subtype_mk
      apply continuous_subtype_val.comp
      apply (S.homotopy n).continuous.comp
      apply Continuous.prodMk
      · exact (continuous_subtype_val.comp continuous_fst).subtype_mk _
      · exact continuous_snd⟩
  compatible m n x hm hn t := by
    apply Subtype.ext
    rcases le_total m n with hmn | hnm
    · exact (S.compatible m n hmn ⟨x, S.mem_carrier m hm⟩ t).symm
    · exact S.compatible n m hnm ⟨x, S.mem_carrier n hn⟩ t
  initial n x := congrArg Subtype.val (S.initial n ⟨x.1, S.mem_carrier n x.2⟩)
  terminal n x := S.terminal n ⟨x.1, S.mem_carrier n x.2⟩
  fixed n x t hx := congrArg Subtype.val (S.fixed n ⟨x.1, S.mem_carrier n x.2⟩ t hx)

/-- The passage from all finite-dimensional stages to an actual neighborhood
and deformation in the full CW complex. -/
theorem exists_neighborhood
    (hquot : P202Specs.Topology.CellStructures.characteristicProjectionQuotient.{u}) :
    ∃ W : Set X, IsOpen W ∧ StrongDeformationRetracts A W :=
  ⟨S.unionCarrier, S.toSkeletalData.isOpen,
    S.toSkeletalData.strongDeformationRetracts hquot⟩

end CompatibleSkeletalNeighborhoods

/-- Openness of the image of an open saturated set under a quotient map. This
is the form needed at a cell attachment, whose projection need not be open. -/
theorem isOpen_image_of_saturated
    {P : Type u} {Q : Type v} [TopologicalSpace P] [TopologicalSpace Q]
    {q : P → Q} (hq : IsQuotientMap q) {U : Set P} (hU : IsOpen U)
    (hsat : ∀ x y, q x = q y → (x ∈ U ↔ y ∈ U)) : IsOpen (q '' U) := by
  apply hq.isCoinducing.isOpen_preimage.mp
  have he : q ⁻¹' (q '' U) = U := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, he⟩
      exact (hsat y x he).mp hy
    · intro x hx
      exact mem_image_of_mem q hx
  rwa [he]

/-- Descend a continuous, fiber-compatible deformation from the preimage of an
open neighborhood through a quotient map. The range is the actual neighborhood
throughout, so this establishes a strong deformation retraction rather than
only an ambient homotopy. -/
theorem strongDeformationRetracts_of_quotient
    {P : Type u} {Q : Type v} [TopologicalSpace P] [TopologicalSpace Q]
    (q : C(P, Q)) (hq : IsQuotientMap q) {B W : Set Q}
    (hW : IsOpen W) (hBW : B ⊆ W)
    (F : C((q ⁻¹' W) × Interval, W))
    (hfiber : ∀ (x y : q ⁻¹' W) (t : Interval), q x.1 = q y.1 → F (x, t) = F (y, t))
    (hzero : ∀ x : q ⁻¹' W, (F (x, 0)).1 = q x.1)
    (hone : ∀ x : q ⁻¹' W, (F (x, 1)).1 ∈ B)
    (hfix : ∀ (x : q ⁻¹' W) (t : Interval), q x.1 ∈ B → (F (x, t)).1 = q x.1) :
    StrongDeformationRetracts B W := by
  let qW : C(q ⁻¹' W, W) := ⟨W.restrictPreimage q, (hq.restrictPreimage_isOpen hW).continuous⟩
  have hqW : IsQuotientMap qW := hq.restrictPreimage_isOpen hW
  let qWI : C((q ⁻¹' W) × Interval, W × Interval) :=
    ⟨Prod.map qW id, qW.continuous.prodMap continuous_id⟩
  have hqWI : IsQuotientMap qWI := quotientMap_prod_locallyCompact hqW
  have hfac : Function.FactorsThrough F qWI := by
    intro p p' hp
    obtain ⟨x, t⟩ := p
    obtain ⟨y, s⟩ := p'
    have hts : t = s := congrArg Prod.snd hp
    subst s
    apply hfiber x y t
    exact congrArg (fun z : W × Interval => z.1.1) hp
  let H : C(W × Interval, W) := hqWI.lift F hfac
  have hcomm : ∀ (x : q ⁻¹' W) (t : Interval), H (qW x, t) = F (x, t) := by
    intro x t
    exact congrArg (fun f : C((q ⁻¹' W) × Interval, W) => f (x, t))
      (hqWI.lift_comp F hfac)
  refine ⟨hBW, H, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := hqW.surjective x
    rw [hcomm]
    exact Subtype.ext (hzero y)
  · intro x
    obtain ⟨y, rfl⟩ := hqW.surjective x
    rw [hcomm]
    exact hone y
  · intro x t hx
    obtain ⟨y, rfl⟩ := hqW.surjective x
    rw [hcomm]
    exact Subtype.ext (hfix y t hx)

namespace Collar

/-- The outer half of the radial interval, including the boundary. -/
abbrev Radius := Set.Ioc (1 / 2 : ℝ) 1

def boundaryRadius : Radius := ⟨1, by norm_num⟩

theorem radius_pos (r : Radius) : 0 < (r : ℝ) := by
  have := r.2.1
  linarith

/-- Move radially at unit speed, stopping at the boundary. -/
def advance (r : Radius) (t : Interval) : Radius :=
  ⟨min ((r : ℝ) + t) 1, by
    constructor
    · apply lt_min
      · have := r.2.1; have := t.2.1; linarith
      · norm_num
    · exact min_le_right _ _⟩

/-- Time available for the old-skeleton homotopy after the initial radial
motion. Clamping at zero gives a continuous expression on the entire collar. -/
def remaining (r : Radius) (t : Interval) : Interval :=
  ⟨max 0 (((t : ℝ) - (1 - (r : ℝ))) / r), by
    constructor
    · exact le_max_left _ _
    · apply max_le zero_le_one
      apply (div_le_iff₀ (radius_pos r)).mpr
      have := t.2.2
      linarith⟩

theorem continuous_advance : Continuous (fun p : Radius × Interval => advance p.1 p.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)).min continuous_const

theorem continuous_remaining : Continuous (fun p : Radius × Interval => remaining p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.max continuous_const
  apply Continuous.div
  · exact (continuous_subtype_val.comp continuous_snd).sub
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
  · exact continuous_subtype_val.comp continuous_fst
  · intro p
    exact ne_of_gt (radius_pos p.1)

@[simp] theorem advance_zero (r : Radius) : advance r 0 = r := by
  apply Subtype.ext
  change min ((r : ℝ) + 0) 1 = r
  simpa only [add_zero] using min_eq_left r.2.2

theorem advance_of_late (r : Radius) (t : Interval)
    (ht : 1 - (r : ℝ) ≤ t) : advance r t = boundaryRadius := by
  apply Subtype.ext
  change min ((r : ℝ) + t) 1 = 1
  apply min_eq_right
  linarith

@[simp] theorem advance_one (r : Radius) : advance r 1 = boundaryRadius := by
  apply advance_of_late
  have := radius_pos r
  change 1 - (r : ℝ) ≤ (1 : ℝ)
  linarith

theorem remaining_of_early (r : Radius) (t : Interval)
    (ht : (t : ℝ) ≤ 1 - (r : ℝ)) : remaining r t = 0 := by
  apply Subtype.ext
  apply max_eq_left
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (radius_pos r).le

@[simp] theorem remaining_zero (r : Radius) : remaining r 0 = 0 := by
  apply remaining_of_early
  have := r.2.2
  change (0 : ℝ) ≤ 1 - (r : ℝ)
  linarith

@[simp] theorem remaining_one (r : Radius) : remaining r 1 = 1 := by
  apply Subtype.ext
  change max 0 (((1 : ℝ) - (1 - (r : ℝ))) / r) = 1
  have hr : (r : ℝ) ≠ 0 := ne_of_gt (radius_pos r)
  have he : ((1 : ℝ) - (1 - (r : ℝ))) / r = 1 := by
    field_simp
    ring
  rw [he]
  exact max_eq_right zero_le_one

@[simp] theorem remaining_boundary (t : Interval) : remaining boundaryRadius t = t := by
  apply Subtype.ext
  change max 0 (((t : ℝ) - (1 - 1)) / 1) = t
  simpa only [sub_self, sub_zero, div_one] using max_eq_right t.2.1

variable {Θ : Type u} {Y : Type v} [TopologicalSpace Θ] [TopologicalSpace Y]

/-- The source's radial-first extension in collar coordinates. Here `f` is the
characteristic map on the collar, and `h` is the old-skeleton homotopy along the
attaching directions. Both maps have the actual eventual neighborhood as their
codomain when the construction is applied to a CW pair. -/
def extend (f : C(Radius × Θ, Y)) (h : C(Θ × Interval, Y))
    (p : (Radius × Θ) × Interval) : Y := by
  classical
  exact if (p.2 : ℝ) ≤ 1 - (p.1.1 : ℝ) then
    f (advance p.1.1 p.2, p.1.2) else h (p.1.2, remaining p.1.1 p.2)

theorem continuous_extend (f : C(Radius × Θ, Y)) (h : C(Θ × Interval, Y))
    (hboundary : ∀ θ, f (boundaryRadius, θ) = h (θ, 0)) : Continuous (extend f h) := by
  classical
  have hr : Continuous (fun p : (Radius × Θ) × Interval => (p.1.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have ht : Continuous (fun p : (Radius × Θ) × Interval => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  unfold extend
  apply continuous_if_le ht (continuous_const.sub hr)
  · apply Continuous.continuousOn
    apply f.continuous.comp
    exact (continuous_advance.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
        (continuous_snd.comp continuous_fst)
  · apply Continuous.continuousOn
    apply h.continuous.comp
    exact (continuous_snd.comp continuous_fst).prodMk
      (continuous_remaining.comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  · intro p hp
    rw [advance_of_late p.1.1 p.2 hp.ge, remaining_of_early p.1.1 p.2 hp.le]
    exact hboundary p.1.2

@[simp] theorem extend_zero (f : C(Radius × Θ, Y)) (h : C(Θ × Interval, Y))
    (r : Radius) (θ : Θ) : extend f h ((r, θ), 0) = f (r, θ) := by
  have ht : (0 : ℝ) ≤ 1 - (r : ℝ) := sub_nonneg.mpr r.2.2
  simp [extend, ht]

@[simp] theorem extend_one (f : C(Radius × Θ, Y)) (h : C(Θ × Interval, Y))
    (r : Radius) (θ : Θ) : extend f h ((r, θ), 1) = h (θ, 1) := by
  have ht : ¬ (1 : ℝ) ≤ 1 - (r : ℝ) := by
    have := radius_pos r
    linarith
  simp [extend, ht]

theorem extend_boundary (f : C(Radius × Θ, Y)) (h : C(Θ × Interval, Y))
    (hboundary : ∀ θ, f (boundaryRadius, θ) = h (θ, 0))
    (θ : Θ) (t : Interval) : extend f h ((boundaryRadius, θ), t) = h (θ, t) := by
  classical
  by_cases ht : (t : ℝ) ≤ 0
  · have he : t = 0 := Subtype.ext (le_antisymm ht t.2.1)
    rw [he, extend_zero]
    exact hboundary θ
  · simpa [extend, boundaryRadius, ht] using congrArg (fun s => h (θ, s))
      (remaining_boundary t)

/-- Points of a characteristic disk with radius strictly greater than `1/2`.
For the zero-dimensional disk this type is empty. -/
abbrev OuterDisk (n : ℕ) := {x : Disk n // 1 / 2 < ‖x.1‖}

def diskRadius (n : ℕ) (x : OuterDisk n) : Radius :=
  ⟨‖x.1.1‖, x.2, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.1.2⟩

theorem norm_ne_zero (n : ℕ) (x : OuterDisk n) : ‖x.1.1‖ ≠ 0 :=
  ne_of_gt (radius_pos (diskRadius n x))

def diskDirection (n : ℕ) (x : OuterDisk n) : Sphere n :=
  ⟨‖x.1.1‖⁻¹ • x.1.1, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero n x)]⟩

def diskPoint (n : ℕ) (p : Radius × Sphere n) : Disk n :=
  ⟨(p.1 : ℝ) • p.2.1, by
    have hθ : ‖p.2.1‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.2.2
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (radius_pos p.1), hθ, mul_one]
    exact p.1.2.2⟩

@[simp] theorem norm_diskPoint (n : ℕ) (p : Radius × Sphere n) :
    ‖(diskPoint n p).1‖ = (p.1 : ℝ) := by
  have hθ : ‖p.2.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.2
  exact (norm_smul _ _).trans (by
    rw [Real.norm_eq_abs, abs_of_pos (radius_pos p.1), hθ, mul_one])

theorem diskPoint_mem_outer (n : ℕ) (p : Radius × Sphere n) :
    1 / 2 < ‖(diskPoint n p).1‖ := by
  rw [norm_diskPoint]
  exact p.1.2.1

theorem continuous_diskRadius (n : ℕ) : Continuous (diskRadius n) :=
  (continuous_subtype_val.comp continuous_subtype_val).norm.subtype_mk _

theorem continuous_diskDirection (n : ℕ) : Continuous (diskDirection n) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
    (norm_ne_zero n)).smul (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_diskPoint (n : ℕ) : Continuous (diskPoint n) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

/-- Collar coordinates in the actual Euclidean characteristic disk. No choice
of a direction at the center is made. This also handles dimension zero without
a separate nonempty-sphere assumption. -/
def diskCoordinates (n : ℕ) : OuterDisk n ≃ₜ Radius × Sphere n where
  toFun x := (diskRadius n x, diskDirection n x)
  invFun p := ⟨diskPoint n p, diskPoint_mem_outer n p⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change ‖x.1.1‖ • ‖x.1.1‖⁻¹ • x.1.1 = x.1.1
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero n x), one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact norm_diskPoint n p
    · apply Subtype.ext
      change ‖(diskPoint n p).1‖⁻¹ • ((p.1 : ℝ) • p.2.1) = p.2.1
      rw [norm_diskPoint, smul_smul, inv_mul_cancel₀ (ne_of_gt (radius_pos p.1)), one_smul]
  continuous_toFun := (continuous_diskRadius n).prodMk (continuous_diskDirection n)
  continuous_invFun := (continuous_diskPoint n).subtype_mk _

theorem diskPoint_boundary (n : ℕ) (θ : Sphere n) :
    diskPoint n (boundaryRadius, θ) = boundaryInclusion n θ := by
  apply Subtype.ext
  exact one_smul ℝ θ.1

/-- Pull back an open set of attaching directions to its actual outer collar.
This is open in the whole characteristic disk, not just in the collar. -/
theorem isOpen_collar (n : ℕ) {U : Set (Sphere n)} (hU : IsOpen U) :
    IsOpen (Subtype.val '' (diskDirection n ⁻¹' U) : Set (Disk n)) := by
  have hopen : IsOpen {x : Disk n | 1 / 2 < ‖x.1‖} :=
    isOpen_lt continuous_const continuous_subtype_val.norm
  exact hopen.isOpenMap_subtype_val _ (hU.preimage (continuous_diskDirection n))

end Collar

/-- Uniqueness of the open cell containing a point. Boundary maps need not be
injective, so uniqueness is asserted only for open cells. -/
theorem cell_index_eq_of_mem
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    {n m : ℕ} {c : Cell X n} {d : Cell X m} {x : X}
    (hc : x ∈ openCell X n c) (hd : x ∈ openCell X m d) :
    (⟨n, c⟩ : Σ k, Cell X k) = ⟨m, d⟩ := by
  by_contra h
  exact Set.disjoint_left.mp
    (CWStructure.disjoint_interiors (mem_univ _) (mem_univ _) h) hc hd

theorem openCell_not_mem_skeletonLT
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    {n : ℕ} {c : Cell X n} {x : X} (hx : x ∈ openCell X n c) :
    x ∉ skeletonLT X n := by
  intro h
  rcases mem_iUnion.mp h with ⟨m, h⟩
  rcases mem_iUnion.mp h with ⟨hm, h⟩
  rcases mem_iUnion.mp h with ⟨d, hd⟩
  have he := congrArg Sigma.fst (cell_index_eq_of_mem hx hd)
  exact (Nat.ne_of_lt hm) he.symm

/-- In the interior of a cell, membership in a subcomplex is exactly selection
of that cell; no closedness theorem is used here. -/
theorem mem_subcomplex_of_mem_openCell_iff
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) {n : ℕ} {c : Cell X n} {x : X}
    (hx : x ∈ openCell X n c) : x ∈ A.carrier ↔ c ∈ A.cells n := by
  constructor
  · intro h
    rcases mem_iUnion.mp h with ⟨m, h⟩
    rcases mem_iUnion.mp h with ⟨d, hd⟩
    have he := cell_index_eq_of_mem hx hd
    cases he
    exact d.2
  · intro hc
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨c, hc⟩, hx⟩⟩

theorem disk_interior_or_boundary (n : ℕ) (x : Disk n) :
    (∃ y : OpenDisk n, interiorInclusion n y = x) ∨
      ∃ z : Sphere n, boundaryInclusion n z = x := by
  have hx : ‖x.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
  rcases lt_or_eq_of_le hx with h | h
  · exact Or.inl ⟨⟨x.1, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩, rfl⟩
  · exact Or.inr ⟨⟨x.1, by simpa only [Metric.mem_sphere, dist_zero_right] using h⟩, rfl⟩

/-- A fiber touching the interior of a new disk has just that one new-disk
point. All nontrivial attachment identifications occur on the boundary. -/
theorem characteristic_interior_fiber
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    {n : ℕ} {c d : Cell X n} (x : OpenDisk n) (y : Disk n)
    (he : interiorMap X n c x = characteristic X n d y) :
    c = d ∧ interiorInclusion n x = y := by
  rcases disk_interior_or_boundary n y with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · have hi := cell_index_eq_of_mem (x := interiorMap X n c x)
      (mem_range_self x) (show interiorMap X n c x ∈ openCell X n d from
        ⟨y, he.symm⟩)
    have hcd : c = d := by cases hi; rfl
    subst d
    have hxy : x = y := (CWStructure.interior_embedding n c).injective he
    exact ⟨rfl, congrArg (interiorInclusion n) hxy⟩
  · exfalso
    exact openCell_not_mem_skeletonLT (mem_range_self x)
      (by rw [he]; exact CWStructure.boundary_lands n d (mem_univ z))

/-- Selected characteristic disks, including their possibly noninjective
boundaries, lie entirely in the subcomplex. -/
theorem characteristic_mem_subcomplex
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) {n : ℕ} {c : Cell X n} (hc : c ∈ A.cells n)
    (x : Disk n) : characteristic X n c x ∈ A.carrier := by
  apply A.contains_closures n c hc
  rw [hclosure n c]
  exact mem_range_self x

/-- Maps on an attachment descend as soon as their values agree on the
attaching boundaries. This explicitly checks the fibers of the canonical
projection rather than assuming injective attaching maps. -/
theorem attachment_factorsThrough
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    {Y : Sort v} (n : ℕ)
    (f : (skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) → Y)
    (hb : ∀ c z, f (.inr ⟨c, boundaryInclusion n z⟩) =
      f (.inl (attachingMap n c z))) :
    Function.FactorsThrough f (attachmentProjection X CWStructure.boundary_lands n) := by
  have hold : ∀ p (x : skeletonLT X n),
      attachmentProjection X CWStructure.boundary_lands n p = oldSkeletonInclusion X n x →
      f p = f (.inl x) := by
    intro p x he
    cases p with
    | inl y =>
      have hxy : y = x := Subtype.ext (congrArg (fun z : skeletonLT X (n + 1) => z.1) he)
      subst y
      rfl
    | inr p =>
      rcases p with ⟨c, y⟩
      rcases disk_interior_or_boundary n y with ⟨y, rfl⟩ | ⟨z, rfl⟩
      · exfalso
        apply openCell_not_mem_skeletonLT (x := interiorMap X n c y) (mem_range_self y)
        have hv : interiorMap X n c y = x.1 :=
          congrArg (fun z : skeletonLT X (n + 1) => z.1) he
        rw [hv]
        exact x.2
      · rw [hb]
        have hz : attachingMap n c z = x := Subtype.ext
          (congrArg (fun z : skeletonLT X (n + 1) => z.1) he)
        rw [hz]
  intro p q he
  cases p with
  | inl x => exact (hold q x he.symm).symm
  | inr p =>
    rcases p with ⟨c, x⟩
    rcases disk_interior_or_boundary n x with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · cases q with
      | inl y => exact hold (.inr ⟨c, interiorInclusion n x⟩) y he
      | inr q =>
        rcases q with ⟨d, y⟩
        obtain ⟨hcd, hxy⟩ := characteristic_interior_fiber x y (congrArg Subtype.val he)
        change c = d at hcd
        subst d
        rw [hxy]
    · rw [hb]
      exact (hold q (attachingMap n c z) he.symm).symm

namespace Collar

/-- The actual open subset of a disk over a set of attaching directions. -/
def diskCollar (n : ℕ) (U : Set (Sphere n)) : Set (Disk n) :=
  Subtype.val '' (diskDirection n ⁻¹' U)

theorem isOpen_diskCollar (n : ℕ) {U : Set (Sphere n)} (hU : IsOpen U) :
    IsOpen (diskCollar n U) := isOpen_collar n hU

theorem norm_boundaryInclusion (n : ℕ) (z : Sphere n) :
    ‖(boundaryInclusion n z).1‖ = 1 := by
  change ‖z.1‖ = 1
  simpa only [Metric.mem_sphere, dist_zero_right] using z.2

theorem boundary_mem_diskCollar (n : ℕ) (U : Set (Sphere n)) (z : Sphere n) :
    boundaryInclusion n z ∈ diskCollar n U ↔ z ∈ U := by
  have hn : 1 / 2 < ‖(boundaryInclusion n z).1‖ := by
    rw [norm_boundaryInclusion]; norm_num
  have hd : diskDirection n ⟨boundaryInclusion n z, hn⟩ = z := by
    apply Subtype.ext
    change ‖(boundaryInclusion n z).1‖⁻¹ • z.1 = z.1
    rw [norm_boundaryInclusion, inv_one, one_smul]
  constructor
  · rintro ⟨x, hx, he⟩
    have he' : x = ⟨boundaryInclusion n z, hn⟩ := Subtype.ext he
    subst x
    change diskDirection n ⟨boundaryInclusion n z, hn⟩ ∈ U at hx
    rwa [hd] at hx
  · intro hz
    refine ⟨⟨boundaryInclusion n z, hn⟩, ?_, rfl⟩
    change diskDirection n ⟨boundaryInclusion n z, hn⟩ ∈ U
    rwa [hd]

end Collar

/-- The open neighborhood before gluing on the next collection of cells. -/
def neighborhoodAttachmentSource
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) (W : Set (skeletonLT X n)) :
    Set (skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) :=
  {p | match p with
    | .inl x => x ∈ W
    | .inr ⟨c, x⟩ => c ∈ A.cells n ∨
        x ∈ Collar.diskCollar n (attachingMap n c ⁻¹' W)}

theorem isOpen_neighborhoodAttachmentSource
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)} (hW : IsOpen W) :
    IsOpen (neighborhoodAttachmentSource A n W) := by
  classical
  apply isOpen_sum_iff.mpr
  refine ⟨hW, ?_⟩
  apply isOpen_sigma_iff.mpr
  intro c
  by_cases hc : c ∈ A.cells n
  · simp [neighborhoodAttachmentSource, hc]
  · simpa [neighborhoodAttachmentSource, hc] using
      Collar.isOpen_diskCollar n (hW.preimage (attachingMap n c).continuous)

theorem neighborhoodAttachmentSource_boundary
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (c : Cell X n) (z : Sphere n) :
    Sum.inr (⟨c, boundaryInclusion n z⟩ : Σ _ : Cell X n, Disk n) ∈
        neighborhoodAttachmentSource A n W ↔ attachingMap n c z ∈ W := by
  change (c ∈ A.cells n ∨ boundaryInclusion n z ∈
    Collar.diskCollar n (attachingMap n c ⁻¹' W)) ↔ _
  rw [Collar.boundary_mem_diskCollar]
  constructor
  · rintro (hc | hz)
    · exact hAW _ (characteristic_mem_subcomplex hclosure A hc (boundaryInclusion n z))
    · exact hz
  · exact Or.inr

theorem neighborhoodAttachmentSource_saturated
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W) :
    ∀ p q, attachmentProjection X CWStructure.boundary_lands n p =
      attachmentProjection X CWStructure.boundary_lands n q →
      (p ∈ neighborhoodAttachmentSource A n W ↔ q ∈ neighborhoodAttachmentSource A n W) := by
  intro p q he
  apply Iff.of_eq
  exact attachment_factorsThrough n (fun p => p ∈ neighborhoodAttachmentSource A n W)
    (fun c z => propext (neighborhoodAttachmentSource_boundary hclosure A n hAW c z)) he

/-- The next-stage neighborhood in the actual next-skeleton subspace. -/
def neighborhoodAttachment
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) (W : Set (skeletonLT X n)) :
    Set (skeletonLT X (n + 1)) :=
  attachmentProjection X CWStructure.boundary_lands n '' neighborhoodAttachmentSource A n W

theorem mem_neighborhoodAttachment_projection
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (p : skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) :
    attachmentProjection X CWStructure.boundary_lands n p ∈ neighborhoodAttachment A n W ↔
      p ∈ neighborhoodAttachmentSource A n W := by
  constructor
  · rintro ⟨q, hq, he⟩
    exact (neighborhoodAttachmentSource_saturated hclosure A n hAW q p he).mp hq
  · exact mem_image_of_mem _

theorem isOpen_neighborhoodAttachment
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)} (hW : IsOpen W)
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W) :
    IsOpen (neighborhoodAttachment A n W) :=
  isOpen_image_of_saturated (CWStructure.attachment_quotient n)
    (isOpen_neighborhoodAttachmentSource A n hW)
    (neighborhoodAttachmentSource_saturated hclosure A n hAW)

/-- Attaching the collars adds no new point to the old skeleton. -/
theorem neighborhoodAttachment_restrict
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (x : skeletonLT X n) :
    oldSkeletonInclusion X n x ∈ neighborhoodAttachment A n W ↔ x ∈ W :=
  mem_neighborhoodAttachment_projection hclosure A n hAW (.inl x)

theorem neighborhoodAttachment_contains
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (x : skeletonLT X (n + 1)) (hx : x.1 ∈ A.carrier) :
    x ∈ neighborhoodAttachment A n W := by
  obtain ⟨p, rfl⟩ := (CWStructure.attachment_quotient n).surjective x
  apply (mem_neighborhoodAttachment_projection hclosure A n hAW p).mpr
  cases p with
  | inl y => exact hAW y hx
  | inr p =>
    rcases p with ⟨c, y⟩
    rcases disk_interior_or_boundary n y with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · exact Or.inl ((mem_subcomplex_of_mem_openCell_iff A (mem_range_self y)).mp hx)
    · exact (neighborhoodAttachmentSource_boundary hclosure A n hAW c z).mpr
        (hAW (attachingMap n c z) hx)

namespace Collar

/-- Coordinates on the collar over a restricted set of directions. -/
def collarCoordinates (n : ℕ) (U : Set (Sphere n)) :
    diskCollar n U → Radius × U := fun x =>
  let xo : OuterDisk n := ⟨x.1, by
    obtain ⟨y, _, hy⟩ := x.2
    exact hy ▸ y.2⟩
  ((diskCoordinates n xo).1, ⟨(diskCoordinates n xo).2, by
    obtain ⟨y, hy, he⟩ := x.2
    have he' : y = xo := Subtype.ext he
    exact he' ▸ hy⟩)

theorem continuous_collarCoordinates (n : ℕ) (U : Set (Sphere n)) :
    Continuous (collarCoordinates n U) := by
  let f : diskCollar n U → OuterDisk n := fun x => ⟨x.1, by
    obtain ⟨y, _, hy⟩ := x.2
    exact hy ▸ y.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  exact (continuous_diskRadius n |>.comp hf).prodMk
    ((continuous_diskDirection n |>.comp hf).subtype_mk _)

theorem diskPoint_collarCoordinates (n : ℕ) (U : Set (Sphere n))
    (x : diskCollar n U) :
    diskPoint n ((collarCoordinates n U x).1, (collarCoordinates n U x).2.1) = x.1 := by
  exact congrArg Subtype.val ((diskCoordinates n).left_inv _)

theorem collarCoordinates_boundary (n : ℕ) (U : Set (Sphere n)) (z : U) :
    collarCoordinates n U ⟨boundaryInclusion n z.1,
      (boundary_mem_diskCollar n U z.1).mpr z.2⟩ = (boundaryRadius, z) := by
  apply Prod.ext
  · apply Subtype.ext
    exact norm_boundaryInclusion n z.1
  · apply Subtype.ext
    apply Subtype.ext
    change ‖(boundaryInclusion n z.1).1‖⁻¹ • z.1.1 = z.1.1
    rw [norm_boundaryInclusion, inv_one, one_smul]

variable {X : Type u} [TopologicalSpace X] [CWStructure X]
    {n : ℕ} {W : Set (skeletonLT X n)}

/-- The radial part, with the ordinary ambient characteristic map as codomain. -/
def radialMap (c : Cell X n) : C(Radius × (attachingMap n c ⁻¹' W), X) :=
  ⟨fun p => characteristic X n c (diskPoint n (p.1, p.2.1)),
    (characteristic X n c).continuous.comp ((continuous_diskPoint n).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩

/-- The old homotopy pulled back along the attaching directions. -/
def boundaryHomotopy (c : Cell X n) (H : C(W × Interval, W)) :
    C((attachingMap n c ⁻¹' W) × Interval, X) :=
  ⟨fun p => (H (⟨attachingMap n c p.1.1, p.1.2⟩, p.2)).1.1, by
    apply continuous_subtype_val.comp
    apply continuous_subtype_val.comp
    apply H.continuous.comp
    exact (((attachingMap n c).continuous.comp
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk continuous_snd⟩

theorem radialMap_boundary (c : Cell X n) (H : C(W × Interval, W))
    (hzero : ∀ x : W, H (x, 0) = x) (z : attachingMap n c ⁻¹' W) :
    radialMap c (boundaryRadius, z) = boundaryHomotopy c H (z, 0) := by
  change characteristic X n c (diskPoint n (boundaryRadius, z.1)) =
    (H (⟨attachingMap n c z.1, z.2⟩, 0)).1.1
  rw [diskPoint_boundary, hzero]
  rfl

/-- Continuous radial-first extension on the actual restricted disk. -/
def cellHomotopy (c : Cell X n) (H : C(W × Interval, W))
    (hzero : ∀ x : W, H (x, 0) = x) :
    C(diskCollar n (attachingMap n c ⁻¹' W) × Interval, X) :=
  ⟨fun p => extend (radialMap c) (boundaryHomotopy c H)
      (collarCoordinates n _ p.1, p.2),
    (continuous_extend _ _ (radialMap_boundary c H hzero)).comp
      (((continuous_collarCoordinates n _).comp continuous_fst).prodMk continuous_snd)⟩

theorem cellHomotopy_zero (c : Cell X n) (H : C(W × Interval, W))
    (hzero : ∀ x : W, H (x, 0) = x)
    (x : diskCollar n (attachingMap n c ⁻¹' W)) :
    cellHomotopy c H hzero (x, 0) = characteristic X n c x.1 := by
  change extend _ _ (_, 0) = _
  rw [extend_zero]
  change characteristic X n c (diskPoint n _) = _
  rw [diskPoint_collarCoordinates]

theorem cellHomotopy_one (c : Cell X n) (H : C(W × Interval, W))
    (hzero : ∀ x : W, H (x, 0) = x)
    (x : diskCollar n (attachingMap n c ⁻¹' W)) :
    cellHomotopy c H hzero (x, 1) =
      boundaryHomotopy c H ((collarCoordinates n _ x).2, 1) := by
  exact extend_one _ _ _ _

theorem cellHomotopy_boundary (c : Cell X n) (H : C(W × Interval, W))
    (hzero : ∀ x : W, H (x, 0) = x) (z : attachingMap n c ⁻¹' W) (t : Interval) :
    cellHomotopy c H hzero
      (⟨boundaryInclusion n z.1, (boundary_mem_diskCollar n _ z.1).mpr z.2⟩, t) =
      (H (⟨attachingMap n c z.1, z.2⟩, t)).1.1 := by
  change extend _ _ (collarCoordinates n _ _, t) = _
  rw [collarCoordinates_boundary]
  exact extend_boundary _ _ (radialMap_boundary c H hzero) z t

end Collar

/-- Continuity on a product with a subset, expressed using its actual subtype. -/
theorem continuousOn_prod_iff_restrict
    {P : Type u} {T : Type v} {Y : Type w}
    [TopologicalSpace P] [TopologicalSpace T] [TopologicalSpace Y]
    (s : Set P) (f : P × T → Y) :
    ContinuousOn f (s ×ˢ univ) ↔
      Continuous (fun p : s × T => f (p.1.1, p.2)) := by
  constructor
  · intro hf
    exact hf.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun p => ⟨p.1.2, mem_univ _⟩)
  · intro hf
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hf.comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
      (fun p => p.2.1)).prodMk (continuous_snd.comp continuous_subtype_val))

theorem continuousOn_sum_prod_iff_of_isOpen
    {P : Type u} {Q : Type v} {T : Type w} {Y : Type*}
    [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace T] [TopologicalSpace Y]
    {s : Set ((P ⊕ Q) × T)} (hs : IsOpen s) (f : (P ⊕ Q) × T → Y) :
    ContinuousOn f s ↔
      ContinuousOn (f ∘ Prod.map Sum.inl id) (Prod.map Sum.inl id ⁻¹' s) ∧
      ContinuousOn (f ∘ Prod.map Sum.inr id) (Prod.map Sum.inr id ⁻¹' s) := by
  constructor
  · intro hf
    exact ⟨hf.comp (continuous_inl.prodMap continuous_id).continuousOn (fun _ hx => hx),
      hf.comp (continuous_inr.prodMap continuous_id).continuousOn (fun _ hx => hx)⟩
  · rintro ⟨hl, hr⟩ ⟨p, t⟩ hp
    apply ContinuousAt.continuousWithinAt
    cases p with
    | inl x =>
      apply ((IsOpenEmbedding.inl.prodMap (.id)).continuousAt_iff
        (g := f) (x := (x, t))).mp
      exact hl.continuousAt
        ((hs.preimage (continuous_inl.prodMap continuous_id)).mem_nhds hp)
    | inr x =>
      apply ((IsOpenEmbedding.inr.prodMap (.id)).continuousAt_iff
        (g := f) (x := (x, t))).mp
      exact hr.continuousAt
        ((hs.preimage (continuous_inr.prodMap continuous_id)).mem_nhds hp)

/-- The new homotopy before gluing. Values off the proposed neighborhood are
only a set-theoretic extension used to state the local continuity test. -/
def attachmentHomotopy
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (p : (skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) × Interval) : X := by
  classical
  exact match p.1 with
  | .inl x => if hx : x ∈ W then (H (⟨x, hx⟩, p.2)).1.1 else x.1
  | .inr ⟨c, x⟩ => if c ∈ A.cells n then characteristic X n c x else
      if hx : x ∈ Collar.diskCollar n (attachingMap n c ⁻¹' W) then
        Collar.cellHomotopy c H hzero (⟨x, hx⟩, p.2) else characteristic X n c x

theorem continuousOn_attachmentHomotopy
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)} (hW : IsOpen W)
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x) :
    ContinuousOn (attachmentHomotopy A n H hzero)
      (neighborhoodAttachmentSource A n W ×ˢ univ) := by
  classical
  apply (continuousOn_sum_prod_iff_of_isOpen
    ((isOpen_neighborhoodAttachmentSource A n hW).prod isOpen_univ) _).mpr
  constructor
  · change ContinuousOn _ (W ×ˢ univ)
    apply (continuousOn_prod_iff_restrict W _).mpr
    have hc := continuous_subtype_val.comp (continuous_subtype_val.comp H.continuous)
    apply hc.congr
    intro p
    simp [attachmentHomotopy, p.1.2]
  · apply (continuousOn_sigma_prod_iff_of_isOpen
      (((isOpen_neighborhoodAttachmentSource A n hW).prod isOpen_univ).preimage
        (continuous_inr.prodMap continuous_id)) _).mpr
    intro c
    by_cases hc : c ∈ A.cells n
    · have hf : Continuous (fun p : Disk n × Interval => characteristic X n c p.1) :=
        (characteristic X n c).continuous.comp continuous_fst
      exact hf.continuousOn.congr (fun p _ => by simp [attachmentHomotopy, hc])
    · have he : (Prod.map (Sigma.mk c) (id : Interval → Interval) ⁻¹'
          (Prod.map Sum.inr id ⁻¹' (neighborhoodAttachmentSource A n W ×ˢ univ))) =
          Collar.diskCollar n (attachingMap n c ⁻¹' W) ×ˢ univ := by
        ext p
        simp [neighborhoodAttachmentSource, hc]
      rw [he]
      apply (continuousOn_prod_iff_restrict _ _).mpr
      apply (Collar.cellHomotopy c H hzero).continuous.congr
      intro p
      simp [attachmentHomotopy, hc, p.1.2]

theorem attachmentHomotopy_zero
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (p : skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) :
    attachmentHomotopy A n H hzero (p, 0) =
      (attachmentProjection X CWStructure.boundary_lands n p).1 := by
  classical
  cases p with
  | inl x =>
    by_cases hx : x ∈ W <;> simp [attachmentHomotopy, hx, hzero,
      attachmentProjection, oldSkeletonInclusion]
  | inr p =>
    rcases p with ⟨c, x⟩
    by_cases hc : c ∈ A.cells n
    · simp [attachmentHomotopy, hc, attachmentProjection, diskToSkeleton]
    · by_cases hx : x ∈ Collar.diskCollar n (attachingMap n c ⁻¹' W)
      · simpa [attachmentHomotopy, hc, hx, attachmentProjection, diskToSkeleton] using
          Collar.cellHomotopy_zero c H hzero ⟨x, hx⟩
      · simp [attachmentHomotopy, hc, hx, attachmentProjection, diskToSkeleton]

theorem attachmentHomotopy_boundary
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (hfix : ∀ (x : W) (t : Interval), x.1.1 ∈ A.carrier → H (x, t) = x)
    (c : Cell X n) (z : Sphere n) (t : Interval) :
    attachmentHomotopy A n H hzero (.inr ⟨c, boundaryInclusion n z⟩, t) =
      attachmentHomotopy A n H hzero (.inl (attachingMap n c z), t) := by
  classical
  by_cases hc : c ∈ A.cells n
  · have hzA : (attachingMap n c z).1 ∈ A.carrier :=
      characteristic_mem_subcomplex hclosure A hc (boundaryInclusion n z)
    have hzW := hAW _ hzA
    simp only [attachmentHomotopy, ite_eq_left hc, dite_eq_left hzW]
    rw [hfix _ t hzA]
    rfl
  · by_cases hzW : attachingMap n c z ∈ W
    · have hzC := (Collar.boundary_mem_diskCollar n (attachingMap n c ⁻¹' W) z).mpr hzW
      simpa only [attachmentHomotopy, ite_eq_right hc, dite_eq_left hzW, dite_eq_left hzC] using
        Collar.cellHomotopy_boundary c H hzero ⟨z, hzW⟩ t
    · have hzC : boundaryInclusion n z ∉ Collar.diskCollar n (attachingMap n c ⁻¹' W) := by
        rwa [Collar.boundary_mem_diskCollar]
      simp only [attachmentHomotopy, ite_eq_right hc, dite_eq_right hzW, dite_eq_right hzC]
      rfl

theorem attachmentHomotopy_factorsThrough
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (hfix : ∀ (x : W) (t : Interval), x.1.1 ∈ A.carrier → H (x, t) = x)
    (t : Interval) :
    Function.FactorsThrough (fun p => attachmentHomotopy A n H hzero (p, t))
      (attachmentProjection X CWStructure.boundary_lands n) :=
  attachment_factorsThrough n _ (fun c z =>
    attachmentHomotopy_boundary hclosure A n hAW H hzero hfix c z t)

theorem attachmentHomotopy_terminal
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (hone : ∀ x : W, (H (x, 1)).1.1 ∈ A.carrier)
    (p : neighborhoodAttachmentSource A n W) :
    attachmentHomotopy A n H hzero (p.1, 1) ∈ A.carrier := by
  classical
  obtain ⟨p, hp⟩ := p
  cases p with
  | inl x =>
    change x ∈ W at hp
    simpa only [attachmentHomotopy, dite_eq_left hp] using hone ⟨x, hp⟩
  | inr p =>
    rcases p with ⟨c, x⟩
    by_cases hc : c ∈ A.cells n
    · simpa only [attachmentHomotopy, ite_eq_left hc] using characteristic_mem_subcomplex hclosure A hc x
    · have hx : x ∈ Collar.diskCollar n (attachingMap n c ⁻¹' W) := hp.resolve_left hc
      simp only [attachmentHomotopy, ite_eq_right hc, dite_eq_left hx]
      rw [Collar.cellHomotopy_one]
      exact hone _

theorem attachmentHomotopy_fixed
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (hfix : ∀ (x : W) (t : Interval), x.1.1 ∈ A.carrier → H (x, t) = x)
    (p : skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) (t : Interval)
    (hp : (attachmentProjection X CWStructure.boundary_lands n p).1 ∈ A.carrier) :
    attachmentHomotopy A n H hzero (p, t) =
      (attachmentProjection X CWStructure.boundary_lands n p).1 := by
  classical
  have hold : ∀ (x : skeletonLT X n), x.1 ∈ A.carrier →
      attachmentHomotopy A n H hzero (.inl x, t) = x.1 := by
    intro x hx
    simp only [attachmentHomotopy, dite_eq_left (hAW x hx)]
    rw [hfix ⟨x, hAW x hx⟩ t hx]
  cases p with
  | inl x => exact hold x hp
  | inr p =>
    rcases p with ⟨c, x⟩
    by_cases hc : c ∈ A.cells n
    · simp [attachmentHomotopy, hc, attachmentProjection, diskToSkeleton]
    · rcases disk_interior_or_boundary n x with ⟨x, rfl⟩ | ⟨z, rfl⟩
      · exact (hc ((mem_subcomplex_of_mem_openCell_iff A (mem_range_self x)).mp hp)).elim
      · rw [attachmentHomotopy_boundary hclosure A n hAW H hzero hfix]
        exact hold (attachingMap n c z) hp

namespace Collar

theorem diskPoint_mem_diskCollar (n : ℕ) (U : Set (Sphere n))
    (r : Radius) (z : U) : diskPoint n (r, z.1) ∈ diskCollar n U := by
  refine ⟨⟨diskPoint n (r, z.1), diskPoint_mem_outer n _⟩, ?_, rfl⟩
  change diskDirection n ((diskCoordinates n).symm (r, z.1)) ∈ U
  have he := congrArg Prod.snd ((diskCoordinates n).apply_symm_apply (r, z.1))
  change diskDirection n ((diskCoordinates n).symm (r, z.1)) = z.1 at he
  rw [he]
  exact z.2

end Collar

/-- The pre-gluing homotopy stays inside the new neighborhood at every time. -/
theorem attachmentHomotopy_mem
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)}
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (p : neighborhoodAttachmentSource A n W) (t : Interval) :
    attachmentHomotopy A n H hzero (p.1, t) ∈
      (Subtype.val '' neighborhoodAttachment A n W : Set X) := by
  classical
  have hold : ∀ x : W, x.1.1 ∈ (Subtype.val '' neighborhoodAttachment A n W : Set X) := by
    intro x
    exact ⟨oldSkeletonInclusion X n x.1,
      (neighborhoodAttachment_restrict hclosure A n hAW x.1).mpr x.2, rfl⟩
  have hdisk : ∀ (c : Cell X n) (x : Disk n),
      Sum.inr (⟨c, x⟩ : Σ _ : Cell X n, Disk n) ∈ neighborhoodAttachmentSource A n W →
      characteristic X n c x ∈ (Subtype.val '' neighborhoodAttachment A n W : Set X) := by
    intro c x hx
    exact ⟨diskToSkeleton X CWStructure.boundary_lands n c x,
      (mem_neighborhoodAttachment_projection hclosure A n hAW (.inr ⟨c, x⟩)).mpr hx, rfl⟩
  obtain ⟨p, hp⟩ := p
  cases p with
  | inl x =>
    change x ∈ W at hp
    simpa only [attachmentHomotopy, dite_eq_left hp] using hold (H (⟨x, hp⟩, t))
  | inr p =>
    rcases p with ⟨c, x⟩
    by_cases hc : c ∈ A.cells n
    · simpa only [attachmentHomotopy, ite_eq_left hc] using hdisk c x (Or.inl hc)
    · have hx : x ∈ Collar.diskCollar n (attachingMap n c ⁻¹' W) := hp.resolve_left hc
      simp only [attachmentHomotopy, ite_eq_right hc, dite_eq_left hx]
      change Collar.extend _ _ (_, t) ∈ _
      unfold Collar.extend
      split_ifs with ht
      · apply hdisk
        exact Or.inr (Collar.diskPoint_mem_diskCollar n _ _ _)
      · exact hold (H (_, _))

/-- Descent of a homotopy through an open restriction of a quotient map,
retaining the commutation equation for later skeletal compatibility. -/
theorem exists_quotient_homotopy
    {P : Type u} {Q : Type v} [TopologicalSpace P] [TopologicalSpace Q]
    {q : P → Q} (hq : IsQuotientMap q) {W : Set Q} (hW : IsOpen W)
    (F : C((q ⁻¹' W) × Interval, W))
    (hfiber : ∀ (x y : q ⁻¹' W) (t : Interval), q x.1 = q y.1 → F (x, t) = F (y, t)) :
    ∃ H : C(W × Interval, W), ∀ (x : q ⁻¹' W) (t : Interval),
      H (⟨q x.1, x.2⟩, t) = F (x, t) := by
  let qW : C(q ⁻¹' W, W) := ⟨W.restrictPreimage q, (hq.restrictPreimage_isOpen hW).continuous⟩
  have hqW : IsQuotientMap qW := hq.restrictPreimage_isOpen hW
  let qWI : C((q ⁻¹' W) × Interval, W × Interval) :=
    ⟨Prod.map qW id, qW.continuous.prodMap continuous_id⟩
  have hqWI : IsQuotientMap qWI := quotientMap_prod_locallyCompact hqW
  have hfac : Function.FactorsThrough F qWI := by
    intro p p' hp
    obtain ⟨x, t⟩ := p
    obtain ⟨y, s⟩ := p'
    have hts : t = s := congrArg Prod.snd hp
    subst s
    exact hfiber x y t (congrArg (fun z : W × Interval => z.1.1) hp)
  refine ⟨hqWI.lift F hfac, ?_⟩
  intro x t
  exact congrArg (fun f : C((q ⁻¹' W) × Interval, W) => f (x, t))
    (hqWI.lift_comp F hfac)

/-- One full inductive extension of a neighborhood and its strong deformation.
The last equality states that the new deformation extends the old one for all
times, with no reparametrization on the old skeleton. -/
theorem exists_neighborhoodAttachment_homotopy
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (n : ℕ) {W : Set (skeletonLT X n)} (hW : IsOpen W)
    (hAW : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ W)
    (H : C(W × Interval, W)) (hzero : ∀ x : W, H (x, 0) = x)
    (hone : ∀ x : W, (H (x, 1)).1.1 ∈ A.carrier)
    (hfix : ∀ (x : W) (t : Interval), x.1.1 ∈ A.carrier → H (x, t) = x) :
    ∃ H' : C(neighborhoodAttachment A n W × Interval, neighborhoodAttachment A n W),
      (∀ x, H' (x, 0) = x) ∧
      (∀ x, (H' (x, 1)).1.1 ∈ A.carrier) ∧
      (∀ x t, x.1.1 ∈ A.carrier → H' (x, t) = x) ∧
      (∀ (x : W) (t : Interval),
        (H' (⟨oldSkeletonInclusion X n x.1,
          (neighborhoodAttachment_restrict hclosure A n hAW x.1).mpr x.2⟩, t)).1.1 =
            (H (x, t)).1.1) := by
  let q := attachmentProjection X CWStructure.boundary_lands n
  let V := neighborhoodAttachment A n W
  have hV : IsOpen V := isOpen_neighborhoodAttachment hclosure A n hW hAW
  have hmem : ∀ p : (q ⁻¹' V) × Interval,
      attachmentHomotopy A n H hzero (p.1.1, p.2) ∈ (Subtype.val '' V : Set X) := by
    intro p
    exact attachmentHomotopy_mem hclosure A n hAW H hzero
      ⟨p.1.1, (mem_neighborhoodAttachment_projection hclosure A n hAW p.1.1).mp p.1.2⟩ p.2
  let F : C((q ⁻¹' V) × Interval, V) :=
    ⟨fun p => ⟨⟨attachmentHomotopy A n H hzero (p.1.1, p.2), by
        obtain ⟨y, _, hy⟩ := hmem p
        rw [← hy]
        exact y.2⟩, by
          obtain ⟨y, hyV, hy⟩ := hmem p
          convert hyV using 1
          exact Subtype.ext hy.symm⟩, by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (continuousOn_attachmentHomotopy A n hW H hzero).comp_continuous
        (continuous_subtype_val.prodMap continuous_id)
        (fun p => ⟨(mem_neighborhoodAttachment_projection hclosure A n hAW p.1.1).mp p.1.2,
          mem_univ _⟩)⟩
  have hfiber : ∀ (x y : q ⁻¹' V) (t : Interval), q x.1 = q y.1 → F (x, t) = F (y, t) := by
    intro x y t he
    apply Subtype.ext
    apply Subtype.ext
    exact attachmentHomotopy_factorsThrough hclosure A n hAW H hzero hfix t he
  obtain ⟨H', hcomm⟩ := exists_quotient_homotopy (CWStructure.attachment_quotient n) hV F hfiber
  have hlift : ∀ (x : V), ∃ p : q ⁻¹' V, (⟨q p.1, p.2⟩ : V) = x := by
    intro x
    obtain ⟨p, hp⟩ := (CWStructure.attachment_quotient n).surjective x.1
    exact ⟨⟨p, by change attachmentProjection X CWStructure.boundary_lands n p ∈ V; rw [hp]; exact x.2⟩, Subtype.ext hp⟩
  refine ⟨H', ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨p, rfl⟩ := hlift x
    rw [hcomm]
    apply Subtype.ext
    apply Subtype.ext
    exact attachmentHomotopy_zero A n H hzero p.1
  · intro x
    obtain ⟨p, rfl⟩ := hlift x
    rw [hcomm]
    exact attachmentHomotopy_terminal hclosure A n H hzero hone
      ⟨p.1, (mem_neighborhoodAttachment_projection hclosure A n hAW p.1).mp p.2⟩
  · intro x t hx
    obtain ⟨p, rfl⟩ := hlift x
    rw [hcomm]
    apply Subtype.ext
    apply Subtype.ext
    exact attachmentHomotopy_fixed hclosure A n hAW H hzero hfix p.1 t hx
  · intro x t
    have hp : q (.inl x.1) ∈ V :=
      (neighborhoodAttachment_restrict hclosure A n hAW x.1).mpr x.2
    have he := congrArg (fun y : V => y.1.1) (hcomm ⟨.inl x.1, hp⟩ t)
    change (H' (⟨oldSkeletonInclusion X n x.1, hp⟩, t)).1.1 =
      attachmentHomotopy A n H hzero (.inl x.1, t) at he
    simpa only [attachmentHomotopy, dite_eq_left x.2] using he

/-- A neighborhood and its deformation on one actual skeleton. -/
structure NeighborhoodStage
    {X : Type u} [TopologicalSpace X] [CWStructure X] (A : Subcomplex X) (n : ℕ) where
  carrier : Set (skeletonLT X n)
  isOpen : IsOpen carrier
  contains : ∀ x : skeletonLT X n, x.1 ∈ A.carrier → x ∈ carrier
  homotopy : C(carrier × Interval, carrier)
  initial : ∀ x, homotopy (x, 0) = x
  terminal : ∀ x, (homotopy (x, 1)).1.1 ∈ A.carrier
  fixed : ∀ x t, x.1.1 ∈ A.carrier → homotopy (x, t) = x

namespace NeighborhoodStage

variable {X : Type u} [TopologicalSpace X] [CWStructure X]
    {A : Subcomplex X} {n : ℕ}

def zero (A : Subcomplex X) : NeighborhoodStage A 0 where
  carrier := ∅
  isOpen := isOpen_empty
  contains x _ := by
    have hx := x.2
    simp [skeletonLT] at hx
  homotopy := ⟨Prod.fst, continuous_fst⟩
  initial _ := rfl
  terminal x := x.2.elim
  fixed _ _ _ := rfl

def next
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (S : NeighborhoodStage A n) : NeighborhoodStage A (n + 1) where
  carrier := neighborhoodAttachment A n S.carrier
  isOpen := isOpen_neighborhoodAttachment hclosure A n S.isOpen S.contains
  contains := neighborhoodAttachment_contains hclosure A n S.contains
  homotopy := Classical.choose (exists_neighborhoodAttachment_homotopy hclosure A n
    S.isOpen S.contains S.homotopy S.initial S.terminal S.fixed)
  initial := (Classical.choose_spec (exists_neighborhoodAttachment_homotopy hclosure A n
    S.isOpen S.contains S.homotopy S.initial S.terminal S.fixed)).1
  terminal := (Classical.choose_spec (exists_neighborhoodAttachment_homotopy hclosure A n
    S.isOpen S.contains S.homotopy S.initial S.terminal S.fixed)).2.1
  fixed := (Classical.choose_spec (exists_neighborhoodAttachment_homotopy hclosure A n
    S.isOpen S.contains S.homotopy S.initial S.terminal S.fixed)).2.2.1

theorem next_restrict
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (S : NeighborhoodStage A n) (x : skeletonLT X n) :
    oldSkeletonInclusion X n x ∈ (S.next hclosure).carrier ↔ x ∈ S.carrier :=
  neighborhoodAttachment_restrict hclosure A n S.contains x

theorem next_compatible
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (S : NeighborhoodStage A n) (x : S.carrier) (t : Interval) :
    ((S.next hclosure).homotopy
      (⟨oldSkeletonInclusion X n x.1, (S.next_restrict hclosure x.1).mpr x.2⟩, t)).1.1 =
        (S.homotopy (x, t)).1.1 :=
  (Classical.choose_spec (exists_neighborhoodAttachment_homotopy hclosure A n
    S.isOpen S.contains S.homotopy S.initial S.terminal S.fixed)).2.2.2 x t

/-- Ordinary recursion on dimension; no bound on the dimensions or cells is
used. The zero stage is the empty minus-one skeleton. -/
def sequence
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) : ∀ n, NeighborhoodStage A n
  | 0 => zero A
  | n + 1 => (sequence hclosure A n).next hclosure

end NeighborhoodStage

/-- Forget the repeated subtype used by a subset of a skeleton, preserving its
actual topology. -/
def flattenSkeletonSubset
    {X : Type u} [TopologicalSpace X] {s : Set X} (W : Set s) :
    W ≃ₜ (Subtype.val '' W : Set X) where
  toFun x := ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
  invFun x := ⟨⟨x.1, by obtain ⟨y, _, hy⟩ := x.2; rw [← hy]; exact y.2⟩, by
    obtain ⟨y, hyW, hy⟩ := x.2
    convert hyW using 1
    exact Subtype.ext hy.symm⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

namespace NeighborhoodStage

variable {X : Type u} [TopologicalSpace X] [CWStructure X]
    {A : Subcomplex X} {n : ℕ} (S : NeighborhoodStage A n)

def ambientCarrier : Set X := Subtype.val '' S.carrier

theorem subset_skeleton : S.ambientCarrier ⊆ skeletonLT X n := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

theorem ambient_mem_iff (x : skeletonLT X n) :
    x.1 ∈ S.ambientCarrier ↔ x ∈ S.carrier := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem ambient_isOpen :
    IsOpen ((Subtype.val : skeletonLT X n → X) ⁻¹' S.ambientCarrier) := by
  have he : (Subtype.val : skeletonLT X n → X) ⁻¹' S.ambientCarrier = S.carrier := by
    ext x; exact S.ambient_mem_iff x
  rw [he]
  exact S.isOpen

def ambientHomotopy : C(S.ambientCarrier × Interval, S.ambientCarrier) :=
  let e := flattenSkeletonSubset S.carrier
  ⟨fun p => e (S.homotopy (e.symm p.1, p.2)),
    e.continuous.comp (S.homotopy.continuous.comp
      ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))⟩

theorem ambient_initial (x : S.ambientCarrier) : S.ambientHomotopy (x, 0) = x := by
  change flattenSkeletonSubset S.carrier (S.homotopy (_, 0)) = _
  rw [S.initial]
  exact (flattenSkeletonSubset S.carrier).apply_symm_apply x

theorem ambient_terminal (x : S.ambientCarrier) :
    (S.ambientHomotopy (x, 1)).1 ∈ A.carrier := S.terminal _

theorem ambient_fixed (x : S.ambientCarrier) (t : Interval) (hx : x.1 ∈ A.carrier) :
    S.ambientHomotopy (x, t) = x := by
  change flattenSkeletonSubset S.carrier (S.homotopy (_, t)) = _
  rw [S.fixed _ t hx]
  exact (flattenSkeletonSubset S.carrier).apply_symm_apply x

theorem ambient_next_restrict
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    (S.next hclosure).ambientCarrier ∩ skeletonLT X n = S.ambientCarrier := by
  ext x
  constructor
  · rintro ⟨hx, hxn⟩
    have hx' := ((S.next hclosure).ambient_mem_iff
      (oldSkeletonInclusion X n ⟨x, hxn⟩)).mp hx
    exact (S.ambient_mem_iff ⟨x, hxn⟩).mpr ((S.next_restrict hclosure _).mp hx')
  · intro hx
    have hxn := S.subset_skeleton hx
    refine ⟨?_, hxn⟩
    apply ((S.next hclosure).ambient_mem_iff (oldSkeletonInclusion X n ⟨x, hxn⟩)).mpr
    exact (S.next_restrict hclosure _).mpr ((S.ambient_mem_iff _).mp hx)

theorem ambient_next_mono
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    S.ambientCarrier ⊆ (S.next hclosure).ambientCarrier := by
  intro x hx
  have he := S.ambient_next_restrict hclosure
  exact (show x ∈ (S.next hclosure).ambientCarrier ∩ skeletonLT X n by rw [he]; exact hx).1

theorem ambient_next_compatible
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (x : S.ambientCarrier) (t : Interval) :
    ((S.next hclosure).ambientHomotopy
      (⟨x.1, S.ambient_next_mono hclosure x.2⟩, t)).1 = (S.ambientHomotopy (x, t)).1 := by
  exact S.next_compatible hclosure ((flattenSkeletonSubset S.carrier).symm x) t

end NeighborhoodStage

/-- The actual compatible skeletal neighborhoods produced by the collar
construction, for an arbitrary subcomplex. -/
def buildCompatibleSkeletalNeighborhoods
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X] (A : Subcomplex X) :
    CompatibleSkeletalNeighborhoods A.carrier := by
  let S := NeighborhoodStage.sequence hclosure A
  have hstep : ∀ n, (S (n + 1)).ambientCarrier ∩ skeletonLT X n = (S n).ambientCarrier :=
    fun n => (S n).ambient_next_restrict hclosure
  have hmono : Monotone (fun n => (S n).ambientCarrier) :=
    monotone_nat_of_le_succ (fun n => (S n).ambient_next_mono hclosure)
  have hrestrict : ∀ m n, m ≤ n →
      (S n).ambientCarrier ∩ skeletonLT X m = (S m).ambientCarrier := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact inter_eq_left.mpr (S m).subset_skeleton
    | succ k hmk ih =>
      calc
        (S (k + 1)).ambientCarrier ∩ skeletonLT X m =
            ((S (k + 1)).ambientCarrier ∩ skeletonLT X k) ∩ skeletonLT X m := by
          ext x
          constructor
          · rintro ⟨hx, hxm⟩
            exact ⟨⟨hx, skeletonLT_mono hmk hxm⟩, hxm⟩
          · rintro ⟨⟨hx, _⟩, hxm⟩
            exact ⟨hx, hxm⟩
        _ = (S k).ambientCarrier ∩ skeletonLT X m := by rw [hstep k]
        _ = (S m).ambientCarrier := ih
  have hcompatible : ∀ m n (hmn : m ≤ n) (x : (S m).ambientCarrier) (t : Interval),
      ((S n).ambientHomotopy (⟨x.1, hmono hmn x.2⟩, t)).1 =
        ((S m).ambientHomotopy (x, t)).1 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro x t; rfl
    | succ k hmk ih =>
      intro x t
      exact ((S k).ambient_next_compatible hclosure ⟨x.1, hmono hmk x.2⟩ t).trans (ih x t)
  exact
    { carrier := fun n => (S n).ambientCarrier
      subset_skeleton := fun n => (S n).subset_skeleton
      monotone := hmono
      restrict := hrestrict
      open_on_skeleton := fun n => (S n).ambient_isOpen
      contains := fun n x hx =>
        ((S n).ambient_mem_iff ⟨x, hx.2⟩).mpr ((S n).contains ⟨x, hx.2⟩ hx.1)
      homotopy := fun n => (S n).ambientHomotopy
      initial := fun n => (S n).ambient_initial
      terminal := fun n => (S n).ambient_terminal
      fixed := fun n => (S n).ambient_fixed
      compatible := hcompatible }

/-- Compatibility helper retaining the former explicit topology premises.
The collar construction itself only needs the characteristic quotient and
cell-closure results, already proved in `CellStructures`. -/
theorem subcomplexNeighborhood_conditional
    (_hcompact : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_hcompactImage : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u, v})
    (_hfiniteImages : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u, v})
    (_hsingular : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_hintervalHomotopy : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_hintervalMap : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_hclosed : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_hweak : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u}) :
    P202Specs.Topology.SubcomplexNeighborhoods.subcomplexNeighborhood.{u} := by
  intro X _ _ A
  exact (buildCompatibleSkeletalNeighborhoods closureOpenCell A).exists_neighborhood
    characteristicProjectionQuotient

/-- Every subcomplex strongly deformation retracts from an open neighborhood,
without restrictions on the number or dimensions of the cells. -/
theorem subcomplexNeighborhood :
    P202Specs.Topology.SubcomplexNeighborhoods.subcomplexNeighborhood.{u} := by
  intro X _ _ A
  exact (buildCompatibleSkeletalNeighborhoods closureOpenCell A).exists_neighborhood
    characteristicProjectionQuotient

end P202.Topology
