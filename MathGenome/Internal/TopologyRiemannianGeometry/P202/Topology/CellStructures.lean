import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.LocalAtTarget
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UrysohnsLemma

noncomputable section
open Set Topology
open P202.Cellular
universe u v w

namespace P202.Cellular.SimplexParametrization

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

def coordSimplex (b : AffineBasis ι ℝ E) (x : convexHull ℝ (range b)) :
    Convexity.StdSimplex ℝ ι where
  weights := Finsupp.equivFunOnFinite.symm (fun i => b.coord i x)
  nonneg i := by
    simpa using (show ∀ i, 0 ≤ b.coord i x from by
      simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using x.2) i
  total := by simp [Finsupp.sum_fintype]

@[simp] theorem coordSimplex_weights (b : AffineBasis ι ℝ E)
    (x : convexHull ℝ (range b)) (i : ι) :
    (coordSimplex b x).weights i = b.coord i x := by
  simp [coordSimplex]

theorem continuous_coordSimplex (b : AffineBasis ι ℝ E) : Continuous (coordSimplex b) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).isInducing.continuous_iff]
  exact continuous_pi fun i => by
    simpa only [Function.comp_def, coordSimplex_weights] using
      (continuous_barycentric_coord b i).comp continuous_subtype_val

def fromSimplex (b : AffineBasis ι ℝ E) (t : Convexity.StdSimplex ℝ ι) : E :=
  Finset.univ.affineCombination ℝ b (fun i => t.weights i)

@[simp] theorem coord_fromSimplex (b : AffineBasis ι ℝ E)
    (t : Convexity.StdSimplex ℝ ι) (i : ι) : b.coord i (fromSimplex b t) = t.weights i := by
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) t.total_of_fintype

theorem fromSimplex_mem (b : AffineBasis ι ℝ E) (t : Convexity.StdSimplex ℝ ι) :
    fromSimplex b t ∈ convexHull ℝ (range b) := by
  rw [b.convexHull_eq_nonneg_coord]
  intro i
  simpa using t.weights_nonneg i

def coordEquiv (b : AffineBasis ι ℝ E) :
    convexHull ℝ (range b) ≃ Convexity.StdSimplex ℝ ι where
  toFun := coordSimplex b
  invFun t := ⟨fromSimplex b t, fromSimplex_mem b t⟩
  left_inv x := by
    apply Subtype.ext
    apply b.ext_elem
    intro i
    simp
  right_inv t := by
    ext i
    simp

def coordHomeomorph (b : AffineBasis ι ℝ E) :
    convexHull ℝ (range b) ≃ₜ Convexity.StdSimplex ℝ ι := by
  haveI : CompactSpace (convexHull ℝ (range b)) :=
    isCompact_iff_compactSpace.mp ((Set.finite_range b).isCompact_convexHull ℝ)
  haveI : T2Space (Convexity.StdSimplex ℝ ι) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).t2Space
  exact Continuous.homeoOfEquivCompactToT2 (f := coordEquiv b) (continuous_coordSimplex b)

theorem exists_diskSimplexHomeomorph (n : ℕ) :
    ∃ e : Disk n ≃ₜ StandardSimplex n,
      ∀ x : Disk n, (∀ i, 0 < (e x).weights i) ↔ ‖x.1‖ < 1 := by
  classical
  obtain ⟨b⟩ : Nonempty (AffineBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin n))) := by
    apply AffineBasis.exists_affineBasis_of_finiteDimensional
    simp
  let s : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (range b)
  have hc : Convex ℝ s := convex_convexHull ℝ (range b)
  have hcompact : IsCompact s := (Set.finite_range b).isCompact_convexHull ℝ
  have hne : (interior s).Nonempty := ⟨_, b.centroid_mem_interior_convexHull⟩
  obtain ⟨h, hI, hC, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hcompact.isBounded
  rw [hcompact.isClosed.closure_eq] at hC
  let k : s ≃ₜ Disk n := (h.image s).trans (Homeomorph.setCongr hC)
  have hk (y : s) : (k y).1 = h y.1 := rfl
  have hks (x : Disk n) : h (k.symm x).1 = x.1 := by
    simpa only [hk] using congrArg Subtype.val (k.apply_symm_apply x)
  have hmem (y : EuclideanSpace ℝ (Fin n)) :
      y ∈ interior s ↔ h y ∈ Metric.ball 0 1 := by
    constructor
    · intro hy
      rw [← hI]
      exact mem_image_of_mem h hy
    · intro hy
      rw [← hI] at hy
      obtain ⟨z, hz, hz'⟩ := hy
      simpa only [h.injective hz'] using hz
  refine ⟨k.symm.trans (coordHomeomorph b), fun x => ?_⟩
  change (∀ i, 0 < (coordSimplex b (k.symm x)).weights i) ↔ ‖x.1‖ < 1
  simp only [coordSimplex_weights]
  change (k.symm x).1 ∈ {y | ∀ i, 0 < b.coord i y} ↔ ‖x.1‖ < 1
  rw [← b.interior_convexHull]
  rw [show convexHull ℝ (range b) = s from rfl, hmem, hks]
  simp only [Metric.mem_ball, dist_zero_right]

end P202.Cellular.SimplexParametrization


namespace P202.Topology

theorem diskSimplexParametrization :
    P202Specs.Topology.CellStructures.diskSimplexParametrization :=
  SimplexParametrization.exists_diskSimplexHomeomorph

theorem quotientAdapter : P202Specs.Topology.CellStructures.quotientAdapter.{u, v} :=
  D10Topology.Ch03.quotientMap_iff_mathlib

/-- Local compactness of the interval preserves arbitrary quotient maps.
The topology on each product here is the ordinary product topology. -/
theorem quotientProductInterval :
    P202Specs.Topology.CellStructures.quotientProductInterval.{u, v} := by
  intro P Q _ _ q hq
  apply (D10Topology.Ch03.quotientMap_iff_mathlib _).mp
  refine D10Topology.Ch03.quotient_of_mapping_test _
    (hq.continuous.prodMap continuous_id) ?_ ?_
  · rintro ⟨y, t⟩
    obtain ⟨x, hx⟩ := hq.surjective y
    exact ⟨(x, t), Prod.ext hx rfl⟩
  · intro Z _ g hg
    exact hq.continuous_lift_prod_left hg

theorem negativeSkeleton : P202Specs.Topology.CellStructures.negativeSkeleton.{u} := by
  intro X _ _
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨m, hm, _⟩ := mem_iUnion.mp hx |>.imp fun m hm =>
    mem_iUnion.mp hm
  exact (not_le_of_gt (show (-1 : ℤ) < (m : ℤ) from
    lt_of_lt_of_le (by decide) (Int.natCast_nonneg m))) hm

theorem skeletonIndexing : P202Specs.Topology.CellStructures.skeletonIndexing.{u} := by
  intro X _ _ n
  ext x
  simp only [skeleton, skeletonLT, Int.ofNat_le, Nat.lt_succ_iff]

theorem characteristicProjectionQuotient :
    P202Specs.Topology.CellStructures.characteristicProjectionQuotient.{u} := by
  intro X _ _
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    have hx : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
      rw [CWStructure.cover]
      trivial
    rcases mem_iUnion.mp hx with ⟨n, hx⟩
    rcases mem_iUnion.mp hx with ⟨c, p, hp⟩
    exact ⟨⟨n, c, interiorInclusion n p⟩, hp⟩
  · intro A
    rw [CWStructure.weak_topology, isClosed_sigma_iff]
    constructor
    · intro h n
      exact isClosed_sigma_iff.mpr (h n)
    · intro h n
      exact isClosed_sigma_iff.mp (h n)

theorem continuityTest : P202Specs.Topology.CellStructures.continuityTest.{u, v} := by
  intro X Y _ _ _ f
  rw [D10Topology.Ch03.quotient_continuous_iff (diskProjection X)
    ((quotientAdapter _).mpr characteristicProjectionQuotient) f,
    continuous_sigma_iff]
  exact forall_congr' fun n => continuous_sigma_iff

theorem homotopyContinuityTest :
    P202Specs.Topology.CellStructures.homotopyContinuityTest.{u, v} := by
  intro X Y _ _ _ H
  constructor
  · intro h n c
    exact h.comp ((characteristic X n c).continuous.prodMap continuous_id)
  · intro h
    apply (D10Topology.Ch03.quotient_continuous_iff
      (Prod.map (diskProjection X) (id : Interval → Interval))
      ((quotientAdapter _).mpr (quotientProductInterval _ characteristicProjectionQuotient)) H).mpr
    let e := (Homeomorph.sigmaProdDistrib (X := fun n => Σ _ : Cell X n, Disk n)
      (Y := Interval))
    apply e.symm.isQuotientMap.continuous_iff.mpr
    apply continuous_sigma
    intro n
    let e' := (Homeomorph.sigmaProdDistrib (X := fun _ : Cell X n => Disk n)
      (Y := Interval))
    apply e'.symm.isQuotientMap.continuous_iff.mpr
    exact continuous_sigma (h n)

theorem characteristicDescent :
    P202Specs.Topology.CellStructures.characteristicDescent.{u, v} := by
  intro X Y _ _ _ f hf hfib
  exact D10Topology.Ch03.quotient_descent (diskProjection X)
    ((quotientAdapter _).mpr characteristicProjectionQuotient) f hf hfib

theorem finiteSimplexTopology :
    P202Specs.Topology.CellStructures.finiteSimplexTopology.{u} := by
  intro V _
  exact Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V

theorem simplicialWeakTopology :
    P202Specs.Topology.CellStructures.simplicialWeakTopology.{u} := by
  intro V K A
  exact isOpen_iSup_iff

theorem simplicialChartContinuous {V : Type u} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) : Continuous (K.simplexChart s) :=
  continuous_iSup_rng (i := s) continuous_coinduced_rng

theorem simplicialHausdorff :
    P202Specs.Topology.CellStructures.simplicialHausdorff.{u} := by
  intro V K
  let coeff : K.Realization → V → ℝ := fun p => p.1.weights
  have hc : Continuous coeff := by
    change Continuous[⨆ s : K.Simplex,
      TopologicalSpace.coinduced (K.simplexChart s) inferInstance, _] coeff
    rw [continuous_iSup_dom]
    intro s
    rw [continuous_coinduced_dom]
    apply continuous_pi
    intro v
    exact (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) v).comp
      (Convexity.StdSimplex.continuous_map ℝ (Subtype.val : s.1 → V))
  apply T2Space.of_injective_continuous (f := coeff) _ hc
  intro p q hpq
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  exact Finsupp.ext (congrFun hpq)

theorem simplicialChartEmbedding :
    P202Specs.Topology.CellStructures.simplicialChartEmbedding.{u} := by
  intro V K s
  have : T2Space K.Realization := simplicialHausdorff K
  apply Continuous.isClosedEmbedding (simplicialChartContinuous K s) _ |>.isEmbedding
  intro p q hpq
  apply Convexity.StdSimplex.ext
  apply Finsupp.mapDomain_injective (Subtype.val_injective :
    Function.Injective (Subtype.val : s.1 → V))
  exact congrArg (fun z : K.Realization => z.1.weights) hpq

theorem deltaFaceCompatibility :
    P202Specs.Topology.CellStructures.deltaFaceCompatibility.{u} := by
  intro D m n a c t
  exact Quotient.sound (Relation.EqvGen.rel _ _ (DeltaComplex.FaceRelation.face a c t))

theorem deltaProjectionQuotient :
    P202Specs.Topology.CellStructures.deltaProjectionQuotient.{u} := by
  intro D
  exact isQuotientMap_quotient_mk'

private theorem interiorInclusion_dense (n : ℕ) : DenseRange (interiorInclusion n) := by
  apply Subtype.dense_iff.mpr
  have hi : (Subtype.val : Disk n → EuclideanSpace ℝ (Fin n)) ''
      range (interiorInclusion n) = Metric.ball 0 1 := by
    ext x
    constructor
    · rintro ⟨p, ⟨q, rfl⟩, rfl⟩
      exact q.2
    · intro hx
      exact ⟨⟨x, Metric.ball_subset_closedBall hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  rw [hi, closure_ball _ one_ne_zero]

theorem closureOpenCell : P202Specs.Topology.CellStructures.closureOpenCell.{u} := by
  intro X _ _ n c
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : IsClosed (closedCell X n c) :=
    (isCompact_range (characteristic X n c).continuous).isClosed
  apply Subset.antisymm
  · apply closure_minimal _ hc
    rintro x ⟨p, rfl⟩
    exact ⟨interiorInclusion n p, rfl⟩
  · have h := image_closure_subset_closure_image (characteristic X n c).continuous
      (s := range (interiorInclusion n))
    rw [(interiorInclusion_dense n).closure_range, image_univ, ← range_comp] at h
    exact h

private theorem disk_cases (n : ℕ) (x : Disk n) :
    (∃ p : OpenDisk n, interiorInclusion n p = x) ∨
    (∃ p : Sphere n, boundaryInclusion n p = x) := by
  have hx : ‖x.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
  rcases lt_or_eq_of_le hx with h | h
  · left
    exact ⟨⟨x.1, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩, rfl⟩
  · right
    exact ⟨⟨x.1, by simpa only [Metric.mem_sphere, dist_zero_right] using h⟩, rfl⟩

theorem openCellDisjointSkeletonLT {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) : Disjoint (openCell X n c) (skeletonLT X n) := by
  simp only [skeletonLT, disjoint_iUnion_right]
  intro m hmn d
  apply CWStructure.disjoint_interiors (mem_univ ⟨n, c⟩) (mem_univ ⟨m, d⟩)
  intro heq
  have hnm : n = m := congrArg Sigma.fst heq
  exact (Nat.ne_of_lt hmn) hnm.symm

theorem attachmentPushout : P202Specs.Topology.CellStructures.attachmentPushout.{u, v} := by
  intro X Y _ _ _ n f g hboundary
  let a := attachingMap (X := X) n
  have on_old (c : Cell X n) (x : Disk n) (z : skeletonLT X n)
      (hx : characteristic X n c x = z.1) : g c x = f z := by
    rcases disk_cases n x with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact False.elim (Set.disjoint_left.mp (openCellDisjointSkeletonLT n c)
        ⟨p, rfl⟩ (by
          change characteristic X n c (interiorInclusion n p) ∈ skeletonLT X n
          rw [hx]
          exact z.2))
    · have hz : attachingMap n c p = z := Subtype.ext hx
      rw [hboundary, hz]
  have on_disks (c d : Cell X n) (x y : Disk n)
      (hxy : characteristic X n c x = characteristic X n d y) : g c x = g d y := by
    rcases disk_cases n x with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · rcases disk_cases n y with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · have hcd : c = d := by
          have heq : (⟨n, c⟩ : Σ k, Cell X k) = ⟨n, d⟩ := by
            by_contra hne
            exact Set.disjoint_left.mp
              (CWStructure.disjoint_interiors (mem_univ _) (mem_univ _) hne)
              ⟨p, rfl⟩ ⟨q, hxy.symm⟩
          simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using heq
        subst d
        have hpq : p = q := (CWStructure.interior_embedding n c).injective hxy
        rw [hpq]
      · exact on_old c (interiorInclusion n p) (a d q) hxy |>.trans (hboundary d q).symm
    · exact (hboundary c p).trans (on_old d y (a c p) hxy.symm).symm
  let F : (skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) → Y :=
    Sum.elim f (fun p => g p.1 p.2)
  have hF : Continuous F := continuous_sum_dom.mpr
    ⟨f.continuous, continuous_sigma fun c => (g c).continuous⟩
  have hfib : ∀ p q, attachmentProjection X CWStructure.boundary_lands n p =
      attachmentProjection X CWStructure.boundary_lands n q → F p = F q := by
    intro p q hpq
    have hpq' := congrArg Subtype.val hpq
    cases p with
    | inl x =>
      cases q with
      | inl y => exact congrArg f (Subtype.ext hpq')
      | inr y => exact (on_old y.1 y.2 x hpq'.symm).symm
    | inr x =>
      cases q with
      | inl y => exact on_old x.1 x.2 y hpq'
      | inr y => exact on_disks x.1 y.1 x.2 y.2 hpq'
  obtain ⟨h, ⟨hc, hh⟩, huniq⟩ := D10Topology.Ch03.quotient_descent
    (attachmentProjection X CWStructure.boundary_lands n)
    ((quotientAdapter _).mpr (CWStructure.attachment_quotient n)) F hF hfib
  refine ⟨⟨h, hc⟩, ⟨?_, ?_⟩, ?_⟩
  · intro x
    exact congrFun hh (Sum.inl x)
  · intro c x
    exact congrFun hh (Sum.inr ⟨c, x⟩)
  · intro k hk
    have heq : (k : _ → Y) = h := huniq k ⟨k.continuous, by
      funext p
      cases p with
      | inl x => exact hk.1 x
      | inr x => exact hk.2 x.1 x.2⟩
    exact ContinuousMap.ext (congrFun heq)

/-- Closure finiteness and the weak topology detect closed sets supported on a
bounded skeleton using only the disks in that skeleton. No attachment axiom is
assumed here. -/
theorem isClosed_of_skeleton_cellwise
    {X : Type u} [TopologicalSpace X] [T2Space X] [CellStructure X]
    (hd : (univ : Set (Σ n, Cell X n)).PairwiseDisjoint
      (fun c => openCell X c.1 c.2))
    (hf : ∀ n (c : Cell X n), ∃ F : Finset (Σ m, Cell X m),
      closedCell X n c ⊆ ⋃ d ∈ F, openCell X d.1 d.2)
    (hw : ∀ B : Set X, IsClosed B ↔
      ∀ n (c : Cell X n), IsClosed (characteristic X n c ⁻¹' B))
    (n : ℕ) (B : Set X) (hB : B ⊆ skeletonLT X n)
    (hlow : ∀ m < n, ∀ c : Cell X m, IsClosed (characteristic X m c ⁻¹' B)) :
    IsClosed B := by
  classical
  have hcell (m : ℕ) (c : Cell X m) : IsClosed (closedCell X m c) := by
    have : CompactSpace (Disk m) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    exact (isCompact_range (characteristic X m c).continuous).isClosed
  have hlo (m : ℕ) (hm : m < n) (c : Cell X m) :
      IsClosed (B ∩ closedCell X m c) := by
    have : CompactSpace (Disk m) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    have heq : characteristic X m c '' (characteristic X m c ⁻¹' B) =
        B ∩ closedCell X m c := by
      ext x
      simp only [mem_image, mem_preimage, mem_inter_iff, closedCell, mem_range]
      aesop
    rw [← heq]
    exact ((hlow m hm c).isCompact.image (characteristic X m c).continuous).isClosed
  apply (hw B).mpr
  intro k c
  obtain ⟨F, hF⟩ := hf k c
  let G := F.filter (fun d => d.1 < n)
  have hG : IsClosed (⋃ d ∈ G, B ∩ closedCell X d.1 d.2) := by
    apply isClosed_biUnion_finset
    intro d hdG
    exact hlo d.1 (Finset.mem_filter.mp hdG).2 d.2
  have heq : B ∩ closedCell X k c =
      closedCell X k c ∩ ⋃ d ∈ G, B ∩ closedCell X d.1 d.2 := by
    ext x
    constructor
    · rintro ⟨hxB, hxc⟩
      obtain ⟨d, hdF, hxd⟩ := mem_iUnion.mp (hF hxc) |>.imp fun d h => mem_iUnion.mp h
      obtain ⟨m, hm, a, hxa⟩ := by
        simpa only [skeletonLT, mem_iUnion] using hB hxB
      have he : d = (⟨m, a⟩ : Σ m, Cell X m) := by
        by_contra hne
        exact Set.disjoint_left.mp (hd (mem_univ d) (mem_univ _) hne) hxd hxa
      have hdn : d.1 < n := by simpa only [he] using hm
      refine ⟨hxc, mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hdF, hdn⟩,
        hxB, ?_⟩⟩⟩
      obtain ⟨p, hp⟩ := hxd
      exact ⟨interiorInclusion d.1 p, hp⟩
    · rintro ⟨hxc, hx⟩
      obtain ⟨d, _, hxd⟩ := mem_iUnion.mp hx |>.imp fun d h => mem_iUnion.mp h
      exact ⟨hxd.1, hxc⟩
  have hc : IsClosed (B ∩ closedCell X k c) := heq ▸ (hcell k c).inter hG
  have heq' : characteristic X k c ⁻¹' (B ∩ closedCell X k c) =
      characteristic X k c ⁻¹' B := by
    ext p
    simp only [mem_preimage, mem_inter_iff]
    exact and_iff_left ⟨p, rfl⟩
  exact heq' ▸ hc.preimage (characteristic X k c).continuous

theorem skeletonLT_mono {X : Type u} [TopologicalSpace X] [CellStructure X]
    {m n : ℕ} (hmn : m ≤ n) : skeletonLT X m ⊆ skeletonLT X n := by
  intro x hx
  obtain ⟨k, hk, c, hxc⟩ := by simpa only [skeletonLT, mem_iUnion] using hx
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨lt_of_lt_of_le hk hmn, mem_iUnion.mpr ⟨c, hxc⟩⟩⟩

/-- Whitehead's closure-finite weak-topology conditions give the attachment
topology on the actual subspace skeleta. Compare Hatcher, Appendix A.2. -/
theorem skeletalAttachmentQuotient
    {X : Type u} [TopologicalSpace X] [T2Space X] [CellStructure X]
    (hd : (univ : Set (Σ n, Cell X n)).PairwiseDisjoint
      (fun c => openCell X c.1 c.2))
    (hb : ∀ n (c : Cell X n), MapsTo (boundaryMap X n c) univ (skeletonLT X n))
    (hf : ∀ n (c : Cell X n), ∃ F : Finset (Σ m, Cell X m),
      closedCell X n c ⊆ ⋃ d ∈ F, openCell X d.1 d.2)
    (hw : ∀ B : Set X, IsClosed B ↔
      ∀ n (c : Cell X n), IsClosed (characteristic X n c ⁻¹' B))
    (n : ℕ) : IsQuotientMap (attachmentProjection X hb n) := by
  have hc : Continuous (attachmentProjection X hb n) := by
    apply continuous_sum_dom.mpr
    constructor
    · exact continuous_subtype_val.subtype_mk _
    · apply continuous_sigma
      intro c
      exact (characteristic X n c).continuous.subtype_mk _
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    obtain ⟨m, hm, c, p, hp⟩ := by
      simpa only [skeletonLT, mem_iUnion, openCell, mem_range] using x.2
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hmn | heq
    · exact ⟨Sum.inl ⟨x.1, mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn,
        mem_iUnion.mpr ⟨c, ⟨p, hp⟩⟩⟩⟩⟩, Subtype.ext rfl⟩
    · subst m
      exact ⟨Sum.inr ⟨c, interiorInclusion n p⟩, Subtype.ext hp⟩
  · intro A
    constructor
    · exact fun h => h.preimage hc
    · intro hA
      let B : Set X := Subtype.val '' A
      have hB : B ⊆ skeletonLT X (n + 1) := by
        rintro x ⟨a, _, rfl⟩
        exact a.2
      have hmem (a : skeletonLT X (n + 1)) : a.1 ∈ B ↔ a ∈ A := by
        simp only [B, mem_image]
        constructor
        · rintro ⟨b, hb, he⟩
          exact (Subtype.ext he : b = a) ▸ hb
        · exact fun ha => ⟨a, ha, rfl⟩
      have hold : IsClosed (oldSkeletonInclusion X n ⁻¹' A) :=
        hA.preimage continuous_inl
      have hnew (c : Cell X n) : IsClosed (diskToSkeleton X hb n c ⁻¹' A) :=
        hA.preimage (continuous_inr.comp continuous_sigmaMk)
      have hclosed : IsClosed B := by
        apply isClosed_of_skeleton_cellwise hd hf hw (n + 1) B hB
        intro m hm c
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hmn | heq
        · let lift : Disk m → skeletonLT X n := fun p =>
            ⟨characteristic X m c p,
              skeletonLT_mono (Nat.succ_le_of_lt hmn) (diskToSkeleton X hb m c p).2⟩
          have hlift : Continuous lift := (characteristic X m c).continuous.subtype_mk _
          have heq : characteristic X m c ⁻¹' B =
              lift ⁻¹' (oldSkeletonInclusion X n ⁻¹' A) := by
            ext p
            exact hmem (oldSkeletonInclusion X n (lift p))
          rw [heq]
          exact hold.preimage hlift
        · subst m
          have heq : characteristic X n c ⁻¹' B = diskToSkeleton X hb n c ⁻¹' A := by
            ext p
            exact hmem (diskToSkeleton X hb n c p)
          rw [heq]
          exact hnew c
      have heq : Subtype.val ⁻¹' B = A := by
        ext a
        exact hmem a
      rw [← heq]
      exact hclosed.preimage continuous_subtype_val

/-- Construct a CW structure without separately assuming skeletal quotient
maps. The characteristic maps and cell indices are retained unchanged. -/
@[instance_reducible] def cwStructureOfWeak
    {X : Type u} [TopologicalSpace X] [T2Space X] [CellStructure X]
    (hi : ∀ n (c : Cell X n), IsEmbedding (interiorMap X n c))
    (hd : (univ : Set (Σ n, Cell X n)).PairwiseDisjoint
      (fun c => openCell X c.1 c.2))
    (hc : ⋃ (n : ℕ) (c : Cell X n), openCell X n c = univ)
    (hb : ∀ n (c : Cell X n), MapsTo (boundaryMap X n c) univ (skeletonLT X n))
    (hf : ∀ n (c : Cell X n), ∃ F : Finset (Σ m, Cell X m),
      closedCell X n c ⊆ ⋃ d ∈ F, openCell X d.1 d.2)
    (hw : ∀ B : Set X, IsClosed B ↔
      ∀ n (c : Cell X n), IsClosed (characteristic X n c ⁻¹' B)) : CWStructure X where
  toCellStructure := inferInstance
  hausdorff := inferInstance
  interior_embedding := hi
  disjoint_interiors := hd
  cover := hc
  boundary_lands := hb
  closure_finite := hf
  weak_topology := hw
  attachment_quotient := skeletalAttachmentQuotient hd hb hf hw

theorem weakCWConstructor : P202Specs.Topology.CellStructures.weakCWConstructor.{u} := by
  intro X _ _ S hi hd hc hb hf hw
  exact ⟨cwStructureOfWeak hi hd hc hb hf hw, rfl⟩

/-- A closed simplex chart consists exactly of points supported on its vertices. -/
theorem simplicialChart_range {V : Type u} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (p : K.Realization) :
    p ∈ range (K.simplexChart s) ↔ p.1.weights.support ⊆ s.1 := by
  classical
  constructor
  · rintro ⟨t, rfl⟩ v hv
    have hv' := Finsupp.mapDomain_support hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv'
    exact a.2
  · intro hp
    have hzero : ∀ v : V, v ∉ range (Subtype.val : s.1 → V) → p.1.weights v = 0 := by
      intro v hv
      apply Finsupp.notMem_support_iff.mp
      exact fun h => hv ⟨⟨v, hp h⟩, rfl⟩
    obtain ⟨t, ht⟩ := (Convexity.StdSimplex.mem_range_map_iff
      (Subtype.val : s.1 → V) p.1).mpr hzero
    exact ⟨t, Subtype.ext ht⟩

/-- The simplex interior is precisely the stratum with that exact support. -/
theorem simplicialChart_interior {V : Type u} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (p : K.Realization) :
    p ∈ K.simplexChart s '' K.simplexInterior s ↔ p.1.weights.support = s.1 := by
  classical
  have hs (t : K.GeometricSimplex s) :
      (K.simplexChart s t).1.weights.support =
        t.weights.support.image (Subtype.val : s.1 → V) :=
    Finsupp.mapDomain_support_of_injective Subtype.val_injective _
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [hs]
    ext v
    constructor
    · intro hv
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
      exact a.2
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finsupp.mem_support_iff.mpr (ht ⟨v, hv⟩).ne', rfl⟩
  · intro hp
    obtain ⟨t, rfl⟩ := (simplicialChart_range K s p).mpr hp.subset
    refine ⟨t, ?_, rfl⟩
    intro v
    apply lt_of_le_of_ne (t.nonneg v)
    intro hv
    have hvs : v.1 ∈ (K.simplexChart s t).1.weights.support := hp.symm ▸ v.2
    rw [hs] at hvs
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hvs
    have hav : a = v := Subtype.ext he
    exact (Finsupp.mem_support_iff.mp ha) (hav ▸ hv.symm)

/-- Every realization point has one and only one simplex-interior label. -/
theorem simplicialInteriorPartition {V : Type u} (K : AbstractSimplicialComplex V)
    (p : K.Realization) : ∃! s : K.Simplex,
      p ∈ K.simplexChart s '' K.simplexInterior s := by
  refine ⟨⟨p.1.weights.support, p.2⟩, (simplicialChart_interior K _ p).mpr rfl, ?_⟩
  intro s hs
  exact Subtype.ext ((simplicialChart_interior K s p).mp hs).symm

theorem deltaChartContinuous (D : DeltaComplex.{u}) (n : ℕ) (c : D.Simplex n) :
    Continuous (D.simplexChart n c) :=
  continuous_quotient_mk'.comp (continuous_sigmaMk.comp continuous_sigmaMk)

theorem deltaWeakTopology (D : DeltaComplex.{u}) (A : Set D.Realization) :
    IsOpen A ↔ ∀ n (c : D.Simplex n), IsOpen (D.simplexChart n c ⁻¹' A) := by
  calc
    IsOpen A ↔ IsOpen (Quotient.mk D.faceSetoid ⁻¹' A) :=
      (deltaProjectionQuotient D).isCoinducing.isOpen_preimage.symm
    _ ↔ _ := by
      rw [isOpen_sigma_iff]
      exact forall_congr' fun n => isOpen_sigma_iff

end P202.Topology

namespace P202.Topology

theorem isEmbedding_restrict_of_isClosedMap
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (f : A → X) (hf : Continuous f) (hclosed : IsClosedMap f)
    (U : Set A) (hsat : f ⁻¹' (f '' U) = U) (hinj : Set.InjOn f U) :
    IsEmbedding (U.domRestrict f) := by
  let B := f '' U
  let e : U ≃ₜ (f ⁻¹' B) := Homeomorph.setCongr hsat.symm
  let g : (f ⁻¹' B) → B := B.restrictPreimage f
  have hgcont : Continuous g := hf.restrictPreimage
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    · exact hsat ▸ x.2
    · exact hsat ▸ y.2
    · exact congrArg Subtype.val hxy
  have hg : IsEmbedding g :=
    (IsClosedEmbedding.of_continuous_injective_isClosedMap hgcont hginj
      (hclosed.restrictPreimage B)).isEmbedding
  exact IsEmbedding.subtypeVal.comp (hg.comp e.isEmbedding)

end P202.Topology

namespace P202.SimplicialGeometry
open P202.Topology

abbrev SimplicialCell {V : Type u} (K : AbstractSimplicialComplex V) (n : ℕ) :=
  {s : K.Simplex // s.1.card = n + 1}

@[instance_reducible] def simplicialCells {V : Type u} (K : AbstractSimplicialComplex V)
    (e : ∀ n (c : SimplicialCell K n), Disk n ≃ₜ K.GeometricSimplex c.1) :
    CellStructure K.Realization where
  Cell := SimplicialCell K
  characteristic n c := ⟨K.simplexChart c.1 ∘ e n c,
    (simplicialChartContinuous K c.1).comp (e n c).continuous⟩

theorem simplicialCells_openCell {V : Type u} (K : AbstractSimplicialComplex V)
    (e : ∀ n (c : SimplicialCell K n), Disk n ≃ₜ K.GeometricSimplex c.1)
    (hi : ∀ n (c : SimplicialCell K n) (x : Disk n),
      e n c x ∈ K.simplexInterior c.1 ↔ ‖x.1‖ < 1)
    (n : ℕ) (c : SimplicialCell K n) :
    letI := simplicialCells K e
    openCell K.Realization n c = K.simplexChart c.1 '' K.simplexInterior c.1 := by
  letI := simplicialCells K e
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e n c (interiorInclusion n x),
      (hi n c _).mpr (by
        change ‖x.1‖ < 1
        simpa only [Metric.mem_ball, dist_zero_right] using x.2), rfl⟩
  · rintro ⟨t, ht, rfl⟩
    have hx : ‖((e n c).symm t).1‖ < 1 := (hi n c _).mp (by simpa)
    exact ⟨⟨((e n c).symm t).1, by simpa [Metric.mem_ball, dist_zero_right] using hx⟩,
      by
        change K.simplexChart c.1 (e n c ((e n c).symm t)) = _
        simp
    ⟩


def simplexCell {V : Type u} (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    SimplicialCell K (s.1.card - 1) :=
  ⟨s, by have := Finset.card_pos.mpr (K.nonempty _ s.2); omega⟩

theorem simplicialCell_label_injective {V : Type u} (K : AbstractSimplicialComplex V) :
    Function.Injective (fun d : Σ n, SimplicialCell K n => d.2.1.1) := by
  rintro ⟨n, c⟩ ⟨m, d⟩ h
  change c.1.1 = d.1.1 at h
  have hnm : n = m := by
    have hcard := congrArg Finset.card h
    have hc := c.2
    have hd := d.2
    omega
  subst m
  have hcd : c = d := Subtype.ext (Subtype.ext h)
  subst d
  rfl

set_option maxHeartbeats 600000 in
theorem simplicialRealizationCW_of_homeomorphs {V : Type u}
    (K : AbstractSimplicialComplex V)
    (e : ∀ n (c : SimplicialCell K n), Disk n ≃ₜ K.GeometricSimplex c.1)
    (hi : ∀ n (c : SimplicialCell K n) (x : Disk n),
      e n c x ∈ K.simplexInterior c.1 ↔ ‖x.1‖ < 1) :
    ∃ (C : CWStructure K.Realization)
      (indices : ∀ n, C.toCellStructure.Cell n ≃ SimplicialCell K n),
      letI : CWStructure K.Realization := C
      ∀ n (c : Cell K.Realization n),
        let s := (indices n c).1
        openCell K.Realization n c = K.simplexChart s '' K.simplexInterior s ∧
        ∃ e : Disk n ≃ₜ K.GeometricSimplex s,
          (characteristic K.Realization n c : Disk n → K.Realization) =
            K.simplexChart s ∘ e := by
  classical
  letI := simplicialCells K e
  letI : T2Space K.Realization := simplicialHausdorff K
  have hopen := simplicialCells_openCell K e hi
  have hopen' (n : ℕ) (c : Cell K.Realization n) (p : K.Realization) :
      p ∈ openCell K.Realization n c ↔
        p ∈ K.simplexChart c.1 '' K.simplexInterior c.1 := by rw [hopen]
  have hem (n : ℕ) (c : Cell K.Realization n) :
      IsEmbedding (interiorMap K.Realization n c) := by
    exact (simplicialChartEmbedding K c.1).comp ((e n c).isEmbedding.comp
      (.inclusion (Metric.ball_subset_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1))))
  have hdis : (univ : Set (Σ n, Cell K.Realization n)).PairwiseDisjoint
      (fun c => openCell K.Realization c.1 c.2) := by
    intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro p hpa hpb
    have hsa : p.1.weights.support = a.2.1.1 :=
      (simplicialChart_interior K a.2.1 p).mp ((hopen' a.1 a.2 p).mp hpa)
    have hsb : p.1.weights.support = b.2.1.1 :=
      (simplicialChart_interior K b.2.1 p).mp ((hopen' b.1 b.2 p).mp hpb)
    exact hab (simplicialCell_label_injective K (hsa.symm.trans hsb))
  have hcover : ⋃ (n : ℕ) (c : Cell K.Realization n), openCell K.Realization n c = univ := by
    apply Set.eq_univ_of_forall
    intro p
    let s : K.Simplex := ⟨p.1.weights.support, p.2⟩
    refine mem_iUnion.mpr ⟨s.1.card - 1, mem_iUnion.mpr ⟨simplexCell K s, ?_⟩⟩
    exact (hopen' _ _ _).mpr ((simplicialChart_interior K s p).mpr rfl)
  have hboundary (n : ℕ) (c : Cell K.Realization n) :
      MapsTo (boundaryMap K.Realization n c) univ (skeletonLT K.Realization n) := by
    intro x _
    let p : K.Realization := boundaryMap K.Realization n c x
    let s : K.Simplex := ⟨p.1.weights.support, p.2⟩
    have hsub : s.1 ⊆ c.1.1 := (simplicialChart_range K c.1 p).mp ⟨e n c (boundaryInclusion n x), rfl⟩
    have hne : s.1 ≠ c.1.1 := by
      intro heq
      obtain ⟨t, ht, he⟩ := (simplicialChart_interior K c.1 p).mpr heq
      have het : t = e n c (boundaryInclusion n x) := (simplicialChartEmbedding K c.1).injective he
      have ht' : e n c (boundaryInclusion n x) ∈ K.simplexInterior c.1 := het ▸ ht
      have hnorm : ‖x.1‖ < 1 := (hi n c (boundaryInclusion n x)).mp ht'
      have heqnorm : ‖x.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.2
      exact (ne_of_lt hnorm) heqnorm
    have hcard : s.1.card < c.1.1.card := Finset.card_lt_card (lt_of_le_of_ne hsub hne)
    have hdim : s.1.card - 1 < n := by
      have hs := Finset.card_pos.mpr (K.nonempty _ s.2)
      have hc := c.2
      omega
    refine mem_iUnion.mpr ⟨s.1.card - 1, mem_iUnion.mpr ⟨hdim,
      mem_iUnion.mpr ⟨simplexCell K s, ?_⟩⟩⟩
    exact (hopen' _ _ _).mpr ((simplicialChart_interior K s p).mpr rfl)
  have hfinite (n : ℕ) (c : Cell K.Realization n) :
      ∃ F : Finset (Σ m, Cell K.Realization m),
        closedCell K.Realization n c ⊆ ⋃ d ∈ F, openCell K.Realization d.1 d.2 := by
    let I : Set (Σ m, Cell K.Realization m) := {d | d.2.1.1 ⊆ c.1.1}
    have hI : I.Finite := by
      have hIeq : I = (fun d : Σ m, SimplicialCell K m => d.2.1.1) ⁻¹' (↑c.1.1.powerset : Set (Finset V)) := by
        ext d
        exact Finset.mem_powerset.symm
      rw [hIeq]
      exact (Finset.finite_toSet (c.1.1.powerset)).preimage
        (simplicialCell_label_injective K).injOn
    refine ⟨hI.toFinset, ?_⟩
    rintro p ⟨x, rfl⟩
    let p : K.Realization := characteristic K.Realization n c x
    let s : K.Simplex := ⟨p.1.weights.support, p.2⟩
    let d : Σ m, Cell K.Realization m := ⟨s.1.card - 1, simplexCell K s⟩
    have hd : d ∈ hI.toFinset := by
      apply hI.mem_toFinset.mpr
      exact (simplicialChart_range K c.1 p).mp ⟨e n c x, rfl⟩
    refine mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨hd, ?_⟩⟩
    exact (hopen' _ _ _).mpr ((simplicialChart_interior K s p).mpr rfl)
  have hweak (A : Set K.Realization) : IsClosed A ↔
      ∀ n (c : Cell K.Realization n), IsClosed (characteristic K.Realization n c ⁻¹' A) := by
    have hk : IsClosed A ↔ ∀ s : K.Simplex, IsClosed (K.simplexChart s ⁻¹' A) :=
      by
        change IsClosed[⨆ s : K.Simplex, TopologicalSpace.coinduced (K.simplexChart s) inferInstance] A ↔ _
        simp only [isClosed_iSup_iff, isClosed_coinduced]
    constructor
    · intro h n c
      exact h.preimage (characteristic K.Realization n c).continuous
    · intro h
      apply hk.mpr
      intro s
      let c := simplexCell K s
      exact (e _ c).isQuotientMap.isCoinducing.isClosed_preimage.mp (h _ c)
  let C := cwStructureOfWeak hem hdis hcover hboundary hfinite hweak
  refine ⟨C, fun n => Equiv.refl _, ?_⟩
  intro n c
  exact ⟨hopen n c, e n c, rfl⟩


def simplexRelabel {A : Type u} {B : Type v} (a : A ≃ B) :
    Convexity.StdSimplex ℝ A ≃ₜ Convexity.StdSimplex ℝ B where
  toFun := Convexity.StdSimplex.map a
  invFun := Convexity.StdSimplex.map a.symm
  left_inv t := by
    ext i
    change Finsupp.mapDomain a.symm (Finsupp.mapDomain a t.weights) i = _
    simp
  right_inv t := by
    ext i
    change Finsupp.mapDomain a (Finsupp.mapDomain a.symm t.weights) i = _
    simp
  continuous_toFun := Convexity.StdSimplex.continuous_map ℝ a
  continuous_invFun := Convexity.StdSimplex.continuous_map ℝ a.symm

theorem exists_simplicialDiskHomeomorph {V : Type u}
    (K : AbstractSimplicialComplex V) (n : ℕ) (c : SimplicialCell K n) :
    ∃ e : Disk n ≃ₜ K.GeometricSimplex c.1,
      ∀ x : Disk n, e x ∈ K.simplexInterior c.1 ↔ ‖x.1‖ < 1 := by
  classical
  let a : Fin (n + 1) ≃ c.1.1 := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using c.2.symm)
  obtain ⟨e, he⟩ := diskSimplexParametrization n
  refine ⟨e.trans (simplexRelabel a), fun x => ?_⟩
  rw [← he x]
  change (∀ v, 0 < ((e x).map a).weights v) ↔ _
  change (∀ v, 0 < Finsupp.mapDomain a (e x).weights v) ↔ _
  simp only [Finsupp.mapDomain_equiv_apply]
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (a i)
  · intro h v
    exact h (a.symm v)

end P202.SimplicialGeometry

namespace P202.Topology

theorem simplicialRealizationCW : P202Specs.Topology.CellStructures.simplicialRealizationCW.{u} := by
  intro V K
  choose e he using SimplicialGeometry.exists_simplicialDiskHomeomorph K
  exact SimplicialGeometry.simplicialRealizationCW_of_homeomorphs K e he

end P202.Topology

namespace P202.Topology.DeltaSupport

/-- Restriction to the actual nonzero barycentric coordinates. -/
def supportedSimplex {V : Type*} (t : Convexity.StdSimplex ℝ V) :
    Convexity.StdSimplex ℝ t.weights.support where
  weights := t.weights.subtypeDomain (· ∈ t.weights.support)
  nonneg := fun v => t.nonneg v
  total := (Finsupp.sum_subtypeDomain_index (fun _ hv => hv)).trans t.total

lemma supportedSimplex_positive {V : Type*} (t : Convexity.StdSimplex ℝ V)
    (v : t.weights.support) : 0 < (supportedSimplex t).weights v := by
  exact lt_of_le_of_ne (t.nonneg v) (Finsupp.mem_support_iff.mp v.2).symm

lemma supportedSimplex_map {V : Type*} (t : Convexity.StdSimplex ℝ V) :
    (supportedSimplex t).map (Subtype.val : t.weights.support → V) = t := by
  ext v
  by_cases hv : v ∈ t.weights.support
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨v, hv⟩
  · change ((supportedSimplex t).weights.mapDomain Subtype.val) v = t.weights v
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simpa using hv),
      Finsupp.notMem_support_iff.mp hv]

lemma interior_support {n : ℕ} {t : StandardSimplex n}
    (ht : t ∈ standardSimplexInterior n) : t.weights.support = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true, Finsupp.mem_support_iff]
  exact (ht v).ne'

lemma orderedFace_support {m n : ℕ} (a : Fin (m + 1) ↪o Fin (n + 1))
    (t : StandardSimplex m) :
    (orderedAffineFace a t).weights.support = t.weights.support.image a :=
  Finsupp.mapDomain_support_of_injective a.injective _

lemma orderedFace_injective {m n : ℕ} (a : Fin (m + 1) ↪o Fin (n + 1)) :
    Function.Injective (orderedAffineFace a) := by
  intro t u h
  exact Convexity.StdSimplex.ext
    (Finsupp.mapDomain_injective a.injective (congrArg Convexity.StdSimplex.weights h))

lemma positive_face_unique {m k n : ℕ}
    (a : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (k + 1) ↪o Fin (n + 1))
    (t : StandardSimplex m) (u : StandardSimplex k)
    (ht : t ∈ standardSimplexInterior m) (hu : u ∈ standardSimplexInterior k)
    (h : orderedAffineFace a t = orderedAffineFace b u) :
    m = k ∧ HEq a b ∧ HEq t u := by
  classical
  have hs : Finset.univ.image a = Finset.univ.image b := by
    simpa only [orderedFace_support, interior_support ht, interior_support hu]
      using congrArg (fun t => t.weights.support) h
  have hmk : m = k := by
    have := congrArg Finset.card hs
    simpa only [Finset.card_image_of_injective _ a.injective,
      Finset.card_image_of_injective _ b.injective, Finset.card_univ, Fintype.card_fin,
      Nat.succ.injEq] using this
  subst k
  have hbcard : (Finset.univ.image b).card = m + 1 := by
    rw [Finset.card_image_of_injective _ b.injective]
    simp
  have hab : a = b := by
    apply Finset.orderEmbOfFin_unique' (s := Finset.univ.image b) hbcard
      (fun x => by rw [← hs]; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
      |>.trans ?_
    exact (Finset.orderEmbOfFin_unique' (s := Finset.univ.image b) hbcard
      (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)).symm
  subst b
  exact ⟨rfl, HEq.rfl, heq_of_eq (orderedFace_injective a h)⟩

/-- Each barycentric point comes from the positive interior of a uniquely
ordered support face. This statement supplies existence; relation invariance
and uniqueness of quotient representatives are separate obligations. -/
theorem exists_interior_face {n : ℕ} (t : StandardSimplex n) :
    ∃ (m : ℕ) (_ : m ≤ n) (a : Fin (m + 1) ↪o Fin (n + 1))
      (u : StandardSimplex m),
      u ∈ standardSimplexInterior m ∧ orderedAffineFace a u = t := by
  classical
  let s := t.weights.support
  have hs : 0 < s.card := t.support_weights_nonempty.card_pos
  let m := s.card - 1
  have hcard : s.card = m + 1 := (Nat.sub_add_cancel hs).symm
  let e : Fin (m + 1) ≃o s := s.orderIsoOfFin hcard
  let a : Fin (m + 1) ↪o Fin (n + 1) := s.orderEmbOfFin hcard
  let u : StandardSimplex m := (supportedSimplex t).map e.symm
  refine ⟨m, ?_, a, u, ?_, ?_⟩
  · have hbound : s.card ≤ n + 1 := by
      exact (Finset.card_le_card (Finset.subset_univ s)).trans_eq (by simp)
    omega
  · intro v
    change 0 < ((supportedSimplex t).weights.mapDomain e.symm) v
    rw [← e.symm_apply_apply v]
    rw [Finsupp.mapDomain_apply_of_injective e.symm.injective]
    exact supportedSimplex_positive t _
  · change (supportedSimplex t |>.map e.symm).map a = t
    rw [Convexity.StdSimplex.map_map]
    have he : (fun x : s => a (e.symm x)) = Subtype.val := by
      funext x
      change (e (e.symm x)).1 = x.1
      rw [e.apply_symm_apply]
    rw [he]
    exact supportedSimplex_map t

def IsInteriorRepresentative (D : DeltaComplex) (p r : D.SimplexSum) : Prop :=
  r.2.2 ∈ standardSimplexInterior r.1 ∧
    ∃ a : Fin (r.1 + 1) ↪o Fin (p.1 + 1),
      D.face a p.2.1 = r.2.1 ∧ orderedAffineFace a r.2.2 = p.2.2

lemma exists_interior_representative (D : DeltaComplex) (p : D.SimplexSum) :
    ∃ r, IsInteriorRepresentative D p r := by
  obtain ⟨m, _, a, t, ht, he⟩ := exists_interior_face p.2.2
  exact ⟨⟨m, D.face a p.2.1, t⟩, ht, a, rfl, he⟩

lemma interior_representative_unique (D : DeltaComplex) (p r s : D.SimplexSum)
    (hr : IsInteriorRepresentative D p r) (hs : IsInteriorRepresentative D p s) : r = s := by
  rcases p with ⟨n, c, t⟩
  rcases r with ⟨m, d, u⟩
  rcases s with ⟨k, e, v⟩
  rcases hr with ⟨hu, a, had, hau⟩
  rcases hs with ⟨hv, b, hbe, hbv⟩
  obtain ⟨hmk, hab, huv⟩ := positive_face_unique a b u v hu hv (hau.trans hbv.symm)
  change m = k at hmk
  subst k
  have hab' : a = b := eq_of_heq hab
  subst b
  have huv' : u = v := eq_of_heq huv
  subst v
  have hde : d = e := had.symm.trans hbe
  subst e
  rfl

lemma interior_self_representative (D : DeltaComplex) (p : D.SimplexSum)
    (hp : p.2.2 ∈ standardSimplexInterior p.1) : IsInteriorRepresentative D p p := by
  refine ⟨hp, OrderEmbedding.id _, D.face_id _ _, ?_⟩
  exact Convexity.StdSimplex.map_id _

lemma representative_push_face (D : DeltaComplex) {m n}
    (b : Fin (m + 1) ↪o Fin (n + 1)) (c : D.Simplex n) (t : StandardSimplex m)
    (r : D.SimplexSum)
    (hr : IsInteriorRepresentative D ⟨m, D.face b c, t⟩ r) :
    IsInteriorRepresentative D ⟨n, c, orderedAffineFace b t⟩ r := by
  rcases hr with ⟨hu, a, had, hau⟩
  refine ⟨hu, a.comp b, (D.face_comp a b c).symm.trans had, ?_⟩
  change r.2.2.map (fun x => b (a x)) = t.map b
  rw [← Convexity.StdSimplex.map_map]
  exact congrArg (Convexity.StdSimplex.map b) hau

def normalForm (D : DeltaComplex) (p : D.SimplexSum) : D.SimplexSum :=
  Classical.choose (exists_interior_representative D p)

lemma normalForm_representative (D : DeltaComplex) (p : D.SimplexSum) :
    IsInteriorRepresentative D p (normalForm D p) :=
  Classical.choose_spec (exists_interior_representative D p)

lemma normalForm_face (D : DeltaComplex) {p q : D.SimplexSum}
    (h : D.FaceRelation p q) : normalForm D p = normalForm D q := by
  cases h with
  | face b c t =>
    exact interior_representative_unique D _ _ _
      (representative_push_face D b c t _ (normalForm_representative D _))
      (normalForm_representative D _)

lemma normalForm_eqv (D : DeltaComplex) {p q : D.SimplexSum}
    (h : Relation.EqvGen D.FaceRelation p q) : normalForm D p = normalForm D q := by
  induction h with
  | rel p q h => exact normalForm_face D h
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma normalForm_of_interior (D : DeltaComplex) (p : D.SimplexSum)
    (hp : p.2.2 ∈ standardSimplexInterior p.1) : normalForm D p = p :=
  interior_representative_unique D p _ p (normalForm_representative D p)
    (interior_self_representative D p hp)

theorem interior_quotient_unique (D : DeltaComplex)
    {n m : ℕ} {c : D.Simplex n} {d : D.Simplex m}
    {t : StandardSimplex n} {u : StandardSimplex m}
    (ht : t ∈ standardSimplexInterior n) (hu : u ∈ standardSimplexInterior m)
    (he : D.simplexChart n c t = D.simplexChart m d u) :
    (⟨n, c, t⟩ : D.SimplexSum) = ⟨m, d, u⟩ := by
  have h := normalForm_eqv D (Quotient.exact he)
  rw [normalForm_of_interior D _ ht, normalForm_of_interior D _ hu] at h
  exact h

end P202.Topology.DeltaSupport

namespace P202.Topology
open DeltaSupport

theorem deltaInteriorCover (D : DeltaComplex) (x : D.Realization) :
    ∃ (n : ℕ) (c : D.Simplex n) (t : StandardSimplex n),
      t ∈ standardSimplexInterior n ∧ D.simplexChart n c t = x := by
  obtain ⟨⟨n, c, t⟩, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨m, _, a, u, hu, htu⟩ := exists_interior_face t
  refine ⟨m, D.face a c, u, hu, ?_⟩
  exact (Quotient.sound (Relation.EqvGen.rel _ _
    (DeltaComplex.FaceRelation.face a c u))).trans (congrArg (D.simplexChart n c) htu)

/-- Each closed chart is covered by the interiors of finitely many labelled
faces. Repeated face labels are harmless and no global finiteness is assumed. -/
theorem deltaFiniteInteriorCover (D : DeltaComplex) (n : ℕ) (c : D.Simplex n) :
    ∃ F : Finset (Σ m, D.Simplex m),
      Set.range (D.simplexChart n c) ⊆
        ⋃ d ∈ F, D.simplexChart d.1 d.2 '' standardSimplexInterior d.1 := by
  classical
  let A := Σ m : Fin (n + 1), (Fin (m.1 + 1) ↪o Fin (n + 1))
  letI : Fintype A := Fintype.ofFinite A
  let label : A → Σ m, D.Simplex m := fun p => ⟨p.1.1, D.face p.2 c⟩
  refine ⟨Finset.univ.image label, ?_⟩
  rintro x ⟨t, rfl⟩
  obtain ⟨m, hm, a, u, hu, htu⟩ := exists_interior_face t
  let p : A := ⟨⟨m, Nat.lt_succ_of_le hm⟩, a⟩
  refine mem_iUnion.mpr ⟨label p, mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  · refine ⟨u, hu, ?_⟩
    exact (Quotient.sound (Relation.EqvGen.rel _ _
      (DeltaComplex.FaceRelation.face a c u))).trans (congrArg (D.simplexChart n c) htu)

end P202.Topology

namespace P202.Topology
open DeltaSupport

lemma orderedFace_self_positive {n : ℕ} (a : Fin (n + 1) ↪o Fin (n + 1))
    (t : StandardSimplex n) (ht : t ∈ standardSimplexInterior n) :
    orderedAffineFace a t ∈ standardSimplexInterior n := by
  intro v
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective a.injective v
  change 0 < t.weights.mapDomain a (a i)
  rw [Finsupp.mapDomain_apply_of_injective a.injective]
  exact ht i

lemma exists_proper_interior_face {n : ℕ} (t : StandardSimplex n)
    (ht : t ∉ standardSimplexInterior n) :
    ∃ (m : ℕ) (_ : m < n) (a : Fin (m + 1) ↪o Fin (n + 1))
      (u : StandardSimplex m),
      u ∈ standardSimplexInterior m ∧ orderedAffineFace a u = t := by
  obtain ⟨m, hm, a, u, hu, htu⟩ := exists_interior_face t
  have hmn : m < n := by
    apply lt_of_le_of_ne hm
    intro heq
    subst m
    exact ht (htu ▸ orderedFace_self_positive a u hu)
  exact ⟨m, hmn, a, u, hu, htu⟩

lemma deltaBoundaryInteriorCover (D : DeltaComplex.{u}) (n : ℕ) (c : D.Simplex n)
    (t : StandardSimplex n) (ht : t ∉ standardSimplexInterior n) :
    ∃ (m : ℕ) (_ : m < n) (d : D.Simplex m) (u : StandardSimplex m),
      u ∈ standardSimplexInterior m ∧ D.simplexChart m d u = D.simplexChart n c t := by
  obtain ⟨m, hm, a, u, hu, htu⟩ := exists_proper_interior_face t ht
  exact ⟨m, hm, D.face a c, u, hu,
    (deltaFaceCompatibility D a c u).trans (congrArg (D.simplexChart n c) htu)⟩

lemma deltaChart_interior_saturated (D : DeltaComplex.{u}) (n : ℕ) (c : D.Simplex n) :
    D.simplexChart n c ⁻¹' (D.simplexChart n c '' standardSimplexInterior n) =
      standardSimplexInterior n := by
  apply Set.Subset.antisymm
  · rintro t ⟨v, hv, htv⟩
    obtain ⟨m, hm, a, u, hu, htu⟩ := exists_interior_face t
    have he : D.simplexChart m (D.face a c) u = D.simplexChart n c v :=
      (deltaFaceCompatibility D a c u).trans ((congrArg (D.simplexChart n c) htu).trans htv.symm)
    have hmn : m = n := congrArg Sigma.fst (interior_quotient_unique D hu hv he)
    subst m
    exact htu ▸ orderedFace_self_positive a u hu
  · exact Set.subset_preimage_image _ _

lemma deltaChart_interior_injective (D : DeltaComplex.{u}) (n : ℕ) (c : D.Simplex n) :
    Set.InjOn (D.simplexChart n c) (standardSimplexInterior n) := by
  intro t ht v hv he
  have h := interior_quotient_unique D ht hv he
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

lemma deltaInteriorEmbedding (D : DeltaComplex.{u}) [T2Space D.Realization]
    (n : ℕ) (c : D.Simplex n) :
    IsEmbedding ((standardSimplexInterior n).domRestrict (D.simplexChart n c)) := by
  apply isEmbedding_restrict_of_isClosedMap _ (deltaChartContinuous D n c)
    (deltaChartContinuous D n c).isClosedMap _
    (deltaChart_interior_saturated D n c) (deltaChart_interior_injective D n c)

end P202.Topology

namespace P202.Topology.DeltaSupport

theorem compatible_face_values (D : DeltaComplex) (N : ℕ)
    {Y : Type*} (f : ∀ m : ℕ, m < N → D.Simplex m → StandardSimplex m → Y)
    (hf : ∀ {k m} (hkm : k ≤ m) (hmN : m < N)
      (a : Fin (k + 1) ↪o Fin (m + 1)) (c : D.Simplex m) (t : StandardSimplex k),
      f k (lt_of_le_of_lt hkm hmN) (D.face a c) t =
        f m hmN c (orderedAffineFace a t))
    {n k m : ℕ} (hk : k < N) (hm : m < N)
    (a : Fin (k + 1) ↪o Fin (n + 1)) (b : Fin (m + 1) ↪o Fin (n + 1))
    (c : D.Simplex n) (t : StandardSimplex k) (u : StandardSimplex m)
    (he : orderedAffineFace a t = orderedAffineFace b u) :
    f k hk (D.face a c) t = f m hm (D.face b c) u := by
  obtain ⟨r, hrk, i, v, hv, hiv⟩ := exists_interior_face t
  obtain ⟨s, hsm, j, w, hw, hjw⟩ := exists_interior_face u
  have hcomp (p q l : ℕ) (i : Fin (p + 1) ↪o Fin (q + 1))
      (a : Fin (q + 1) ↪o Fin (l + 1)) (v : StandardSimplex p) :
      orderedAffineFace (i.comp a) v = orderedAffineFace a (orderedAffineFace i v) := by
    exact (Convexity.StdSimplex.map_map v i a).symm
  have he' : orderedAffineFace (i.comp a) v = orderedAffineFace (j.comp b) w := by
    rw [hcomp, hcomp, hiv, hjw]
    exact he
  obtain ⟨hrs, hij, hvw⟩ := positive_face_unique (i.comp a) (j.comp b) v w hv hw he'
  have h₁ := hf hrk hk i (D.face a c) v
  rw [hiv, D.face_comp] at h₁
  have h₂ := hf hsm hm j (D.face b c) w
  rw [hjw, D.face_comp] at h₂
  subst s
  have hij' : i.comp a = j.comp b := eq_of_heq hij
  have hvw' : v = w := eq_of_heq hvw
  subst w
  rw [← h₁, ← h₂, hij']

end P202.Topology.DeltaSupport

namespace P202.Topology.DeltaBoundary
open DeltaSupport

abbrev Boundary (n : ℕ) := (standardSimplexInterior n)ᶜ

abbrev ProperFaceSum (n : ℕ) :=
  Σ m : Fin n, Σ _ : (Fin (m.1 + 1) ↪o Fin (n + 1)), StandardSimplex m.1

lemma isOpen_interior (n : ℕ) : IsOpen (standardSimplexInterior n) := by
  simp only [standardSimplexInterior, ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (Convexity.StdSimplex.continuous_weights_apply ℝ i)

lemma isClosed_boundary (n : ℕ) : IsClosed (Boundary n) := (isOpen_interior n).isClosed_compl

lemma properFace_mem_boundary {m n : ℕ} (hmn : m < n)
    (a : Fin (m + 1) ↪o Fin (n + 1)) (t : StandardSimplex m) :
    orderedAffineFace a t ∈ Boundary n := by
  intro hpos
  have hsurj : Function.Surjective a := by
    intro i
    by_contra hi
    have hzero : (orderedAffineFace a t).weights i = 0 :=
      Finsupp.mapDomain_of_notMem_range t.weights i hi
    exact (hpos i).ne' hzero
  have hc := Fintype.card_le_of_surjective a hsurj
  simp only [Fintype.card_fin] at hc
  omega

def faceProjection (n : ℕ) : ProperFaceSum n → Boundary n :=
  fun p => ⟨orderedAffineFace p.2.1 p.2.2,
    properFace_mem_boundary p.1.2 p.2.1 p.2.2⟩

lemma continuous_faceProjection (n : ℕ) : Continuous (faceProjection n) := by
  apply continuous_sigma
  intro m
  apply continuous_sigma
  intro a
  exact (Convexity.StdSimplex.continuous_map ℝ a).subtype_mk _

lemma faceProjection_surjective (n : ℕ) : Function.Surjective (faceProjection n) := by
  rintro ⟨t, ht⟩
  obtain ⟨m, hmn, a, u, hu, htu⟩ := exists_interior_face t
  have hlt : m < n := by
    apply lt_of_le_of_ne hmn
    intro h
    subst m
    have hsurj : Function.Surjective a := Finite.surjective_of_injective a.injective
    apply ht
    intro v
    obtain ⟨w, rfl⟩ := hsurj v
    rw [← htu]
    change 0 < (u.weights.mapDomain a) (a w)
    rw [Finsupp.mapDomain_apply_of_injective a.injective]
    exact hu w
  refine ⟨⟨⟨m, hlt⟩, a, u⟩, ?_⟩
  exact Subtype.ext htu

lemma quotient_faceProjection (n : ℕ) : IsQuotientMap (faceProjection n) := by
  haveI : T2Space (StandardSimplex n) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).t2Space
  exact (continuous_faceProjection n).isClosedMap.isQuotientMap
    (continuous_faceProjection n) (faceProjection_surjective n)

theorem exists_boundary_extension (n : ℕ) (f : C(ProperFaceSum n, ℝ))
    (hf : ∀ p q, faceProjection n p = faceProjection n q → f p = f q) :
    ∃ F : C(StandardSimplex n, ℝ), ∀ p : ProperFaceSum n,
      F (orderedAffineFace p.2.1 p.2.2) = f p := by
  classical
  let q := faceProjection n
  have hq : Function.Surjective q := faceProjection_surjective n
  let g : Boundary n → ℝ := fun y => f (Classical.choose (hq y))
  have hg (p : ProperFaceSum n) : g (q p) = f p := by
    apply hf
    exact Classical.choose_spec (hq (q p))
  have hgcont : Continuous g := by
    apply (quotient_faceProjection n).continuous_iff.mpr
    have heq : g ∘ q = f := funext hg
    rw [show faceProjection n = q from rfl, heq]
    exact f.continuous
  haveI : NormalSpace (StandardSimplex n) :=
    (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ (Fin (n+1))).normalSpace
  obtain ⟨F, hF⟩ := (ContinuousMap.mk g hgcont).exists_restrict_eq (isClosed_boundary n)
  refine ⟨F, fun p => ?_⟩
  have hp := congrArg (fun G : C(Boundary n, ℝ) => G (q p)) hF
  exact hp.trans (hg p)

end P202.Topology.DeltaBoundary

namespace P202.Topology.DeltaBoundary

theorem exists_compatible_extension (D : DeltaComplex) (N : ℕ)
    (f : ∀ m : ℕ, m < N → D.Simplex m → C(StandardSimplex m, ℝ))
    (hf : ∀ {k m} (hkm : k ≤ m) (hmN : m < N)
      (a : Fin (k + 1) ↪o Fin (m + 1)) (c : D.Simplex m) (t : StandardSimplex k),
      f k (lt_of_le_of_lt hkm hmN) (D.face a c) t =
        f m hmN c (orderedAffineFace a t)) :
    ∃ g : ∀ c : D.Simplex N, C(StandardSimplex N, ℝ),
      ∀ (m : ℕ) (hm : m < N) (a : Fin (m + 1) ↪o Fin (N + 1))
        (c : D.Simplex N) (t : StandardSimplex m),
        f m hm (D.face a c) t = g c (orderedAffineFace a t) := by
  classical
  let F (c : D.Simplex N) : C(ProperFaceSum N, ℝ) :=
    ⟨fun p => f p.1.1 p.1.2 (D.face p.2.1 c) p.2.2, by
      apply continuous_sigma
      intro m
      apply continuous_sigma
      intro a
      exact (f m.1 m.2 (D.face a c)).continuous⟩
  have hext (c : D.Simplex N) : ∃ G : C(StandardSimplex N, ℝ),
      ∀ p : ProperFaceSum N, G (orderedAffineFace p.2.1 p.2.2) = F c p := by
    apply exists_boundary_extension N (F c)
    intro p q hpq
    exact DeltaSupport.compatible_face_values D N
      (fun m hm c => (f m hm c : StandardSimplex m → ℝ)) hf p.1.2 q.1.2
      p.2.1 q.2.1 c p.2.2 q.2.2 (congrArg Subtype.val hpq)
  choose g hg using hext
  refine ⟨g, fun m hm a c t => ?_⟩
  exact (hg c ⟨⟨m, hm⟩, a, t⟩).symm

end P202.Topology.DeltaBoundary

namespace P202.DeltaGeometry
open P202.Topology

@[instance_reducible] def deltaCells (D : DeltaComplex.{u})
    (e : ∀ n, Disk n ≃ₜ StandardSimplex n) : CellStructure D.Realization where
  Cell := D.Simplex
  characteristic n c := ⟨D.simplexChart n c ∘ e n,
    (deltaChartContinuous D n c).comp (e n).continuous⟩

theorem deltaCells_openCell (D : DeltaComplex.{u})
    (e : ∀ n, Disk n ≃ₜ StandardSimplex n)
    (hi : ∀ n (x : Disk n), e n x ∈ standardSimplexInterior n ↔ ‖x.1‖ < 1)
    (n : ℕ) (c : D.Simplex n) :
    letI := deltaCells D e
    openCell D.Realization n c = D.simplexChart n c '' standardSimplexInterior n := by
  letI := deltaCells D e
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e n (interiorInclusion n x), (hi n _).mpr (by
      change ‖x.1‖ < 1
      simpa only [Metric.mem_ball, dist_zero_right] using x.2), rfl⟩
  · rintro ⟨t, ht, rfl⟩
    have hx : ‖((e n).symm t).1‖ < 1 := (hi n _).mp (by simpa)
    refine ⟨⟨((e n).symm t).1, by simpa only [Metric.mem_ball, dist_zero_right] using hx⟩, ?_⟩
    change D.simplexChart n c (e n ((e n).symm t)) = _
    simp

set_option maxHeartbeats 600000 in
theorem deltaRealizationCW_of_embedding_boundary
    (D : DeltaComplex.{u}) [T2Space D.Realization]
    (hemb : ∀ n (c : D.Simplex n), IsEmbedding
      ((standardSimplexInterior n).domRestrict (D.simplexChart n c)))
    (hbd : ∀ n (c : D.Simplex n) (t : StandardSimplex n),
      t ∉ standardSimplexInterior n →
      ∃ m < n, ∃ (d : D.Simplex m) (u : StandardSimplex m),
        u ∈ standardSimplexInterior m ∧ D.simplexChart m d u = D.simplexChart n c t) :
    ∃ (C : CWStructure D.Realization)
      (indices : ∀ n, C.toCellStructure.Cell n ≃ D.Simplex n),
      letI : CWStructure D.Realization := C
      ∀ n (c : Cell D.Realization n),
        openCell D.Realization n c =
          D.simplexChart n (indices n c) '' standardSimplexInterior n ∧
        ∃ e : Disk n ≃ₜ StandardSimplex n,
          (characteristic D.Realization n c : Disk n → D.Realization) =
            D.simplexChart n (indices n c) ∘ e := by
  classical
  choose e he using diskSimplexParametrization
  letI := deltaCells D e
  have hopen := deltaCells_openCell D e he
  have hopen' (n : ℕ) (c : Cell D.Realization n) (p : D.Realization) :
      p ∈ openCell D.Realization n c ↔
        p ∈ D.simplexChart n c '' standardSimplexInterior n := by rw [hopen]
  have hem (n : ℕ) (c : Cell D.Realization n) :
      IsEmbedding (interiorMap D.Realization n c) := by
    let k : OpenDisk n → standardSimplexInterior n := fun x =>
      ⟨e n (interiorInclusion n x), (he n _).mpr (by
        change ‖x.1‖ < 1
        simpa only [Metric.mem_ball, dist_zero_right] using x.2)⟩
    have hk : IsEmbedding k := ((e n).isEmbedding.comp
      (.inclusion (Metric.ball_subset_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)))).codRestrict _ _
    exact (hemb n c).comp hk
  have hdis : (univ : Set (Σ n, Cell D.Realization n)).PairwiseDisjoint
      (fun c => openCell D.Realization c.1 c.2) := by
    intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro p hpa hpb
    obtain ⟨t, ht, htp⟩ := (hopen' a.1 a.2 p).mp hpa
    obtain ⟨u, hu, hup⟩ := (hopen' b.1 b.2 p).mp hpb
    have heq := DeltaSupport.interior_quotient_unique D ht hu (htp.trans hup.symm)
    exact hab (congrArg (fun q : D.SimplexSum => (⟨q.1, q.2.1⟩ : Σ n, D.Simplex n)) heq)
  have hcover : ⋃ (n : ℕ) (c : Cell D.Realization n), openCell D.Realization n c = univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨n, c, t, ht, htp⟩ := deltaInteriorCover D p
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨c, (hopen' _ _ _).mpr ⟨t, ht, htp⟩⟩⟩
  have hboundary (n : ℕ) (c : Cell D.Realization n) :
      MapsTo (boundaryMap D.Realization n c) univ (skeletonLT D.Realization n) := by
    intro x _
    have hnot : e n (boundaryInclusion n x) ∉ standardSimplexInterior n := by
      intro ht
      have hnorm : ‖x.1‖ < 1 := (he n (boundaryInclusion n x)).mp ht
      have heqnorm : ‖x.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.2
      exact (ne_of_lt hnorm) heqnorm
    obtain ⟨m, hmn, d, t, ht, htp⟩ := hbd n c _ hnot
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn,
      mem_iUnion.mpr ⟨d, (hopen' _ _ _).mpr ⟨t, ht, htp⟩⟩⟩⟩
  have hfinite (n : ℕ) (c : Cell D.Realization n) :
      ∃ F : Finset (Σ m, Cell D.Realization m),
        closedCell D.Realization n c ⊆ ⋃ d ∈ F, openCell D.Realization d.1 d.2 := by
    obtain ⟨F, hF⟩ := deltaFiniteInteriorCover D n c
    refine ⟨F, ?_⟩
    rintro p ⟨x, rfl⟩
    obtain ⟨d, hd, hp⟩ := mem_iUnion.mp (hF ⟨e n x, rfl⟩) |>.imp fun d h => mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨hd, (hopen' _ _ _).mpr hp⟩⟩
  have hweak (A : Set D.Realization) : IsClosed A ↔
      ∀ n (c : Cell D.Realization n), IsClosed (characteristic D.Realization n c ⁻¹' A) := by
    have hk : IsClosed A ↔ ∀ n (c : D.Simplex n), IsClosed (D.simplexChart n c ⁻¹' A) := by
      simpa only [← isOpen_compl_iff, ← preimage_compl] using deltaWeakTopology D Aᶜ
    constructor
    · intro h n c
      exact h.preimage (characteristic D.Realization n c).continuous
    · intro h
      apply hk.mpr
      intro n c
      exact (e n).isQuotientMap.isCoinducing.isClosed_preimage.mp (h n c)
  let C := cwStructureOfWeak hem hdis hcover hboundary hfinite hweak
  refine ⟨C, fun n => Equiv.refl _, ?_⟩
  intro n c
  exact ⟨hopen n c, e n, rfl⟩

end P202.DeltaGeometry

namespace P202.Topology

theorem deltaRealizationCW_of_hausdorff
    (ht2 : ∀ D : DeltaComplex.{u}, T2Space D.Realization) :
    P202Specs.Topology.CellStructures.deltaRealizationCW.{u} := by
  intro D
  letI := ht2 D
  apply DeltaGeometry.deltaRealizationCW_of_embedding_boundary D (deltaInteriorEmbedding D)
  intro n c t ht
  obtain ⟨m, hm, d, u, hu, heq⟩ := deltaBoundaryInteriorCover D n c t ht
  exact ⟨m, hm, d, u, hu, heq⟩

end P202.Topology

namespace P202.Topology

/-- Every quotient point belongs to exactly one labelled simplex interior. -/
theorem deltaInteriorPartition : P202Specs.Topology.CellStructures.deltaInteriorPartition.{u} := by
  intro D x
  obtain ⟨n, c, t, ht, he⟩ := deltaInteriorCover D x
  refine ⟨⟨n, c, t⟩, ⟨ht, he⟩, ?_⟩
  rintro ⟨m, d, v⟩ ⟨hv, hvx⟩
  exact DeltaSupport.interior_quotient_unique D hv ht (hvx.trans he.symm)

end P202.Topology

namespace P202.Topology.DeltaBoundary

lemma exists_simplex_bump (n : ℕ) (t : StandardSimplex n)
    (ht : t ∈ standardSimplexInterior n) (S : Set (StandardSimplex n))
    (hS : IsClosed S) (htS : t ∉ S) :
    ∃ F : C(StandardSimplex n, ℝ), F t = 1 ∧
      (∀ x ∈ Boundary n, F x = 0) ∧ (∀ x ∈ S, F x = 0) := by
  haveI : T2Space (StandardSimplex n) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).t2Space
  haveI : NormalSpace (StandardSimplex n) :=
    (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ (Fin (n+1))).normalSpace
  have hd : Disjoint (Boundary n ∪ S) {t} := by
    apply Set.disjoint_left.mpr
    intro x hx he
    have hxt : x = t := Set.mem_singleton_iff.mp he
    subst x
    rcases hx with hb | hS'
    · exact hb ht
    · exact htS hS'
  obtain ⟨F, hzero, hone, _⟩ := exists_continuous_zero_one_of_isClosed
    ((isClosed_boundary n).union hS) isClosed_singleton hd
  exact ⟨F, hone (Set.mem_singleton t),
    fun x hx => hzero (Or.inl hx), fun x hx => hzero (Or.inr hx)⟩

end P202.Topology.DeltaBoundary

namespace P202.Topology

lemma deltaScalarDescent (D : DeltaComplex.{u})
    (f : ∀ n, D.Simplex n → C(StandardSimplex n, ℝ))
    (hf : ∀ {m n} (a : Fin (m + 1) ↪o Fin (n + 1))
      (c : D.Simplex n) (t : StandardSimplex m),
      f m (D.face a c) t = f n c (orderedAffineFace a t)) :
    ∃ F : C(D.Realization, ℝ), ∀ n (c : D.Simplex n) (t : StandardSimplex n),
      F (D.simplexChart n c t) = f n c t := by
  let raw : D.SimplexSum → ℝ := fun p => f p.1 p.2.1 p.2.2
  have hraw : Continuous raw :=
    continuous_sigma fun n => continuous_sigma fun c => (f n c).continuous
  have hrel {p q : D.SimplexSum} (h : D.FaceRelation p q) : raw p = raw q := by
    cases h with
    | face a c t => exact hf a c t
  have heqv {p q : D.SimplexSum} (h : Relation.EqvGen D.FaceRelation p q) :
      raw p = raw q := by
    induction h with
    | rel p q h => exact hrel h
    | refl p => rfl
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨g, ⟨hg, hgeq⟩, _⟩ := D10Topology.Ch03.quotient_descent
    (Quotient.mk D.faceSetoid) ((quotientAdapter _).mpr (deltaProjectionQuotient D))
    raw hraw (fun p q hpq => heqv (Quotient.exact hpq))
  exact ⟨⟨g, hg⟩, fun n c t => congrFun hgeq ⟨n, c, t⟩⟩

lemma t2Space_of_continuous_scalar_separation {X : Type u} [TopologicalSpace X]
    (hsep : ∀ x y : X, x ≠ y → ∃ f : C(X, ℝ), f x ≠ f y) : T2Space X := by
  apply T2Space.of_injective_continuous
    (f := fun x : X => fun g : C(X, ℝ) => g x) ?_ ?_
  · intro x y hxy
    by_contra hne
    obtain ⟨f, hf⟩ := hsep x y hne
    exact hf (congrFun hxy f)
  · exact continuous_pi fun g => g.continuous

end P202.Topology

namespace P202.Topology.DeltaFamilies

abbrev MapsBelow (D : DeltaComplex) (N : ℕ) :=
  ∀ m : ℕ, m < N → D.Simplex m → C(StandardSimplex m, ℝ)

def Compatible (D : DeltaComplex) (N : ℕ) (f : MapsBelow D N) : Prop :=
  ∀ {k m} (hkm : k ≤ m) (hmN : m < N)
    (a : Fin (k + 1) ↪o Fin (m + 1)) (c : D.Simplex m) (t : StandardSimplex k),
    f k (lt_of_le_of_lt hkm hmN) (D.face a c) t =
      f m hmN c (orderedAffineFace a t)

structure Family (D : DeltaComplex) (N : ℕ) where
  maps : MapsBelow D N
  compatible : Compatible D N maps

def ExtensionStep (D : DeltaComplex) : Prop :=
  ∀ N (f : MapsBelow D N), Compatible D N f →
    ∃ g : ∀ c : D.Simplex N, C(StandardSimplex N, ℝ),
      ∀ m (hm : m < N) (a : Fin (m + 1) ↪o Fin (N + 1))
        (c : D.Simplex N) (t : StandardSimplex m),
        f m hm (D.face a c) t = g c (orderedAffineFace a t)

lemma self_embedding_eq_id {n : ℕ} (a : Fin (n + 1) ↪o Fin (n + 1)) :
    a = OrderEmbedding.id _ := by
  have ha := Finset.orderEmbOfFin_unique' (s := Finset.univ)
    (by simp : (Finset.univ : Finset (Fin (n + 1))).card = n + 1)
    (f := a) (fun _ => Finset.mem_univ _)
  have hi := Finset.orderEmbOfFin_unique' (s := Finset.univ)
    (by simp : (Finset.univ : Finset (Fin (n + 1))).card = n + 1)
    (f := OrderEmbedding.id _) (fun _ => Finset.mem_univ _)
  exact ha.trans hi.symm

lemma exists_successor (D : DeltaComplex) (hstep : ExtensionStep D)
    {N : ℕ} (f : Family D N) :
    ∃ g : Family D (N + 1), ∀ m (hm : m < N) c,
      g.maps m (Nat.lt_succ_of_lt hm) c = f.maps m hm c := by
  obtain ⟨g, hg⟩ := hstep N f.maps f.compatible
  let F : MapsBelow D (N + 1) := fun m hm c =>
    if h : m < N then f.maps m h c
    else by
      have he : m = N := by omega
      subst m
      exact g c
  have Fold (m : ℕ) (hm : m < N) (hm' : m < N + 1) (c : D.Simplex m) :
      F m hm' c = f.maps m hm c := by simp only [F, dif_pos hm]
  have Fnew (hm : N < N + 1) (c : D.Simplex N) : F N hm c = g c := by
    simp only [F, lt_self_iff_false, ↓reduceDIte]
  refine ⟨⟨F, ?_⟩, ?_⟩
  · intro k m hkm hm a c t
    by_cases hmN : m < N
    · rw [Fold k (lt_of_le_of_lt hkm hmN), Fold m hmN]
      exact f.compatible hkm hmN a c t
    · have hmN' : m = N := by omega
      subst m
      by_cases hkN : k < N
      · rw [Fold k hkN, Fnew hm c]
        exact hg k hkN a c t
      · have hkN' : k = N := by omega
        subst k
        rw [Fnew hm _, Fnew hm _, self_embedding_eq_id a, D.face_id]
        exact congrArg (g c) (Convexity.StdSimplex.map_id t).symm
  · intro m hm c
    exact Fold m hm _ c

def successor (D : DeltaComplex) (hstep : ExtensionStep D) {N : ℕ}
    (f : Family D N) : Family D (N + 1) :=
  Classical.choose (exists_successor D hstep f)

lemma successor_old (D : DeltaComplex) (hstep : ExtensionStep D)
    {N : ℕ} (f : Family D N) (m : ℕ) (hm : m < N) (c : D.Simplex m) :
    (successor D hstep f).maps m (Nat.lt_succ_of_lt hm) c = f.maps m hm c :=
  Classical.choose_spec (exists_successor D hstep f) m hm c

def stages (D : DeltaComplex) (hstep : ExtensionStep D) {N : ℕ}
    (f : Family D N) : ∀ r : ℕ, Family D (N + r)
  | 0 => f
  | r + 1 => successor D hstep (stages D hstep f r)

lemma stages_mono (D : DeltaComplex) (hstep : ExtensionStep D) {N : ℕ}
    (f : Family D N) {r s : ℕ} (hrs : r ≤ s) (m : ℕ) (hm : m < N + r)
    (c : D.Simplex m) :
    (stages D hstep f s).maps m (lt_of_lt_of_le hm (Nat.add_le_add_left hrs N)) c =
      (stages D hstep f r).maps m hm c := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    rw [show stages D hstep f (s + 1) = successor D hstep (stages D hstep f s) from rfl]
    rw [successor_old D hstep (stages D hstep f s) m
      (lt_of_lt_of_le hm (Nat.add_le_add_left hrs N)) c]
    exact ih

def globalMaps (D : DeltaComplex) (hstep : ExtensionStep D) {N : ℕ}
    (f : Family D N) (m : ℕ) (c : D.Simplex m) : C(StandardSimplex m, ℝ) :=
  (stages D hstep f (m + 1)).maps m (by omega) c

lemma globalMaps_agree (D : DeltaComplex) (hstep : ExtensionStep D) {N : ℕ}
    (f : Family D N) (r m : ℕ) (hm : m < N + r) (c : D.Simplex m) :
    globalMaps D hstep f m c = (stages D hstep f r).maps m hm c := by
  let s := max r (m + 1)
  have h₁ := stages_mono D hstep f (le_max_right r (m + 1)) m
    (show m < N + (m + 1) by omega) c
  have h₂ := stages_mono D hstep f (le_max_left r (m + 1)) m hm c
  exact h₁.symm.trans h₂

lemma embedding_dimension_le {m n : ℕ} (a : Fin (m + 1) ↪o Fin (n + 1)) : m ≤ n := by
  have h := Fintype.card_le_of_injective a a.injective
  simpa only [Fintype.card_fin, Nat.succ_le_succ_iff] using h

theorem globalMaps_compatible (D : DeltaComplex) (hstep : ExtensionStep D) {N : ℕ}
    (f : Family D N) {m n : ℕ} (a : Fin (m + 1) ↪o Fin (n + 1))
    (c : D.Simplex n) (t : StandardSimplex m) :
    globalMaps D hstep f m (D.face a c) t =
      globalMaps D hstep f n c (orderedAffineFace a t) := by
  have hmn := embedding_dimension_le a
  have hn : n < N + (n + 1) := by omega
  rw [globalMaps_agree D hstep f (n + 1) m (lt_of_le_of_lt hmn hn),
    globalMaps_agree D hstep f (n + 1) n hn]
  exact (stages D hstep f (n + 1)).compatible hmn hn a c t

theorem exists_global_extension (D : DeltaComplex) (hstep : ExtensionStep D)
    (N : ℕ) (f : MapsBelow D N) (hf : Compatible D N f) :
    ∃ F : ∀ m, D.Simplex m → C(StandardSimplex m, ℝ),
      (∀ {m n} (a : Fin (m + 1) ↪o Fin (n + 1)) (c : D.Simplex n)
        (t : StandardSimplex m), F m (D.face a c) t = F n c (orderedAffineFace a t)) ∧
      ∀ m (hm : m < N) c, F m c = f m hm c := by
  let f' : Family D N := ⟨f, hf⟩
  refine ⟨globalMaps D hstep f', fun a c t => globalMaps_compatible D hstep f' a c t, ?_⟩
  intro m hm c
  exact globalMaps_agree D hstep f' 0 m hm c

end P202.Topology.DeltaFamilies

namespace P202.Topology.DeltaInitial
open Classical

def topFamily (D : DeltaComplex.{u}) (N : ℕ) (c : D.Simplex N)
    (g : C(StandardSimplex N, ℝ)) :
    ∀ k : ℕ, k < N + 1 → D.Simplex k → C(StandardSimplex k, ℝ) :=
  fun k _ => if h : k = N then by
    subst k
    exact fun d => if d = c then g else 0
  else fun _ => 0

lemma topFamily_top (D : DeltaComplex.{u}) (N : ℕ) (c : D.Simplex N)
    (g : C(StandardSimplex N, ℝ)) (d : D.Simplex N) (h : N < N + 1) :
    topFamily D N c g N h d = if d = c then g else 0 := by
  simp [topFamily]

lemma topFamily_lower (D : DeltaComplex.{u}) (N : ℕ) (c : D.Simplex N)
    (g : C(StandardSimplex N, ℝ)) (k : ℕ) (hk : k < N) (d : D.Simplex k) :
    topFamily D N c g k (Nat.lt_succ_of_lt hk) d = 0 := by
  simp [topFamily, Nat.ne_of_lt hk]

lemma topFamily_compatible (D : DeltaComplex.{u}) (N : ℕ) (c : D.Simplex N)
    (g : C(StandardSimplex N, ℝ))
    (hg : ∀ x ∈ DeltaBoundary.Boundary N, g x = 0) :
    ∀ {k m} (hkm : k ≤ m) (hmN : m < N + 1)
      (a : Fin (k + 1) ↪o Fin (m + 1)) (d : D.Simplex m) (t : StandardSimplex k),
      topFamily D N c g k (lt_of_le_of_lt hkm hmN) (D.face a d) t =
        topFamily D N c g m hmN d (orderedAffineFace a t) := by
  intro k m hkm hmN a d t
  by_cases hm : m = N
  · subst m
    by_cases hk : k = N
    · subst k
      rw [DeltaFamilies.self_embedding_eq_id a, D.face_id]
      exact congrArg (topFamily D N c g N hmN d) (Convexity.StdSimplex.map_id t).symm
    · have hkN : k < N := by omega
      rw [topFamily_lower D N c g k hkN, topFamily_top]
      split_ifs with hd
      · exact (hg _ (DeltaBoundary.properFace_mem_boundary hkN a t)).symm
      · rfl
  · have hmN' : m < N := by omega
    rw [topFamily_lower D N c g k (lt_of_le_of_lt hkm hmN'),
      topFamily_lower D N c g m hmN']
    rfl

set_option maxHeartbeats 600000 in
theorem exists_separating_maps_below (D : DeltaComplex.{u})
    {m n : ℕ} (hmn : m ≤ n) (c : D.Simplex n) (d : D.Simplex m)
    (t : StandardSimplex n) (u : StandardSimplex m)
    (ht : t ∈ standardSimplexInterior n)
    (hneq : (⟨n, c, t⟩ : D.SimplexSum) ≠ ⟨m, d, u⟩) :
    ∃ f : ∀ k : ℕ, k < n + 1 → D.Simplex k → C(StandardSimplex k, ℝ),
      (∀ {k l} (hkl : k ≤ l) (hln : l < n + 1)
        (a : Fin (k + 1) ↪o Fin (l + 1)) (e : D.Simplex l) (s : StandardSimplex k),
        f k (lt_of_le_of_lt hkl hln) (D.face a e) s = f l hln e (orderedAffineFace a s)) ∧
      f n (Nat.lt_succ_self n) c t ≠ f m (lt_of_le_of_lt hmn (Nat.lt_succ_self n)) d u := by
  classical
  letI : T2Space (StandardSimplex n) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).t2Space
  by_cases hm : m = n
  · subst m
    by_cases hdc : d = c
    · subst d
      have htu : t ≠ u := by intro heq; subst u; exact hneq rfl
      obtain ⟨g, hgt, hgb, hgu⟩ := DeltaBoundary.exists_simplex_bump n t ht {u}
        isClosed_singleton (by simpa using htu)
      refine ⟨topFamily D n c g, topFamily_compatible D n c g hgb, ?_⟩
      rw [topFamily_top, ite_eq_left rfl, hgt, hgu u (Set.mem_singleton u)]
      exact one_ne_zero
    · obtain ⟨g, hgt, hgb, _⟩ := DeltaBoundary.exists_simplex_bump n t ht ∅ isClosed_empty (by simp)
      refine ⟨topFamily D n c g, topFamily_compatible D n c g hgb, ?_⟩
      rw [topFamily_top, topFamily_top, ite_eq_left rfl, ite_eq_right hdc, hgt]
      exact one_ne_zero
  · have hlt : m < n := by omega
    obtain ⟨g, hgt, hgb, _⟩ := DeltaBoundary.exists_simplex_bump n t ht ∅ isClosed_empty (by simp)
    refine ⟨topFamily D n c g, topFamily_compatible D n c g hgb, ?_⟩
    rw [topFamily_top, topFamily_lower D n c g m hlt, ite_eq_left rfl, hgt]
    exact one_ne_zero

end P202.Topology.DeltaInitial

namespace P202.Topology

/-- Scalar functions on compatible simplex faces separate distinct positive
representatives after extension through all higher-dimensional simplices. -/
lemma delta_separating_scalar_of_dimension_le (D : DeltaComplex.{u})
    {m n : ℕ} (hmn : m ≤ n) (c : D.Simplex n) (d : D.Simplex m)
    (t : StandardSimplex n) (u : StandardSimplex m)
    (ht : t ∈ standardSimplexInterior n)
    (hneq : (⟨n, c, t⟩ : D.SimplexSum) ≠ ⟨m, d, u⟩) :
    ∃ G : C(D.Realization, ℝ),
      G (D.simplexChart n c t) ≠ G (D.simplexChart m d u) := by
  obtain ⟨f, hf, hsep⟩ := DeltaInitial.exists_separating_maps_below D hmn c d t u ht hneq
  obtain ⟨F, hF, hagree⟩ := DeltaFamilies.exists_global_extension D
    (DeltaBoundary.exists_compatible_extension D) (n + 1) f hf
  obtain ⟨G, hG⟩ := deltaScalarDescent D F hF
  refine ⟨G, ?_⟩
  intro heq
  apply hsep
  calc
    f n (Nat.lt_succ_self n) c t = F n c t :=
      (congrArg (fun f : C(StandardSimplex n, ℝ) => f t) (hagree n (Nat.lt_succ_self n) c)).symm
    _ = G (D.simplexChart n c t) := (hG n c t).symm
    _ = G (D.simplexChart m d u) := heq
    _ = F m d u := hG m d u
    _ = f m (lt_of_le_of_lt hmn (Nat.lt_succ_self n)) d u :=
      congrArg (fun f : C(StandardSimplex m, ℝ) => f u)
        (hagree m (lt_of_le_of_lt hmn (Nat.lt_succ_self n)) d)

/-- The weak ordered-face quotient is Hausdorff without a local-finiteness
hypothesis or a bound on simplex dimensions. -/
theorem deltaHausdorff : P202Specs.Topology.CellStructures.deltaHausdorff.{u} := by
  intro D
  apply t2Space_of_continuous_scalar_separation
  intro x y hxy
  obtain ⟨n, c, t, ht, hx⟩ := deltaInteriorCover D x
  obtain ⟨m, d, u, hu, hy⟩ := deltaInteriorCover D y
  have hneq : (⟨n, c, t⟩ : D.SimplexSum) ≠ ⟨m, d, u⟩ := by
    intro heq
    have heq' := congrArg (Quotient.mk D.faceSetoid) heq
    exact hxy (hx.symm.trans (heq'.trans hy))
  rcases le_total m n with hmn | hnm
  · obtain ⟨G, hG⟩ := delta_separating_scalar_of_dimension_le D hmn c d t u ht hneq
    exact ⟨G, by simpa only [hx, hy] using hG⟩
  · obtain ⟨G, hG⟩ := delta_separating_scalar_of_dimension_le D hnm d c u t hu hneq.symm
    exact ⟨G, by simpa only [hx, hy] using hG.symm⟩

theorem deltaRealizationCW : P202Specs.Topology.CellStructures.deltaRealizationCW.{u} :=
  deltaRealizationCW_of_hausdorff deltaHausdorff

end P202.Topology
