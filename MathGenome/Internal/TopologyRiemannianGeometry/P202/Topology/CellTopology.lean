import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import Mathlib.Topology.DiscreteSubset

noncomputable section
open Set Topology
universe u v

namespace P202.Topology
open P202.Cellular

private theorem cell_disjoint {X : Type u} [TopologicalSpace X] [CWStructure X]
    {d e : Σ n, Cell X n} (h : d ≠ e) :
    Disjoint (openCell X d.1 d.2) (openCell X e.1 e.2) :=
  CWStructure.disjoint_interiors (mem_univ d) (mem_univ e) h

private theorem cell_unique {X : Type u} [TopologicalSpace X] [CWStructure X]
    {d e : Σ n, Cell X n} {x : X}
    (hd : x ∈ openCell X d.1 d.2) (he : x ∈ openCell X e.1 e.2) : d = e := by
  by_contra h
  exact Set.disjoint_left.mp (cell_disjoint h) hd he

private theorem mem_carrier {X : Type u} [TopologicalSpace X] [CWStructure X]
    {A : Subcomplex X} {x : X} :
    x ∈ A.carrier ↔ ∃ (n : ℕ) (c : Cell X n), c ∈ A.cells n ∧ x ∈ openCell X n c := by
  simp [Subcomplex.carrier]

private theorem cell_selected {X : Type u} [TopologicalSpace X] [CWStructure X]
    {A : Subcomplex X} {n : ℕ} {c : Cell X n} {x : X}
    (hx : x ∈ A.carrier) (hc : x ∈ openCell X n c) : c ∈ A.cells n := by
  obtain ⟨m, d, hd, hxd⟩ := mem_carrier.mp hx
  have h : (⟨m, d⟩ : Σ n, Cell X n) = ⟨n, c⟩ := cell_unique hxd hc
  cases h
  exact hd

private theorem closed_cell {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) : IsClosed (closedCell X n c) := by
  exact (isCompact_range (characteristic X n c).continuous).isClosed

/-- Closure finiteness promotes a closed-set test on a selected family of
closed cells to ambient closedness for any subset of their open-cell union. -/
private theorem closed_of_selected_intersections
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) (B : Set X) (hBA : B ⊆ A.carrier)
    (hB : ∀ n (c : Cell X n), c ∈ A.cells n → IsClosed (B ∩ closedCell X n c)) :
    IsClosed B := by
  classical
  apply (CWStructure.weak_topology B).mpr
  intro n c
  obtain ⟨F, hF⟩ := CWStructure.closure_finite n c
  let T : Set X := ⋃ d ∈ F, if d.2 ∈ A.cells d.1 then B ∩ closedCell X d.1 d.2 else ∅
  have hT : IsClosed T := by
    apply isClosed_biUnion_finset
    intro d hd
    split_ifs with h
    · exact hB d.1 d.2 h
    · exact isClosed_empty
  have hEq : B ∩ closedCell X n c = T ∩ closedCell X n c := by
    ext x
    constructor
    · rintro ⟨hxB, hxc⟩
      obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp (hF hxc)
      have hdA := cell_selected (hBA hxB) hxd
      refine ⟨mem_iUnion₂.mpr ⟨d, hd, ?_⟩, hxc⟩
      simp only [ite_eq_left hdA]
      exact ⟨hxB, by
        obtain ⟨y, rfl⟩ := hxd
        exact ⟨interiorInclusion d.1 y, rfl⟩⟩
    · rintro ⟨hxT, hxc⟩
      obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hxT
      split_ifs at hxd with h
      · exact ⟨hxd.1, hxc⟩
      · exact hxd.elim
  have hc : IsClosed (B ∩ closedCell X n c) := by
    rw [hEq]
    exact hT.inter (closed_cell n c)
  have heq : characteristic X n c ⁻¹' B =
      characteristic X n c ⁻¹' (B ∩ closedCell X n c) := by
    ext x
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => ⟨h, ⟨x, rfl⟩⟩, And.left⟩
  rw [heq]
  exact hc.preimage (characteristic X n c).continuous

private theorem subcomplex_closed
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.subcomplexClosed.{u} := by
  intro X _ _ A
  apply closed_of_selected_intersections A A.carrier Subset.rfl
  intro n c hc
  have hsub : closedCell X n c ⊆ A.carrier := by
    rw [← hclosure n c]
    exact A.contains_closures n c hc
  rw [inter_eq_right.mpr hsub]
  exact closed_cell n c

private theorem subcomplex_weak_topology
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u} := by
  intro X _ _ A B hBA
  constructor
  · intro hB n c hc
    have hsub : ∀ x, characteristic X n c x ∈ A.carrier := by
      intro x
      apply A.contains_closures n c hc
      rw [hclosure n c]
      exact ⟨x, rfl⟩
    exact hB.preimage ((characteristic X n c).continuous.subtype_mk hsub)
  · intro hB
    have hclosed : IsClosed B := by
      apply closed_of_selected_intersections A B hBA
      intro n c hc
      have hEq : B ∩ closedCell X n c =
          characteristic X n c '' (characteristic X n c ⁻¹' B) := by
        rw [image_preimage_eq_inter_range]
        rfl
      rw [hEq]
      exact (characteristic X n c).continuous.isClosedMap _ (hB n c hc)
    exact hclosed.preimage continuous_subtype_val


/-- A set with finitely many points in each open cell is closed. -/
private theorem closed_of_cellwise_finite
    {X : Type u} [TopologicalSpace X] [CWStructure X] (S : Set X)
    (hS : ∀ n (c : Cell X n), (S ∩ openCell X n c).Finite) : IsClosed S := by
  apply (CWStructure.weak_topology S).mpr
  intro n c
  obtain ⟨F, hF⟩ := CWStructure.closure_finite n c
  have hfin : (S ∩ closedCell X n c).Finite := by
    apply (F.finite_toSet.biUnion (fun d _ => hS d.1 d.2)).subset
    rintro x ⟨hxS, hxc⟩
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp (hF hxc)
    exact mem_iUnion₂.mpr ⟨d, hd, hxS, hxd⟩
  have heq : characteristic X n c ⁻¹' S =
      characteristic X n c ⁻¹' (S ∩ closedCell X n c) := by
    ext x
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => ⟨h, ⟨x, rfl⟩⟩, And.left⟩
  rw [heq]
  exact hfin.isClosed.preimage (characteristic X n c).continuous

/-- There are finitely many cells meeting a compact set, even when the
complex has unbounded dimension and arbitrarily many cells. -/
private theorem compact_meets_finitely_many_cells
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (K : Set X) (hK : IsCompact K) :
    {d : Σ n, Cell X n | (K ∩ openCell X d.1 d.2).Nonempty}.Finite := by
  classical
  let M := {d : Σ n, Cell X n // (K ∩ openCell X d.1 d.2).Nonempty}
  let f : M → X := fun d => d.2.choose
  have hfK : ∀ d, f d ∈ K := fun d => d.2.choose_spec.1
  have hfcell : ∀ d, f d ∈ openCell X d.1.1 d.1.2 := fun d => d.2.choose_spec.2
  have hfinj : Function.Injective f := by
    intro d e h
    apply Subtype.ext
    exact cell_unique (hfcell d) (h ▸ hfcell e)
  have hsparse : ∀ n (c : Cell X n), (range f ∩ openCell X n c).Subsingleton := by
    intro n c x hx y hy
    obtain ⟨d, rfl⟩ := hx.1
    obtain ⟨e, rfl⟩ := hy.1
    have hd : d.1 = ⟨n, c⟩ := cell_unique (hfcell d) hx.2
    have he : e.1 = ⟨n, c⟩ := cell_unique (hfcell e) hy.2
    exact congrArg f (Subtype.ext (hd.trans he.symm))
  have hclosed : ∀ T ⊆ range f, IsClosed T := by
    intro T hT
    apply closed_of_cellwise_finite
    intro n c
    have hh : (T ∩ openCell X n c).Subsingleton := by
      intro x hx y hy
      exact hsparse n c ⟨hT hx.1, hx.2⟩ ⟨hT hy.1, hy.2⟩
    exact hh.finite
  have hcompact : IsCompact (range f) :=
    hK.of_isClosed_subset (hclosed _ Subset.rfl) (by rintro x ⟨d, rfl⟩; exact hfK d)
  have hdiscrete : IsDiscrete (range f) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T, hclosed T hT, inter_eq_left.mpr hT⟩
  have hrange := hcompact.finite hdiscrete
  have hM : Finite M := (Set.finite_range_iff hfinj).mp hrange
  exact Set.finite_coe_iff.mp hM


private def cellUnion {X : Type u} [TopologicalSpace X] [CWStructure X]
    (S : Set (Σ n, Cell X n)) : Set X := ⋃ d ∈ S, openCell X d.1 d.2

private theorem cellUnion_mono {X : Type u} [TopologicalSpace X] [CWStructure X]
    {S T : Set (Σ n, Cell X n)} (h : S ⊆ T) : cellUnion S ⊆ cellUnion T := by
  exact iUnion₂_mono' fun d hd => ⟨d, h hd, Subset.rfl⟩

private theorem closedCell_subset_cell_union_skeleton
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) :
    closedCell X n c ⊆ openCell X n c ∪ skeletonLT X n := by
  rintro _ ⟨x, rfl⟩
  have hx : ‖x.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
  rcases lt_or_eq_of_le hx with h | h
  · exact Or.inl ⟨⟨x.1, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩, rfl⟩
  · have hs : x.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using h
    have hb : boundaryMap X n c ⟨x.1, hs⟩ ∈ skeletonLT X n :=
      CWStructure.boundary_lands n c (mem_univ _)
    exact Or.inr hb

/-- Induction on dimension closes a single cell under all necessary boundary
cells. The chosen sets can contain extra lower-dimensional cells. -/
private theorem finite_closed_cell_hull
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) :
    ∃ S : Set (Σ m, Cell X m), S.Finite ∧ (⟨n, c⟩ : Σ m, Cell X m) ∈ S ∧
      ∀ d ∈ S, closedCell X d.1 d.2 ⊆ cellUnion S := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨F, hF⟩ := CWStructure.closure_finite n c
    let L := F.filter (fun d => d.1 < n)
    have hrec : ∀ d : ↥L, ∃ S : Set (Σ m, Cell X m),
        S.Finite ∧ d.1 ∈ S ∧ ∀ e ∈ S, closedCell X e.1 e.2 ⊆ cellUnion S := by
      intro d
      exact ih d.1.1 (Finset.mem_filter.mp d.2).2 d.1.2
    choose S hSfin hSin hSclosed using hrec
    let G : Set (Σ m, Cell X m) := insert ⟨n, c⟩ (⋃ d, S d)
    have hSG : ∀ d, S d ⊆ G := by
      intro d e he
      exact mem_insert_of_mem _ (mem_iUnion.mpr ⟨d, he⟩)
    refine ⟨G, (Set.finite_iUnion hSfin).insert _, mem_insert _ _, ?_⟩
    intro e he
    rcases mem_insert_iff.mp he with rfl | he
    · intro x hx
      rcases closedCell_subset_cell_union_skeleton n c hx with hxc | hxs
      · exact mem_iUnion₂.mpr ⟨⟨n, c⟩, mem_insert _ _, hxc⟩
      · simp only [skeletonLT, mem_iUnion] at hxs
        obtain ⟨m, hm, d, hxd⟩ := hxs
        obtain ⟨e, heF, hxe⟩ := mem_iUnion₂.mp (hF hx)
        have hed : e = ⟨m, d⟩ := cell_unique hxe hxd
        have heL : e ∈ L := Finset.mem_filter.mpr ⟨heF, by simpa [hed] using hm⟩
        have heS := hSin ⟨e, heL⟩
        exact mem_iUnion₂.mpr ⟨e, hSG ⟨e, heL⟩ heS, hxe⟩
    · obtain ⟨d, heS⟩ := mem_iUnion.mp he
      exact (hSclosed d e heS).trans (cellUnion_mono (hSG d))


private def subcomplexFromCells
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (S : Set (Σ m, Cell X m))
    (hS : ∀ d ∈ S, closedCell X d.1 d.2 ⊆ cellUnion S) : Subcomplex X where
  cells n := {c | (⟨n, c⟩ : Σ m, Cell X m) ∈ S}
  contains_closures := by
    intro n c hc x hx
    rw [hclosure n c] at hx
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp (hS ⟨n, c⟩ hc hx)
    exact mem_iUnion.mpr ⟨d.1, mem_iUnion.mpr ⟨⟨d.2, hd⟩, hxd⟩⟩

private theorem subcomplexFromCells_carrier
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (S : Set (Σ m, Cell X m))
    (hS : ∀ d ∈ S, closedCell X d.1 d.2 ⊆ cellUnion S) :
    (subcomplexFromCells hclosure S hS).carrier = cellUnion S := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, c, hc, hxc⟩ := mem_carrier.mp hx
    exact mem_iUnion₂.mpr ⟨⟨n, c⟩, hc, hxc⟩
  · intro hx
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
    exact mem_carrier.mpr ⟨d.1, d.2, hd, hxd⟩

/-- Finitely many prescribed cells lie in a finite subcomplex. -/
private theorem finite_cells_contained
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    {X : Type u} [TopologicalSpace X] [CWStructure X]
    (F : Set (Σ m, Cell X m)) (hF : F.Finite) :
    ∃ A : Subcomplex X, A.IsFinite ∧ cellUnion F ⊆ A.carrier := by
  classical
  let : Finite F := hF.to_subtype
  have hh : ∀ d : F, ∃ S : Set (Σ m, Cell X m), S.Finite ∧ d.1 ∈ S ∧
      ∀ e ∈ S, closedCell X e.1 e.2 ⊆ cellUnion S := by
    intro d
    exact finite_closed_cell_hull d.1.1 d.1.2
  choose S hSfinite hSin hSclosed using hh
  let G := ⋃ d, S d
  have hGclosed : ∀ e ∈ G, closedCell X e.1 e.2 ⊆ cellUnion G := by
    intro e he
    obtain ⟨d, heS⟩ := mem_iUnion.mp he
    exact (hSclosed d e heS).trans (cellUnion_mono (subset_iUnion S d))
  let A := subcomplexFromCells hclosure G hGclosed
  refine ⟨A, ?_, ?_⟩
  · exact Set.finite_iUnion hSfinite
  · change cellUnion F ⊆ (subcomplexFromCells hclosure G hGclosed).carrier
    rw [subcomplexFromCells_carrier]
    apply cellUnion_mono
    intro d hd
    exact mem_iUnion.mpr ⟨⟨d, hd⟩, hSin ⟨d, hd⟩⟩

private theorem compact_contained
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u} := by
  intro X _ _ K hK
  let F : Set (Σ m, Cell X m) := {d | (K ∩ openCell X d.1 d.2).Nonempty}
  obtain ⟨A, hAfin, hA⟩ := finite_cells_contained hclosure F
    (compact_meets_finitely_many_cells K hK)
  refine ⟨A, hAfin, ?_⟩
  intro x hx
  have hcover : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
    rw [CWStructure.cover]
    exact mem_univ x
  obtain ⟨n, c, hxc⟩ := mem_iUnion₂.mp hcover
  apply hA
  exact mem_iUnion₂.mpr ⟨⟨n, c⟩, ⟨x, hx, hxc⟩, hxc⟩

private theorem compact_image_support
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v} := by
  intro X D _ _ _ _ f
  exact compact_contained hclosure (range f) (isCompact_range f.continuous)

private theorem finite_compact_images_support
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v} := by
  intro X _ _ ι _ D _ _ f
  have hK : IsCompact (⋃ i, range (f i)) :=
    isCompact_iUnion (fun i => isCompact_range (f i).continuous)
  obtain ⟨A, hAfin, hA⟩ := compact_contained hclosure _ hK
  exact ⟨A, hAfin, fun i => (subset_iUnion _ i).trans hA⟩

private theorem interval_map_support
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u} := by
  intro X _ _ f
  exact compact_image_support hclosure f

private theorem interval_homotopy_support
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u} := by
  intro X _ _ H
  exact compact_image_support hclosure H

private theorem finite_singular_simplex_support
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u} := by
  intro X _ _ σ
  have hK : IsCompact (⋃ s : ↥σ, range s.1.2) :=
    isCompact_iUnion (fun s => isCompact_range s.1.2.continuous)
  obtain ⟨A, hAfin, hA⟩ := compact_contained hclosure _ hK
  exact ⟨A, hAfin, fun s hs =>
    (subset_iUnion (fun t : ↥σ => range t.1.2) ⟨s, hs⟩).trans hA⟩

theorem subcomplexClosed : P202Specs.Topology.CellTopology.subcomplexClosed.{u} :=
  subcomplex_closed closureOpenCell

theorem subcomplexWeakTopology : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u} :=
  subcomplex_weak_topology closureOpenCell

theorem compactContainedInFiniteSubcomplex : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u} :=
  compact_contained closureOpenCell

theorem compactImageFiniteSupport : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u, v} :=
  compact_image_support closureOpenCell

theorem finiteCompactImagesFiniteSupport : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u, v} :=
  finite_compact_images_support closureOpenCell

theorem intervalMapFiniteSupport : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u} :=
  interval_map_support closureOpenCell

theorem intervalHomotopyFiniteSupport : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u} :=
  interval_homotopy_support closureOpenCell

theorem finiteSingularSimplexSupport : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u} :=
  finite_singular_simplex_support closureOpenCell

end P202.Topology
