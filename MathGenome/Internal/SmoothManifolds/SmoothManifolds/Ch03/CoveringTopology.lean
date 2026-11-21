import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Models
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.CoveringTopology
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Compactness.Lindelof

namespace SmoothManifolds.CoveringTopology
open Set Topology TopologicalSpace
universe u v w

section OpenCovers
variable {X : Type u} [TopologicalSpace X]

/-- A second-countable open set meets only countably many members of a disjoint
open family. Countability of the ambient space is unnecessary. -/
theorem countable_intersecting_family {J : Type v} (V : J → Set X)
    (ho : ∀ j, IsOpen (V j)) (hd : Pairwise fun i j => Disjoint (V i) (V j))
    (U : Set X) [SecondCountableTopology U] :
    {j | (U ∩ V j).Nonempty}.Countable := by
  have hd' : ({j | (U ∩ V j).Nonempty} : Set J).PairwiseDisjoint
      (fun j => (Subtype.val : U → X) ⁻¹' V j) := by
    intro i _ j _ hij
    exact (hd hij).preimage _
  apply hd'.countable_of_isOpen
  · intro j _
    exact (ho j).preimage continuous_subtype_val
  · rintro j ⟨x, hx, hV⟩
    exact ⟨⟨x, hx⟩, hV⟩

/-- Countably branching sheet chains in a preconnected space give a countable
subcover. This is the finite-chain argument, without a countability hypothesis
on the indexing type of the original cover. -/
theorem secondCountable_of_countable_neighbors {J : Type v} [PreconnectedSpace X]
    (V : J → Set X) (ho : ∀ j, IsOpen (V j))
    [∀ j, SecondCountableTopology (V j)]
    (hc : ⋃ j, V j = univ)
    (hn : ∀ i, {j | (V i ∩ V j).Nonempty}.Countable) :
    SecondCountableTopology X := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · infer_instance
  obtain ⟨x⟩ := hX
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hc.symm ▸ mem_univ x)
  let R : ℕ → Set J := fun n => Nat.rec {i₀}
    (fun _ s => s ∪ ⋃ i ∈ s, {j | (V i ∩ V j).Nonempty}) n
  have hR : ∀ n, (R n).Countable := by
    intro n
    induction n with
    | zero => exact countable_singleton _
    | succ n ih => exact ih.union (ih.biUnion fun i _ => hn i)
  let S : Set J := ⋃ n, R n
  have hS : S.Countable := countable_iUnion hR
  have hstep {i j : J} (hi : i ∈ S) (hij : (V i ∩ V j).Nonempty) : j ∈ S := by
    obtain ⟨n, hi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨n + 1, Or.inr (mem_iUnion₂.mpr ⟨i, hi, hij⟩)⟩
  let W : Set X := ⋃ i ∈ S, V i
  have hWo : IsOpen W := isOpen_iUnion fun i => isOpen_iUnion fun _ => ho i
  have hWc : IsOpen Wᶜ := by
    apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc.symm ▸ mem_univ z)
    refine ⟨V j, ?_, ho j, hj⟩
    intro y hy hyW
    obtain ⟨i, hi, hiy⟩ := mem_iUnion₂.mp hyW
    exact hz (mem_iUnion₂.mpr ⟨j, hstep hi ⟨y, hiy, hy⟩, hj⟩)
  have hWu : W = univ := (show IsClopen W from ⟨isOpen_compl_iff.mp hWc, hWo⟩).eq_univ
    ⟨x, mem_iUnion₂.mpr ⟨i₀, mem_iUnion.mpr ⟨0, mem_singleton i₀⟩, hi₀⟩⟩
  let : Countable S := hS.to_subtype
  exact secondCountableTopology_of_countable_cover (fun i : S => ho i)
    (by simpa only [iUnion_subtype] using hWu)

end OpenCovers

section Sheets
variable {E : Type u} {M : Type v} {F : Type w}
  [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace F]
  {p : E → M} {U : Set M}

/-- One inverse branch of an evenly covered neighborhood. -/
def sheetMap (H : p ⁻¹' U ≃ₜ U × F) (i : F) (x : U) : E :=
  (H.symm (x, i)).val

theorem sheetMap_isOpenEmbedding [DiscreteTopology F]
    (hU : IsOpen (p ⁻¹' U)) (H : p ⁻¹' U ≃ₜ U × F) (i : F) :
    IsOpenEmbedding (sheetMap H i) := by
  have hi : IsOpenEmbedding (fun x : U => (x, i)) :=
    ⟨isEmbedding_prodMkLeft i, by
      have heq : range (fun x : U => (x, i)) = (Prod.snd : U × F → F) ⁻¹' {i} := by
        ext x
        simp only [mem_range, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨y, rfl, rfl⟩; rfl
        · intro h; exact ⟨x.1, Prod.ext rfl h.symm⟩
      rw [heq]
      exact (isOpen_discrete {i}).preimage continuous_snd⟩
  exact hU.isOpenEmbedding_subtypeVal.comp (H.symm.isOpenEmbedding.comp hi)

theorem sheetMap_pairwiseDisjoint (H : p ⁻¹' U ≃ₜ U × F) :
    Pairwise (fun i j => Disjoint (range (sheetMap H i)) (range (sheetMap H j))) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, h⟩
  have he : H.symm (y, j) = H.symm (x, i) := Subtype.ext h
  exact hij (congrArg Prod.snd (H.symm.injective he)).symm

theorem mem_sheetMap_range (H : p ⁻¹' U ≃ₜ U × F) {e : E} (he : p e ∈ U) :
    ∃ i, e ∈ range (sheetMap H i) := by
  exact ⟨(H ⟨e, he⟩).2, (H ⟨e, he⟩).1, congrArg Subtype.val (H.symm_apply_apply ⟨e, he⟩)⟩

end Sheets

section GeneralCoverings
variable {E : Type u} {M : Type v} [TopologicalSpace E] [TopologicalSpace M]
  {p : E → M}

/-- Separate points with different projections in the base, and points in the
same fiber by the covering's disjoint sheets. -/
theorem hausdorff_of_covering [T2Space M] (hp : IsCoveringMap p) : T2Space E := by
  constructor
  intro x y hxy
  by_cases h : p x = p y
  · exact hp.isSeparatedMap x y h hxy
  · obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := t2_separation h
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous,
      hV.preimage hp.continuous, hx, hy, hd.preimage p⟩

/-- Choose a countable cover in the base and all the sheets above it. Every
sheet is second countable, and each sheet meets at most countably many others.
When all fibers are countable, the entire sheet index type is countable. -/
theorem exists_sheet_cover [SecondCountableTopology M] (hp : IsCoveringMap p) :
    ∃ (J : Type (max u v)) (V : J → Set E),
      (∀ j, IsOpen (V j)) ∧ (∀ j, SecondCountableTopology (V j)) ∧
      (⋃ j, V j = univ) ∧ (∀ i, {j | (V i ∩ V j).Nonempty}.Countable) ∧
      ((∀ y, (p ⁻¹' {y}).Countable) → Countable J) := by
  classical
  choose U hy hU hpU H _hH using fun y => (hp y).2
  let : ∀ y, DiscreteTopology (p ⁻¹' {y}) := fun y => (hp y).1
  obtain ⟨C, hC, hcov⟩ := TopologicalSpace.countable_cover_nhds (fun y => (hU y).mem_nhds (hy y))
  let : Countable C := hC.to_subtype
  let J := Σ y : C, p ⁻¹' {(y : M)}
  let V : J → Set E := fun j => range (sheetMap (H j.1) j.2)
  have hopen (j : J) : IsOpen (V j) :=
    (sheetMap_isOpenEmbedding (hpU j.1) (H j.1) j.2).isOpen_range
  have hsc (j : J) : SecondCountableTopology (V j) :=
    (sheetMap_isOpenEmbedding (hpU j.1) (H j.1) j.2).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine ⟨J, V, hopen, hsc, ?_, ?_, ?_⟩
  · apply eq_univ_iff_forall.mpr
    intro e
    obtain ⟨y, hyC, heU⟩ := mem_iUnion₂.mp (hcov.symm ▸ mem_univ (p e))
    obtain ⟨i, hi⟩ := mem_sheetMap_range (H y) heU
    exact mem_iUnion.mpr ⟨⟨⟨y, hyC⟩, i⟩, hi⟩
  · intro j
    let : SecondCountableTopology (V j) := hsc j
    have hN (y : C) : {i : p ⁻¹' {(y : M)} | (V j ∩ V ⟨y, i⟩).Nonempty}.Countable :=
      countable_intersecting_family (fun i => V ⟨y, i⟩) (fun i => hopen ⟨y, i⟩)
        (sheetMap_pairwiseDisjoint (H y)) (V j)
    have hcount : (⋃ y : C,
        (fun i : p ⁻¹' {(y : M)} => (⟨y, i⟩ : J)) ''
          {i | (V j ∩ V ⟨y, i⟩).Nonempty}).Countable :=
      countable_iUnion (fun y : C => (hN y).image
        (fun i : p ⁻¹' {(y : M)} => (⟨y, i⟩ : J)))
    apply hcount.mono
    rintro ⟨y, i⟩ hi
    exact mem_iUnion.mpr ⟨y, mem_image_of_mem _ hi⟩
  · intro h
    let : ∀ y : C, Countable (p ⁻¹' {(y : M)}) := fun y => (h y).to_subtype
    infer_instance

theorem secondCountable_covering_of_countable_fibers [SecondCountableTopology M]
    (hp : IsCoveringMap p) (hf : ∀ y, (p ⁻¹' {y}).Countable) :
    SecondCountableTopology E := by
  obtain ⟨J, V, ho, hsc, hc, _, hJ⟩ := exists_sheet_cover hp
  let : Countable J := hJ hf
  let : ∀ j, SecondCountableTopology (V j) := hsc
  exact secondCountableTopology_of_countable_cover ho hc

theorem secondCountable_covering_of_preconnected [SecondCountableTopology M]
    [PreconnectedSpace E] (hp : IsCoveringMap p) : SecondCountableTopology E := by
  obtain ⟨J, V, ho, hsc, hc, hn, _⟩ := exists_sheet_cover hp
  let : ∀ j, SecondCountableTopology (V j) := hsc
  exact secondCountable_of_countable_neighbors V ho hc hn

end GeneralCoverings

section ManifoldCoverings
variable {n : ℕ} {kind : ModelKind} {M : Type u} {E : Type v}
  [TopologicalSpace M] [TopologicalSpace E]

/-- The Hausdorff axiom for the total space, with its original topology. -/
theorem hausdorff (A : TopologicalManifold n kind M) (p : E → M)
    (hp : IsCoveringMap p) : T2Space E := by
  let := A.hausdorff
  exact hausdorff_of_covering hp

/-- Countable fibers suffice, with no connectedness or nonemptiness condition. -/
theorem secondCountable_of_countable_fibers (A : TopologicalManifold n kind M)
    (p : E → M) (hp : IsCoveringMap p) (hf : ∀ y, (p ⁻¹' {y}).Countable) :
    SecondCountableTopology E := by
  let := A.secondCountable
  exact secondCountable_covering_of_countable_fibers hp hf

/-- In the connected case second countability of the total space is proved,
without assuming countability of fibers. Preconnectedness includes the empty case. -/
theorem secondCountable_of_preconnected [PreconnectedSpace E]
    (A : TopologicalManifold n kind M) (p : E → M) (hp : IsCoveringMap p) :
    SecondCountableTopology E := by
  let := A.secondCountable
  exact secondCountable_covering_of_preconnected hp

/-- Discrete fibers in the second-countable total space are countable. -/
theorem countable_fibers_of_preconnected [PreconnectedSpace E]
    (A : TopologicalManifold n kind M) (p : E → M) (hp : IsCoveringMap p) (y : M) :
    (p ⁻¹' {y}).Countable := by
  let := secondCountable_of_preconnected A p hp
  let := (hp y).discreteTopology_fiber
  exact countable_univ_iff.mp
    (show (univ : Set (p ⁻¹' {y})).Countable from isLindelof_univ.countable_of_discrete)
    |>.to_set

end ManifoldCoverings

end SmoothManifolds.CoveringTopology
