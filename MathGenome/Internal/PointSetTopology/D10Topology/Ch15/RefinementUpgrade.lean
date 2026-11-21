import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.RefinementUpgrade
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.ClosureSums
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.ShrinkingHierarchy

/-! The three upgrades of paper.tex, d10:15:michael. First remove all earlier
layers from each member of a sigma locally finite open cover. Regular shrinking
then yields closed locally finite refinements. A second closed refinement,
subordinate to neighborhoods meeting only finitely many members of the first,
provides locally finite open expansions. No T₁ hypothesis is used. -/

open Set
open scoped Topology
universe u v

namespace D10Topology.Ch15

variable {X : Type u} [TopologicalSpace X]

/-- Removing earlier open layers produces a locally finite (possibly nonopen)
cover refining a sigma locally finite open cover. -/
lemma sigmaLocallyFinite_arbitrary_refinement {J : Type v} (V : J → Set X)
    (hVo : ∀ j, IsOpen (V j)) (hV : (⋃ j, V j) = univ)
    (hσ : SigmaLocallyFinite V) :
    ∃ S : J → Set X, (⋃ j, S j) = univ ∧ LocallyFinite S ∧ ∀ j, S j ⊆ V j := by
  classical
  obtain ⟨c, hc⟩ := (sigmaLocallyFinite_iff_layers V).mp hσ
  let S : J → Set X := fun j => V j \ ⋃ k : {k // c k < c j}, V k
  have hSV : ∀ j, S j ⊆ V j := fun _ _ h => h.1
  refine ⟨S, ?_, ?_, hSV⟩
  · apply iUnion_eq_univ_iff.mpr
    intro x
    have hex : ∃ n, ∃ j, c j = n ∧ x ∈ V j := by
      obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hV x
      exact ⟨c j, j, rfl, hj⟩
    obtain ⟨j, hjc, hjx⟩ := Nat.find_spec hex
    refine ⟨j, hjx, ?_⟩
    rintro h
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    exact Nat.find_min hex (hjc ▸ k.property) ⟨k.val, rfl, hk⟩
  · intro x
    obtain ⟨j₀, hx₀⟩ := iUnion_eq_univ_iff.mp hV x
    obtain ⟨N, hN, hf⟩ : ∃ N : ℕ → Set X, (∀ n, N n ∈ 𝓝 x) ∧
        ∀ n, {j : {j // c j = n} | (V j ∩ N n).Nonempty}.Finite := by
      choose N hN hf using fun n => hc n x
      exact ⟨N, hN, hf⟩
    let H := V j₀ ∩ ⋂ n ∈ Finset.range (c j₀ + 1), N n
    have hH : H ∈ 𝓝 x :=
      Filter.inter_mem ((hVo j₀).mem_nhds hx₀)
        (Filter.biInter_mem (Finset.finite_toSet _) |>.mpr fun n _ => hN n)
    have hfinite : (⋃ n ∈ Finset.range (c j₀ + 1),
        Subtype.val '' {j : {j // c j = n} | (V j ∩ N n).Nonempty}).Finite :=
      (Finset.finite_toSet _).biUnion fun n _ => (hf n).image Subtype.val
    refine ⟨H, hH, hfinite.subset ?_⟩
    rintro j ⟨y, hyS, hyH⟩
    have hjle : c j ≤ c j₀ := by
      by_contra h
      exact hyS.2 (mem_iUnion.mpr ⟨⟨j₀, Nat.lt_of_not_ge h⟩, hyH.1⟩)
    have hjrange : c j ∈ Finset.range (c j₀ + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hjle)
    refine mem_iUnion.mpr ⟨c j, mem_iUnion.mpr ⟨hjrange, ?_⟩⟩
    refine ⟨⟨j, rfl⟩, ?_, rfl⟩
    exact ⟨y, hSV j hyS, mem_iInter₂.mp hyH.2 (c j) hjrange⟩

/-- First upgrade: every open cover has a locally finite arbitrary refinement. -/
private lemma arbitrary_refinements
    (hσ : ∀ (I : Type u) (U : I → Set X), (∀ i, IsOpen (U i)) →
      (⋃ i, U i) = univ → ∃ (J : Type u) (V : J → Set X),
        (∀ j, IsOpen (V j)) ∧ SigmaLocallyFinite V ∧ CoverRefinement U V)
    (I : Type u) (U : I → Set X) (hUo : ∀ i, IsOpen (U i))
    (hU : (⋃ i, U i) = univ) :
    ∃ (J : Type u) (B : J → Set X), LocallyFinite B ∧ CoverRefinement U B := by
  obtain ⟨J, V, hVo, hVσ, hVr⟩ := hσ I U hUo hU
  obtain ⟨S, hScov, hSf, hSV⟩ :=
    sigmaLocallyFinite_arbitrary_refinement V hVo hVr.1 hVσ
  refine ⟨J, S, hSf, hScov, ?_⟩
  intro j
  obtain ⟨i, hi⟩ := hVr.2 j
  exact ⟨i, (hSV j).trans hi⟩

/-- Second upgrade: regular shrinking followed by closure yields a closed
locally finite refinement of every open cover. -/
private lemma closed_refinements [RegularSpace X]
    (hσ : ∀ (I : Type u) (U : I → Set X), (∀ i, IsOpen (U i)) →
      (⋃ i, U i) = univ → ∃ (J : Type u) (V : J → Set X),
        (∀ j, IsOpen (V j)) ∧ SigmaLocallyFinite V ∧ CoverRefinement U V)
    (I : Type u) (U : I → Set X) (hUo : ∀ i, IsOpen (U i))
    (hU : (⋃ i, U i) = univ) :
    ∃ (J : Type u) (B : J → Set X), (∀ j, IsClosed (B j)) ∧
      LocallyFinite B ∧ CoverRefinement U B := by
  classical
  have hsmall : ∀ x : X, ∃ G : Set X, IsOpen G ∧ x ∈ G ∧
      ∃ i, closure G ⊆ U i := by
    intro x
    obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.mp hU x
    obtain ⟨G, hGo, hxG, _, hGU⟩ :=
      (Ch07.regular_iff_shrinking X).mp ‹RegularSpace X› x (U i) (hUo i) hi
    exact ⟨G, hGo, hxG, i, hGU⟩
  choose G hGo hxG a ha using hsmall
  obtain ⟨J, B, hBf, hBr⟩ := arbitrary_refinements hσ X G hGo
    (iUnion_eq_univ_iff.mpr fun x => ⟨x, hxG x⟩)
  refine ⟨J, fun j => closure (B j), fun _ => isClosed_closure, hBf.closure, ?_, ?_⟩
  · apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hBr.1 x
    exact ⟨j, subset_closure hj⟩
  · intro j
    obtain ⟨x, hx⟩ := hBr.2 j
    exact ⟨a x, (closure_mono hx).trans (ha x)⟩

/-- A closed locally finite cover whose members meet only finitely many `B j`
gives locally finite open expansions of the `B j`. The `B j` themselves need
not be closed. This is the final expansion construction in the source. -/
lemma locallyFinite_open_expansion {J : Type v} {K : Type u}
    (B : J → Set X) (C : K → Set X)
    (hCo : ∀ k, IsClosed (C k)) (hCf : LocallyFinite C)
    (hCcov : (⋃ k, C k) = univ)
    (hCB : ∀ k, {j | (B j ∩ C k).Nonempty}.Finite) :
    ∃ E : J → Set X, (∀ j, IsOpen (E j)) ∧ LocallyFinite E ∧ ∀ j, B j ⊆ E j := by
  classical
  let E : J → Set X := fun j => (⋃ k : {k // Disjoint (C k) (B j)}, C k)ᶜ
  have hBE : ∀ j, B j ⊆ E j := by
    intro j y hy h
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp k.property hk hy
  refine ⟨E, ?_, ?_, hBE⟩
  · intro j
    exact ((hCf.comp_injective
      (g := fun k : {k // Disjoint (C k) (B j)} => k.val) Subtype.val_injective).isClosed_iUnion
      (fun k => hCo k.val)).isOpen_compl
  · intro x
    obtain ⟨N, hN, hf⟩ := hCf x
    have hfinite : (⋃ k ∈ {k | (C k ∩ N).Nonempty},
        {j | (B j ∩ C k).Nonempty}).Finite := hf.biUnion fun k _ => hCB k
    refine ⟨N, hN, hfinite.subset ?_⟩
    rintro j ⟨y, hyE, hyN⟩
    obtain ⟨k, hyC⟩ := iUnion_eq_univ_iff.mp hCcov y
    refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨y, hyC, hyN⟩, ?_⟩⟩
    by_contra h
    have hd : Disjoint (C k) (B j) := by
      apply Set.disjoint_left.mpr
      intro z hzC hzB
      exact h ⟨z, hzB, hzC⟩
    exact hyE (mem_iUnion.mpr ⟨⟨k, hd⟩, hyC⟩)

/-- Refinement upgrade (Michael): regularity, without T₁, and sigma locally
finite open refinements for every open cover imply paracompactness. -/
theorem refinement_upgrade (X : Type u) [TopologicalSpace X]
    (hR : RegularSpace X)
    (hσ : ∀ (I : Type u) (U : I → Set X), (∀ i, IsOpen (U i)) →
      (⋃ i, U i) = univ → ∃ (J : Type u) (V : J → Set X),
        (∀ j, IsOpen (V j)) ∧ SigmaLocallyFinite V ∧ CoverRefinement U V) :
    Paracompact X := by
  classical
  let : RegularSpace X := hR
  constructor
  intro I U hUo hU
  obtain ⟨J, B, _, hBf, hBr⟩ := closed_refinements hσ I U hUo hU
  obtain ⟨N, hNo, hxN, hNf⟩ : ∃ N : X → Set X,
      (∀ x, IsOpen (N x)) ∧ (∀ x, x ∈ N x) ∧
        ∀ x, {j | (B j ∩ N x).Nonempty}.Finite := by
    choose N hNo hxN hNf using (locallyFinite_iff_open_neighborhood B).mp hBf
    exact ⟨N, hNo, hxN, hNf⟩
  obtain ⟨K, C, hCc, hCf, hCr⟩ := closed_refinements hσ X N hNo
    (iUnion_eq_univ_iff.mpr fun x => ⟨x, hxN x⟩)
  have hCB : ∀ k, {j | (B j ∩ C k).Nonempty}.Finite := by
    intro k
    obtain ⟨x, hx⟩ := hCr.2 k
    apply (hNf x).subset
    rintro j ⟨y, hyB, hyC⟩
    exact ⟨y, hyB, hx hyC⟩
  obtain ⟨E, hEo, hEf, hBE⟩ := locallyFinite_open_expansion B C hCc hCf hCr.1 hCB
  choose a ha using hBr.2
  refine ⟨J, fun j => E j ∩ U (a j), fun j => (hEo j).inter (hUo (a j)), ?_,
    hEf.subset (fun _ => inter_subset_left), fun j => ⟨a j, inter_subset_right⟩⟩
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hBr.1 x
  exact ⟨j, hBE j hj, ha j hj⟩

end D10Topology.Ch15
