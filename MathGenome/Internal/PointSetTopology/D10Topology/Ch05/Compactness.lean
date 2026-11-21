import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-!
Open-cover compactness, its canonical Mathlib bridges, both FIP criteria,
and compactness of closed subsets and finite unions. The arguments use no
separation or nonemptiness assumptions. The empty-subcover and empty-FIP
conventions are recorded explicitly at the end.
-/

open Set
universe u v

namespace D10Topology.Ch05

/-- Every ambient open cover has a finite subcover; the finite family may be empty. -/
def AmbientCoverCompact {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  ∀ U : Set (Set X), (∀ V ∈ U, IsOpen V) → K ⊆ ⋃₀ U →
    ∃ V : Set (Set X), V ⊆ U ∧ V.Finite ∧ K ⊆ ⋃₀ V

/-- Compactness is the open-cover property, without separation assumptions. -/
def CoverCompact (X : Type u) [TopologicalSpace X] : Prop :=
  AmbientCoverCompact (univ : Set X)

/-- The empty finite subfamily is included; its intersection is the whole type. -/
def HasFIP {X : Type u} (A : Set (Set X)) : Prop :=
  ∀ B : Set (Set X), B ⊆ A → B.Finite → (⋂₀ B).Nonempty

/-- A subset is compact in its canonical induced subspace topology. -/
def SubspaceCompact {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  CoverCompact K

variable {X : Type u} [t : TopologicalSpace X]

theorem ambientCoverCompact_iff_isCompact (K : Set X) :
    AmbientCoverCompact K ↔ IsCompact K := by
  constructor
  · intro h
    exact isCompact_generateFrom (TopologicalSpace.generateFrom_setOfPred_isOpen t).symm h
  · intro h U hU hcover
    obtain ⟨V, hVU, hV, hKV⟩ := h.elim_finite_subcover_image
      (b := U) (c := fun V : Set X => V) hU (by simpa only [sUnion_eq_biUnion] using hcover)
    exact ⟨V, hVU, hV, by simpa only [sUnion_eq_biUnion] using hKV⟩

theorem coverCompact_iff_isCompact_univ (X : Type u) [TopologicalSpace X] :
    CoverCompact X ↔ IsCompact (univ : Set X) :=
  ambientCoverCompact_iff_isCompact univ

theorem coverCompact_iff_compactSpace (X : Type u) [TopologicalSpace X] :
    CoverCompact X ↔ CompactSpace X :=
  (coverCompact_iff_isCompact_univ X).trans isCompact_univ_iff

theorem coverCompact_iff_closed_fip (X : Type u) [TopologicalSpace X] :
    CoverCompact X ↔ ∀ A : Set (Set X),
      (∀ F ∈ A, IsClosed F) → HasFIP A → (⋂₀ A).Nonempty := by
  constructor
  · intro h A hclosed hfip
    let : CompactSpace X := (coverCompact_iff_compactSpace X).mp h
    exact CompactSpace.nonempty_sInter hclosed hfip
  · intro h U hU hcover
    classical
    by_contra hn
    have hfip : HasFIP (compl '' U) := by
      intro B hBU hB
      have hsub : compl '' B ⊆ U := by
        rintro _ ⟨F, hFB, rfl⟩
        obtain ⟨V, hVU, rfl⟩ := hBU hFB
        simpa using hVU
      have hnot : ¬ (univ : Set X) ⊆ ⋃₀ (compl '' B) := by
        intro hc
        exact hn ⟨compl '' B, hsub, hB.image _, hc⟩
      obtain ⟨x, _, hx⟩ := Set.not_subset.mp hnot
      refine ⟨x, ?_⟩
      rwa [sInter_eq_compl_sUnion_compl]
    obtain ⟨x, hx⟩ := h (compl '' U)
      (by rintro _ ⟨V, hV, rfl⟩; exact (hU V hV).isClosed_compl) hfip
    have hxnot : x ∉ ⋃₀ U := by
      simpa only [← compl_sUnion, mem_compl_iff] using hx
    exact hxnot (hcover (mem_univ x))

theorem coverCompact_iff_fip_closures (X : Type u) [TopologicalSpace X] :
    CoverCompact X ↔ ∀ A : Set (Set X),
      HasFIP A → (⋂₀ (closure '' A)).Nonempty := by
  constructor
  · intro h A hfip
    let : CompactSpace X := (coverCompact_iff_compactSpace X).mp h
    have hf : ∀ F : Finset A, (⋂ i ∈ F, closure (i : Set X)).Nonempty := by
      intro F
      obtain ⟨x, hx⟩ := hfip (Subtype.val '' (F : Set A))
        (by rintro _ ⟨a, _, rfl⟩; exact a.property) (F.finite_toSet.image _)
      refine ⟨x, mem_iInter.mpr fun a => mem_iInter.mpr fun ha => ?_⟩
      exact subset_closure (mem_sInter.mp hx _ ⟨a, ha, rfl⟩)
    obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty
      (t := fun a : A => closure (a : Set X)) (fun _ => isClosed_closure) hf
    refine ⟨x, mem_sInter.mpr ?_⟩
    rintro _ ⟨S, hS, rfl⟩
    exact mem_iInter.mp hx ⟨S, hS⟩
  · intro h
    apply (coverCompact_iff_closed_fip X).mpr
    intro A hclosed hfip
    obtain ⟨x, hx⟩ := h A hfip
    refine ⟨x, mem_sInter.mpr fun S hS => ?_⟩
    have hxS := mem_sInter.mp hx _ ⟨S, hS, rfl⟩
    rwa [(hclosed S hS).closure_eq] at hxS

theorem subspaceCompact_iff_compactSpace (K : Set X) :
    SubspaceCompact K ↔ CompactSpace K :=
  coverCompact_iff_compactSpace K

theorem subspaceCompact_iff_isCompact (K : Set X) :
    SubspaceCompact K ↔ IsCompact K :=
  (subspaceCompact_iff_compactSpace K).trans isCompact_iff_compactSpace.symm

theorem subspaceCompact_iff_ambient_open_cover (K : Set X) :
    SubspaceCompact K ↔ ∀ U : Set (Set X),
      (∀ V ∈ U, IsOpen V) → K ⊆ ⋃₀ U →
        ∃ V : Set (Set X), V ⊆ U ∧ V.Finite ∧ K ⊆ ⋃₀ V :=
  (subspaceCompact_iff_isCompact K).trans (ambientCoverCompact_iff_isCompact K).symm

theorem closed_subset_compact (hX : CoverCompact X) (F : Set X) (hF : IsClosed F) :
    SubspaceCompact F := by
  let : CompactSpace X := (coverCompact_iff_compactSpace X).mp hX
  exact (subspaceCompact_iff_isCompact F).mpr hF.isCompact

theorem closed_subset_of_compact (K F : Set X) (hK : SubspaceCompact K)
    (hF : IsClosed F) (hFK : F ⊆ K) : SubspaceCompact F :=
  (subspaceCompact_iff_isCompact F).mpr
    (((subspaceCompact_iff_isCompact K).mp hK).of_isClosed_subset hF hFK)

theorem finite_union_compact (A : Set (Set X)) (hA : A.Finite)
    (hK : ∀ K ∈ A, SubspaceCompact K) : SubspaceCompact (⋃₀ A) :=
  (subspaceCompact_iff_isCompact _).mpr
    (hA.isCompact_sUnion fun K h => (subspaceCompact_iff_isCompact K).mp (hK K h))

theorem finite_indexed_union_compact {ι : Type v} [Finite ι] (K : ι → Set X)
    (hK : ∀ i, SubspaceCompact (K i)) : SubspaceCompact (⋃ i, K i) :=
  (subspaceCompact_iff_isCompact _).mpr
    (isCompact_iUnion fun i => (subspaceCompact_iff_isCompact _).mp (hK i))

theorem empty_subset_compact (X : Type u) [TopologicalSpace X] :
    SubspaceCompact (∅ : Set X) :=
  (subspaceCompact_iff_isCompact _).mpr isCompact_empty

theorem empty_union_compact (X : Type u) [TopologicalSpace X] :
    SubspaceCompact (⋃₀ (∅ : Set (Set X))) := by
  simpa only [sUnion_empty] using empty_subset_compact X

theorem empty_space_empty_subcover (X : Type u) [TopologicalSpace X] [IsEmpty X]
    (U : Set (Set X)) :
    (∅ : Set (Set X)) ⊆ U ∧ (∅ : Set (Set X)).Finite ∧
      (univ : Set X) ⊆ ⋃₀ (∅ : Set (Set X)) := by
  simp

theorem empty_space_compact (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    CoverCompact X := by
  intro U _ _
  exact ⟨∅, empty_space_empty_subcover X U⟩

theorem fip_empty_family_iff (X : Type u) :
    HasFIP (∅ : Set (Set X)) ↔ Nonempty X := by
  constructor
  · intro h
    obtain ⟨x, _⟩ := h ∅ (empty_subset _) finite_empty
    exact ⟨x⟩
  · intro h B hB _
    have : B = ∅ := subset_empty_iff.mp hB
    subst B
    simp

theorem no_fip_on_empty_space (X : Type u) [IsEmpty X] (A : Set (Set X)) :
    ¬ HasFIP A := by
  intro h
  obtain ⟨x, _⟩ := h ∅ (empty_subset _) finite_empty
  exact isEmptyElim x

end D10Topology.Ch05
