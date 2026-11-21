import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.LindelofCompactProduct
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.TubesAndFiniteProducts

/-!
A Lindelöf space times a compact space is Lindelöf (`d10:08:permanence`).
Finite covers of the compact fibers extend to tubes. A countable subcover
of the first factor by these tubes selects countably many finite families
from the original cover. No separation or inhabitedness assumptions occur;
finite and countable subfamilies may be empty.
-/

open Set
universe u v w

namespace D10Topology.Ch08

theorem lindelof_compact_product_countable_subcover
    {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K]
    (hX : LindelofSpace X) (hK : Ch05.CoverCompact K)
    {ι : Type w} (U : ι → Set (X × K)) (ho : ∀ i, IsOpen (U i))
    (hc : (⋃ i, U i) = univ) :
    ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ := by
  classical
  have hcompact : IsCompact (univ : Set K) :=
    (Ch05.coverCompact_iff_isCompact_univ K).mp hK
  -- Compactness of each fiber gives a finite family of original cover members.
  have hfiber : ∀ x : X, ∃ F : Finset ι,
      ({x} : Set X) ×ˢ (univ : Set K) ⊆ ⋃ i ∈ F, U i := by
    intro x
    exact (isCompact_singleton.prod hcompact).elim_finite_subcover U ho
      (hc ▸ subset_univ _)
  choose F hF using hfiber
  -- The tube lemma enlarges the finite cover of a fiber to a neighborhood in X.
  have htube : ∀ x : X, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ V ×ˢ (univ : Set K) ⊆ ⋃ i ∈ F x, U i := by
    intro x
    exact Ch05.tube_lemma hK x _ (isOpen_biUnion fun i _ => ho i) (hF x)
  choose V hVo hxV hV using htube
  have hVcover : (⋃ x, V x) = univ :=
    eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨S, hSc, hScover⟩ :=
    lindelof_indexed_countable_subcover hX V hVo hVcover
  -- A countable union of finite index sets is a countable set of indices.
  refine ⟨⋃ x ∈ S, (F x : Set ι),
    hSc.biUnion (fun x _ => (F x).finite_toSet.countable), ?_⟩
  apply eq_univ_of_forall
  rintro ⟨x, k⟩
  obtain ⟨y, hyS, hxy⟩ := mem_iUnion₂.mp (hScover ▸ mem_univ x)
  have hxk : (x, k) ∈ ⋃ i ∈ F y, U i := hV y ⟨hxy, mem_univ k⟩
  obtain ⟨i, hiF, hki⟩ := mem_iUnion₂.mp hxk
  exact mem_iUnion₂.mpr ⟨i, mem_iUnion₂.mpr ⟨y, hyS, hiF⟩, hki⟩

theorem lindelof_compact_product
    {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K]
    (hX : LindelofSpace X) (hK : Ch05.CoverCompact K) :
    LindelofSpace (X × K) := by
  apply lindelof_iff_countable_subcover.mpr
  intro ι U ho hc
  exact lindelof_compact_product_countable_subcover hX hK U ho hc

end D10Topology.Ch08
