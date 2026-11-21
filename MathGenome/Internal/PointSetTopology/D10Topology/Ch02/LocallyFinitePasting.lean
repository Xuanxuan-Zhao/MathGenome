import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.LocallyFinitePasting
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.Pasting

/-!
Locally finite closed unions and pasting, for an arbitrary indexed family.
The canonical predicate is `LocallyFinite`, with the source's open-neighborhood
formulation proved below. For pasting, each closed target preimage is the union
of the ambient images of the piece preimages. These are closed subsets of the
closed pieces, and form a locally finite family by containment. Construction
and uniqueness of the pasted set map are reused from the arbitrary-cover
pasting theorem. In particular, no separation condition on the target is used.
-/

open Set
universe u v w

namespace D10Topology.Ch02

theorem locallyFinite_iff_open_neighborhood
    {X : Type u} {I : Type w} [TopologicalSpace X] (A : I → Set X) :
    LocallyFinite A ↔ ∀ x : X, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ {i | (A i ∩ U).Nonempty}.Finite := by
  constructor
  · intro h x
    obtain ⟨N, hN, hfin⟩ := h x
    obtain ⟨U, hUN, hU, hx⟩ := mem_nhds_iff.mp hN
    refine ⟨U, hU, hx, hfin.subset ?_⟩
    rintro i ⟨y, hyA, hyU⟩
    exact ⟨y, hyA, hUN hyU⟩
  · intro h x
    obtain ⟨U, hU, hx, hfin⟩ := h x
    exact ⟨U, hU.mem_nhds hx, hfin⟩

theorem locallyFinite_iUnion_isClosed
    {X : Type u} {I : Type w} [TopologicalSpace X] (A : I → Set X)
    (hloc : LocallyFinite A) (hA : ∀ i, IsClosed (A i)) :
    IsClosed (⋃ i, A i) :=
  hloc.isClosed_iUnion hA

theorem locallyFinite_iUnion_isClosed_of_subset
    {X : Type u} {I : Type w} [TopologicalSpace X] (A F : I → Set X)
    (hloc : LocallyFinite A) (hsub : ∀ i, F i ⊆ A i)
    (hF : ∀ i, IsClosed (F i)) : IsClosed (⋃ i, F i) :=
  locallyFinite_iUnion_isClosed F (hloc.subset hsub) hF

variable {X : Type u} {Y : Type v} {I : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

theorem pasting_continuous_of_locallyFinite_closed
    (A : I → Set X) (f : ∀ i, A i → Y) (g : X → Y)
    (hcover : (⋃ i, A i) = univ) (hf : ∀ i, Continuous (f i))
    (hg : ∀ i (a : A i), g a.val = f i a) (hA : ∀ i, IsClosed (A i))
    (hloc : LocallyFinite A) : Continuous g := by
  apply (continuous_iff_closed_preimages g).mpr
  intro F hF
  rw [pasting_preimage A f g hcover hg F]
  apply locallyFinite_iUnion_isClosed_of_subset A _ hloc
  · rintro i x ⟨a, _, rfl⟩
    exact a.property
  · intro i
    exact (hA i).isClosedMap_subtype_val _
      ((continuous_iff_closed_preimages (f i)).mp (hf i) F hF)

theorem pasting_locallyFinite_closed
    (A : I → Set X) (f : ∀ i, A i → Y)
    (hcover : (⋃ i, A i) = univ) (hf : ∀ i, Continuous (f i))
    (hagree : ∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) (hA : ∀ i, IsClosed (A i))
    (hloc : LocallyFinite A) :
    ∃! g : X → Y, (∀ i (a : A i), g a.val = f i a) ∧ Continuous g := by
  obtain ⟨g, hg, huniq⟩ := pasting_existsUnique A f hcover hagree
  exact ⟨g, ⟨hg,
    pasting_continuous_of_locallyFinite_closed A f g hcover hf hg hA hloc⟩,
    fun k hk => huniq k hk.1⟩

end D10Topology.Ch02
