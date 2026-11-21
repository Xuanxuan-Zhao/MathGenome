import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.Pasting
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.ContinuityTests
import Mathlib.Data.Set.UnionLift

/-!
Pasting over an open cover or a finite closed cover (`paper.tex`,
d10:02:pasting). The set map is constructed by choosing a covering piece
at each point; overlap agreement identifies its value with every applicable
piece map. No inhabitance of the index type, domain, or codomain is used.

The inverse image of any set is the union of the piece inverse images,
viewed in X by the subtype inclusions. For open pieces these inclusions
are open maps; for closed pieces they are closed maps, and a finite union
of closed sets is closed. No separation assumptions are needed.
-/

open Set
universe u v w

namespace D10Topology.Ch02

theorem pasting_existsUnique {X : Type u} {Y : Type v} {I : Type w}
    (A : I → Set X) (f : ∀ i, A i → Y)
    (hcover : (⋃ i, A i) = univ)
    (hagree : ∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃! g : X → Y, ∀ i (a : A i), g a.val = f i a := by
  refine ⟨Set.liftCover A f hagree hcover, fun i a => Set.liftCover_coe a, ?_⟩
  intro g hg
  funext x
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  exact (hg i ⟨x, hi⟩).trans (Set.liftCover_of_mem hi).symm

/-- The preimage formula is purely set-theoretic and uses the actual
subtype inclusions to regard each piece preimage as a subset of X. -/
theorem pasting_preimage {X : Type u} {Y : Type v} {I : Type w}
    (A : I → Set X) (f : ∀ i, A i → Y) (g : X → Y)
    (hcover : (⋃ i, A i) = univ)
    (hg : ∀ i (a : A i), g a.val = f i a) (V : Set Y) :
    g ⁻¹' V = ⋃ i, (Subtype.val : A i → X) '' ((f i) ⁻¹' V) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    apply mem_iUnion.mpr
    refine ⟨i, ⟨x, hi⟩, ?_, rfl⟩
    change f i ⟨x, hi⟩ ∈ V
    rwa [← hg i ⟨x, hi⟩]
  · intro hx
    obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.mp hx
    change g a.val ∈ V
    rwa [hg i a]

variable {X : Type u} {Y : Type v} {I : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

theorem pasting_continuous_of_open
    (A : I → Set X) (f : ∀ i, A i → Y) (g : X → Y)
    (hcover : (⋃ i, A i) = univ) (hf : ∀ i, Continuous (f i))
    (hg : ∀ i (a : A i), g a.val = f i a) (hA : ∀ i, IsOpen (A i)) :
    Continuous g := by
  apply (continuous_iff_open_preimages g).mpr
  intro V hV
  rw [pasting_preimage A f g hcover hg V]
  exact isOpen_iUnion fun i =>
    (hA i).isOpenMap_subtype_val _
      ((continuous_iff_open_preimages (f i)).mp (hf i) V hV)

theorem pasting_continuous_of_finite_closed [Finite I]
    (A : I → Set X) (f : ∀ i, A i → Y) (g : X → Y)
    (hcover : (⋃ i, A i) = univ) (hf : ∀ i, Continuous (f i))
    (hg : ∀ i (a : A i), g a.val = f i a) (hA : ∀ i, IsClosed (A i)) :
    Continuous g := by
  apply (continuous_iff_closed_preimages g).mpr
  intro F hF
  rw [pasting_preimage A f g hcover hg F]
  exact isClosed_iUnion_of_finite fun i =>
    (hA i).isClosedMap_subtype_val _
      ((continuous_iff_closed_preimages (f i)).mp (hf i) F hF)

theorem pasting_open
    (A : I → Set X) (f : ∀ i, A i → Y)
    (hcover : (⋃ i, A i) = univ) (hf : ∀ i, Continuous (f i))
    (hagree : ∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) (hA : ∀ i, IsOpen (A i)) :
    ∃! g : X → Y, (∀ i (a : A i), g a.val = f i a) ∧ Continuous g := by
  obtain ⟨g, hg, huniq⟩ := pasting_existsUnique A f hcover hagree
  exact ⟨g, ⟨hg, pasting_continuous_of_open A f g hcover hf hg hA⟩,
    fun k hk => huniq k hk.1⟩

theorem pasting_finite_closed [Finite I]
    (A : I → Set X) (f : ∀ i, A i → Y)
    (hcover : (⋃ i, A i) = univ) (hf : ∀ i, Continuous (f i))
    (hagree : ∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) (hA : ∀ i, IsClosed (A i)) :
    ∃! g : X → Y, (∀ i (a : A i), g a.val = f i a) ∧ Continuous g := by
  obtain ⟨g, hg, huniq⟩ := pasting_existsUnique A f hcover hagree
  exact ⟨g, ⟨hg, pasting_continuous_of_finite_closed A f g hcover hf hg hA⟩,
    fun k hk => huniq k hk.1⟩

end D10Topology.Ch02
