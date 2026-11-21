import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.OnePointConstruction
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.SubspacesExhaustion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.CompactImagesAndSeparation

open Set Topology
universe u v
namespace D10Topology.Ch11

abbrev Xplus (X : Type u) := OnePoint X
abbrev plusInclusion {X : Type u} : X → Xplus X := OnePoint.some
def plusInfinity (X : Type u) : Xplus X := OnePoint.infty
abbrev plusTopology (X : Type u) [TopologicalSpace X] : TopologicalSpace (Xplus X) :=
  inferInstance

theorem one_point_opens {X : Type u} [TopologicalSpace X] (hX : LCH X)
    (U : Set (Xplus X)) :
    IsOpen U ↔ (∃ V : Set X, IsOpen V ∧ U = plusInclusion '' V) ∨
      ∃ K : Set X, IsCompact K ∧ U = (plusInclusion '' K)ᶜ := by
  let : T2Space X := hX.2
  constructor
  · intro hU
    by_cases hi : OnePoint.infty ∈ U
    · right
      refine ⟨(plusInclusion ⁻¹' U)ᶜ, ((OnePoint.isOpen_iff_of_mem hi).mp hU).2, ?_⟩
      ext z
      induction z using OnePoint.rec with
      | infty => simp [plusInclusion, hi]
      | coe x => simp [plusInclusion]
    · left
      refine ⟨plusInclusion ⁻¹' U, OnePoint.continuous_coe.isOpen_preimage _ hU, ?_⟩
      ext z
      induction z using OnePoint.rec with
      | infty => simp [plusInclusion, hi]
      | coe x => simp [plusInclusion]
  · rintro (⟨V, hV, rfl⟩ | ⟨K, hK, rfl⟩)
    · exact OnePoint.isOpen_image_coe.mpr hV
    · exact OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩

theorem one_point_compact_hausdorff (X : Type u) [TopologicalSpace X] (hX : LCH X) :
    CompactSpace (Xplus X) ∧ T2Space (Xplus X) := by
  let : T2Space X := hX.2
  let : WeaklyLocallyCompactSpace X :=
    (locallyCompact_iff_weaklyLocallyCompactSpace X).mp hX.1
  exact ⟨inferInstance, inferInstance⟩

theorem one_point_open_embedding (X : Type u) [TopologicalSpace X] :
    IsOpenEmbedding (@plusInclusion X) := OnePoint.isOpenEmbedding_coe

theorem one_point_induced_topology (X : Type u) [t : TopologicalSpace X] :
    TopologicalSpace.induced (@plusInclusion X) inferInstance = t :=
  OnePoint.isOpenEmbedding_coe.isInducing.eq_induced.symm

theorem one_point_topology_unique (X : Type u) [TopologicalSpace X]
    (t : TopologicalSpace (Xplus X)) (hc : @CompactSpace (Xplus X) t)
    (ht : @T2Space (Xplus X) t)
    (hf : @IsEmbedding X (Xplus X) _ t plusInclusion) :
    t = @OnePoint.instTopologicalSpace X ‹TopologicalSpace X› := by
  let e : @Homeomorph (OnePoint X) (OnePoint X)
      (@OnePoint.instTopologicalSpace X ‹TopologicalSpace X›) t :=
    @OnePoint.equivOfIsEmbeddingOfRangeEq X (OnePoint X) _ t ht hc
      OnePoint.infty plusInclusion hf OnePoint.compl_infty.symm
  have he : (e : OnePoint X → OnePoint X) = id := by
    funext z
    induction z using OnePoint.rec <;> rfl
  apply TopologicalSpace.ext
  funext U
  apply propext
  have h := @Homeomorph.isOpen_preimage (OnePoint X) (OnePoint X)
    (@OnePoint.instTopologicalSpace X ‹TopologicalSpace X›) t e U
  rw [he] at h
  exact h.symm

theorem one_point_infinity_isolated_iff (X : Type u) [TopologicalSpace X] :
    IsOpen ({plusInfinity X} : Set (Xplus X)) ↔ CompactSpace X := by
  rw [OnePoint.isOpen_iff_of_mem' (show OnePoint.infty ∈
    ({plusInfinity X} : Set (Xplus X)) from rfl)]
  simp only [plusInfinity, OnePoint.coe_preimage_infty, compl_empty, isOpen_empty,
    and_true, isCompact_univ_iff]

theorem one_point_dense_iff (X : Type u) [TopologicalSpace X] :
    DenseRange (@plusInclusion X) ↔ ¬CompactSpace X := by
  constructor
  · intro hd hc
    let := hc
    have hclosed : IsClosed (range (@plusInclusion X)) := by
      rw [← image_univ]
      exact OnePoint.isClosed_image_coe.mpr ⟨isClosed_univ, isCompact_univ⟩
    exact OnePoint.infty_notMem_range_coe (hclosed.closure_eq ▸ hd OnePoint.infty)
  · intro h
    let : NoncompactSpace X := not_compactSpace_iff.mp h
    exact OnePoint.denseRange_coe

theorem one_point_empty (X : Type u) [IsEmpty X] (z : Xplus X) :
    z = plusInfinity X := Subsingleton.elim _ _

theorem one_point_converse {X : Type u} {Z : Type v} [TopologicalSpace X]
    [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (p : Z) (f : X → Z)
    (hf : IsEmbedding f) (hr : range f = {p}ᶜ) :
    LCH X ∧ ∃ e : Xplus X ≃ₜ Z,
      (∀ x, e (plusInclusion x) = f x) ∧ e (plusInfinity X) = p := by
  let : T2Space X := hf.t2Space
  have ho : IsOpen (range f) := hr ▸ isClosed_singleton.isOpen_compl
  let : LocallyCompactSpace X := hf.isInducing.locallyCompactSpace ho.isLocallyClosed
  refine ⟨⟨locallyCompact_of_mathlib_locallyCompactSpace X inferInstance, inferInstance⟩,
    OnePoint.equivOfIsEmbeddingOfRangeEq p f hf hr, ?_, ?_⟩
  · intro x
    rfl
  · rfl

theorem complement_one_point_lch (Z : Type u) [TopologicalSpace Z]
    [CompactSpace Z] [T2Space Z] (p : Z) : LCH ({p}ᶜ : Set Z) := by
  exact open_subspace_lch
    ⟨locallyCompact_of_mathlib_locallyCompactSpace Z inferInstance, inferInstance⟩
    _ isClosed_singleton.isOpen_compl

theorem one_point_compactification_iff (X : Type u) [TopologicalSpace X] :
    HausdorffCompactification (@plusInclusion X) ↔ LCH X ∧ ¬CompactSpace X := by
  constructor
  · rintro ⟨he, hd, hc, ht⟩
    let := hc
    let := ht
    exact ⟨(one_point_converse OnePoint.infty plusInclusion he
      OnePoint.compl_infty.symm).1, (one_point_dense_iff X).mp hd⟩
  · rintro ⟨hX, hn⟩
    exact ⟨(one_point_open_embedding X).isEmbedding, (one_point_dense_iff X).mpr hn,
      (one_point_compact_hausdorff X hX).1, (one_point_compact_hausdorff X hX).2⟩

end D10Topology.Ch11
