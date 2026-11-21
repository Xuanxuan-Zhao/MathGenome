import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.AffinePatching
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.PartitionConventions

open Set
open scoped Topology
universe u v w

namespace D10Topology.Ch15

abbrev AffineStable {E : Type w} [AddCommGroup E] [Module ℝ E] (A : Set E) : Prop :=
  Specs.D10Topology.Ch15.AffinePatching.AffineStable A

noncomputable abbrev weightedExtension {X : Type u} {E : Type w}
    [AddCommGroup E] [Module ℝ E] (U : Set X) (φ : X → ℝ) (s : U → E) : X → E :=
  Specs.D10Topology.Ch15.AffinePatching.weightedExtension U φ s

noncomputable abbrev affinePatch {X : Type u} {I : Type v} {E : Type w}
    [AddCommGroup E] [Module ℝ E] (U : I → Set X)
    (φ : I → X → Icc (0 : ℝ) 1) (s : ∀ i, U i → E) : X → E :=
  Specs.D10Topology.Ch15.AffinePatching.affinePatch U φ s

variable {X : Type u} {I : Type v} {E : Type w} [AddCommGroup E] [Module ℝ E]

theorem weightedExtension_values (U : Set X) (φ : X → ℝ) (s : U → E) (x : X) :
    (∀ h : x ∈ U, weightedExtension U φ s x = φ x • s ⟨x, h⟩) ∧
    (x ∉ U → weightedExtension U φ s x = 0) ∧
    (φ x = 0 → weightedExtension U φ s x = 0) := by
  classical
  constructor
  · intro hx
    exact dite_eq_left hx
  constructor
  · intro hx
    exact dite_eq_right hx
  · intro hφ
    by_cases hx : x ∈ U
    · rw [show weightedExtension U φ s x = φ x • s ⟨x, hx⟩ from dite_eq_left hx,
        hφ, zero_smul]
    · exact dite_eq_right hx

theorem weightedExtension_support (U : Set X) (φ : X → ℝ) (s : U → E) :
    Function.support (weightedExtension U φ s) ⊆ Function.support φ := by
  intro x hx hφ
  exact hx ((weightedExtension_values U φ s x).2.2 hφ)

variable [TopologicalSpace X] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

theorem weightedExtension_continuous (U : Set X) (φ : X → ℝ) (s : U → E)
    (hU : IsOpen U) (hφ : Continuous φ) (hsub : closure {x | φ x ≠ 0} ⊆ U)
    (hs : Continuous s) : Continuous (weightedExtension U φ s) := by
  have hw : ContinuousOn (weightedExtension U φ s) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : U.domRestrict (weightedExtension U φ s) =
        (fun x : U => φ x • s x) := by
      funext x
      exact (weightedExtension_values U φ s x).1 x.property
    rw [heq]
    exact (hφ.comp continuous_subtype_val).smul hs
  exact continuous_of_tsupport fun x hx => hw.continuousAt
    (hU.mem_nhds (hsub (closure_mono (weightedExtension_support U φ s) hx)))

omit [TopologicalSpace X] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
theorem affinePatch_eq_sum (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1)
    (s : ∀ i, U i → E) (x : X) (t : Finset I)
    (ht : ∀ i, i ∉ t → (φ i x : ℝ) = 0) :
    affinePatch U φ s x =
      ∑ i ∈ t, weightedExtension (U i) (fun y => (φ i y : ℝ)) (s i) x := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  exact hi ((weightedExtension_values (U i) (fun y => (φ i y : ℝ)) (s i) x).2.2
    (ht i hn))

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem affinePatch_locally_sum (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1)
    (s : ∀ i, U i → E) (h : SubordinatePartitionOfUnity U φ) :
    ∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∃ t : Finset I,
      ∀ y ∈ N, (∀ i, i ∉ t → (φ i y : ℝ) = 0) ∧
        (∑ i ∈ t, (φ i y : ℝ)) = 1 ∧
        affinePatch U φ s y =
          ∑ i ∈ t, weightedExtension (U i) (fun z => (φ i z : ℝ)) (s i) y := by
  intro x
  obtain ⟨N, hN, hx, t, ht⟩ := partition_locally_sum U φ h x
  exact ⟨N, hN, hx, t, fun y hy =>
    ⟨(ht y hy).1, (ht y hy).2, affinePatch_eq_sum U φ s y t (ht y hy).1⟩⟩

omit [TopologicalSpace X] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
/-- Finite sums on arbitrary index types are finite affine combinations. -/
theorem AffineStable.sum_mem {A : Set E} (hA : AffineStable A)
    (t : Finset I) (c : I → ℝ) (z : I → E)
    (hc : (∑ i ∈ t, c i) = 1) (hz : ∀ i ∈ t, z i ∈ A) :
    (∑ i ∈ t, c i • z i) ∈ A := by
  classical
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  have hc' : (∑ j, c (e j)) = 1 :=
    (e.sum_comp (fun j : t => c j)).trans ((Finset.sum_coe_sort t c).trans hc)
  have h := hA (Fintype.card t) (fun j => c (e j)) (fun j => z (e j)) hc'
    (fun j => hz (e j) (e j).property)
  have heq : (∑ j, c (e j) • z (e j)) = ∑ i ∈ t, c i • z i :=
    (e.sum_comp (fun j : t => c j • z j)).trans
      (Finset.sum_coe_sort t (fun i => c i • z i))
  rwa [heq] at h

/-- Patching needs no ambient extension of any of the local solutions. -/
theorem affine_patching (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1)
    (s : ∀ i, U i → E) (S : X → Set E)
    (hU : ∀ i, IsOpen (U i)) (_hcover : (⋃ i, U i) = univ)
    (hφ : SubordinatePartitionOfUnity U φ) (hs : ∀ i, Continuous (s i))
    (hsol : ∀ i (x : U i), s i x ∈ S x.val)
    (hS : ∀ x, AffineStable (S x)) :
    Continuous (affinePatch U φ s) ∧ ∀ x, affinePatch U φ s x ∈ S x := by
  classical
  constructor
  · apply continuous_finsum
    · intro i
      exact weightedExtension_continuous (U i) (fun y => (φ i y : ℝ)) (s i)
        (hU i) (hφ.1 i).subtype_val (hφ.2.1 i) (hs i)
    · exact hφ.2.2.1.subset (fun i =>
        (weightedExtension_support (U i) (fun y => (φ i y : ℝ)) (s i)).trans
          subset_closure)
  · intro x
    have hf : {i | (φ i x : ℝ) ≠ 0}.Finite :=
      pointwiseSum_finite_nonzero (fun i y => (φ i y : ℝ)) hφ.2.2.1 x
    let t : Finset I := hf.toFinset
    have ht : ∀ i, i ∉ t → (φ i x : ℝ) = 0 := by
      intro i hi
      by_contra hn
      exact hi (hf.mem_toFinset.mpr hn)
    have hxU : ∀ i ∈ t, x ∈ U i := by
      intro i hi
      exact hφ.2.1 i (subset_closure (hf.mem_toFinset.mp hi))
    let z : I → E := fun i => if hi : x ∈ U i then s i ⟨x, hi⟩ else 0
    have hmem : (∑ i ∈ t, (φ i x : ℝ) • z i) ∈ S x := by
      apply (hS x).sum_mem t (fun i => (φ i x : ℝ)) z
        (partition_sum_finset U φ hφ x t ht)
      intro i hi
      simpa only [z, dite_eq_left (hxU i hi)] using hsol i ⟨x, hxU i hi⟩
    rw [affinePatch_eq_sum U φ s x t ht]
    convert hmem using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [(weightedExtension_values (U i) (fun y => (φ i y : ℝ)) (s i) x).1
      (hxU i hi)]
    simp only [z, dite_eq_left (hxU i hi)]

end D10Topology.Ch15
