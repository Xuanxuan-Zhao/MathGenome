import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.ClosureSums
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.LocallyFinitePasting

/-!
Closure and sum constructions for paper.tex, d10:15:closure-sums.
The support in the hypotheses is the closure of the nonzero set. Its local
finiteness implies local finiteness of the nonzero sets, allowing the finite
sum construction without countability or summability assumptions.
-/

open Set
open scoped Topology
universe u v

namespace D10Topology.Ch15

noncomputable abbrev pointwiseSum {X : Type u} {I : Type v}
    (f : I → X → ℝ) : X → ℝ :=
  Specs.D10Topology.Ch15.ClosureSums.pointwiseSum f

variable {X : Type u} {I : Type v} [TopologicalSpace X]

theorem locallyFinite_closures (A : I → Set X) (h : LocallyFiniteFamily A) :
    LocallyFiniteFamily (fun i => closure (A i)) :=
  h.closure

theorem closure_iUnion (A : I → Set X) (h : LocallyFiniteFamily A) :
    closure (⋃ i, A i) = ⋃ i, closure (A i) :=
  h.closure_iUnion

theorem locallyFinite_closed_iUnion (A : I → Set X) (h : LocallyFiniteFamily A)
    (hA : ∀ i, IsClosed (A i)) : IsClosed (⋃ i, A i) :=
  Ch02.locallyFinite_iUnion_isClosed A h hA

/-- Passing from closed supports to algebraic nonzero supports adds no hypothesis. -/
theorem locallyFinite_nonzero (f : I → X → ℝ)
    (h : LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0})) :
    LocallyFinite (fun i => Function.support (f i)) :=
  h.subset (fun _ => subset_closure)

theorem pointwiseSum_finite_nonzero (f : I → X → ℝ)
    (h : LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0})) :
    ∀ x, {i | f i x ≠ 0}.Finite :=
  (locallyFinite_nonzero f h).point_finite

omit [TopologicalSpace X] in
theorem pointwiseSum_eq_sum (f : I → X → ℝ) (x : X) (s : Finset I)
    (hs : ∀ i, i ∉ s → f i x = 0) :
    pointwiseSum f x = ∑ i ∈ s, f i x := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  exact hi (hs i hn)

theorem pointwiseSum_locally_eq_sum (f : I → X → ℝ)
    (h : LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0})) :
    ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ s : Finset I,
      ∀ y ∈ U, (∀ i, i ∉ s → f i y = 0) ∧
        pointwiseSum f y = ∑ i ∈ s, f i y := by
  classical
  intro x
  obtain ⟨s, hs⟩ := (locallyFinite_nonzero f h).exists_finset_support x
  obtain ⟨U, hUsub, hUopen, hx⟩ := mem_nhds_iff.mp hs
  refine ⟨U, hUopen, hx, s, ?_⟩
  intro y hy
  have hzero : ∀ i, i ∉ s → f i y = 0 := by
    intro i hi
    by_contra hn
    exact hi (hUsub hy hn)
  exact ⟨hzero, pointwiseSum_eq_sum f y s hzero⟩

theorem pointwiseSum_continuous (f : I → X → ℝ)
    (hf : ∀ i, Continuous (f i))
    (h : LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0})) :
    Continuous (pointwiseSum f) :=
  continuous_finsum hf (locallyFinite_nonzero f h)

end D10Topology.Ch15
