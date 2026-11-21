import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real

/-!
Independent statements for paper.tex, d10:15:closure-sums. All index types
and underlying spaces may be empty. Local finiteness retains indexed
multiplicity. The function hypothesis concerns the closed supports, explicitly
written as closures of nonzero sets. No separation axiom on X is imposed.

The canonical pointwise sum uses `finsum`. The obligations below establish
finite nonzero sets at every point and a fixed finite sum on an open
neighborhood, so its fallback value for infinite support is never used under
the source hypothesis.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch15.ClosureSums

open Specs.D10Topology.Ch15.LocallyFiniteConventions

noncomputable def pointwiseSum {X : Type u} {I : Type v}
    (f : I → X → ℝ) : X → ℝ := fun x => ∑ᶠ i, f i x

def pointwiseSumType : Type (max u v + 1) :=
  {X : Type u} → {I : Type v} → (I → X → ℝ) → X → ℝ

noncomputable def pointwiseSumValue : pointwiseSumType.{u,v} :=
  fun f x => ∑ᶠ i, f i x

def locallyFinite_closures : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyFiniteFamily A → LocallyFiniteFamily (fun i => closure (A i))

def closure_iUnion : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyFiniteFamily A → closure (⋃ i, A i) = ⋃ i, closure (A i)

def locallyFinite_closed_iUnion : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyFiniteFamily A → (∀ i, IsClosed (A i)) → IsClosed (⋃ i, A i)

def pointwiseSum_finite_nonzero : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (f : I → X → ℝ),
    LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0}) →
    ∀ x, {i | f i x ≠ 0}.Finite

/-- Independence of the chosen finite collection of potentially nonzero terms. -/
def pointwiseSum_eq_sum : Prop :=
  ∀ {X : Type u} {I : Type v} (f : I → X → ℝ) (x : X) (s : Finset I),
    (∀ i, i ∉ s → f i x = 0) → pointwiseSum f x = ∑ i ∈ s, f i x

def pointwiseSum_locally_eq_sum : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (f : I → X → ℝ),
    LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0}) →
    ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ s : Finset I,
      ∀ y ∈ U, (∀ i, i ∉ s → f i y = 0) ∧
        pointwiseSum f y = ∑ i ∈ s, f i y

def pointwiseSum_continuous : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (f : I → X → ℝ),
    (∀ i, Continuous (f i)) →
    LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0}) →
    Continuous (pointwiseSum f)

end Specs.D10Topology.Ch15.ClosureSums
