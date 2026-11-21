import MathGenome.Internal.Specs.D05.M02.SpanProperties

/-!
Independent statements for K05.02.sum_intersection (paper.tex:511–512).
The sum is the actual set of two-term sums, not a set union. The bridge to
the canonical lattice supremum is a theorem obligation. Intersections are
arbitrary, including empty families; the ambient space need not be finite
dimensional. The coordinate example uses `K × K` as the coordinate plane.
-/

namespace Specs.D05.M02.SumIntersection

/-- The set displayed as `U + W` in the paper. -/
def sumSet {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V) : Set V :=
  {x | ∃ u ∈ U, ∃ w ∈ W, u + w = x}

def intersection_subspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    ∃ I : Submodule K V, (I : Set V) = (U : Set V) ∩ (W : Set V)

def intersection_closed : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    (0 : V) ∈ (U : Set V) ∩ (W : Set V) ∧
      (∀ x y : V, x ∈ (U : Set V) ∩ (W : Set V) →
        y ∈ (U : Set V) ∩ (W : Set V) →
        x + y ∈ (U : Set V) ∩ (W : Set V)) ∧
      (∀ (a : K) (x : V), x ∈ (U : Set V) ∩ (W : Set V) →
        a • x ∈ (U : Set V) ∩ (W : Set V))

/-- In particular, the displayed sum set has a subspace structure. -/
def sum_eq_sup : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V), (↑(U ⊔ W) : Set V) = sumSet U W

def sum_closed : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    (0 : V) ∈ sumSet U W ∧
      (∀ x y : V, x ∈ sumSet U W → y ∈ sumSet U W → x + y ∈ sumSet U W) ∧
      (∀ (a : K) (x : V), x ∈ sumSet U W → a • x ∈ sumSet U W)

def union_subset_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V), (U : Set V) ∪ (W : Set V) ⊆ sumSet U W

def sum_le_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W T : Submodule K V),
    sumSet U W ⊆ (T : Set V) ↔ (U : Set V) ∪ (W : Set V) ⊆ (T : Set V)

def sum_eq_span_union : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    sumSet U W = (Submodule.span K ((U : Set V) ∪ (W : Set V)) : Set V)

def iInter_subspace : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V),
    ∃ I : Submodule K V, (I : Set V) = ⋂ i, (U i : Set V)

/-- The arbitrary collection formulation also includes the empty collection. -/
def sInter_subspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (C : Set (Submodule K V)),
    ∃ I : Submodule K V, (I : Set V) = ⋂₀ ((fun U : Submodule K V => (U : Set V)) '' C)

/-- The coordinate axes contain the two unit vectors, but their union excludes
their sum and cannot be the carrier of any subspace, over every field. -/
def coordinate_lines_counterexample : Prop :=
  ∀ (K : Type*) [Field K], ∃ U W : Submodule K (K × K),
    (U : Set (K × K)) = {x | x.2 = 0} ∧
    (W : Set (K × K)) = {x | x.1 = 0} ∧
    (1, 0) ∈ U ∧ (0, 1) ∈ W ∧
    ((1, 0) + (0, 1) : K × K) ∉ (U : Set (K × K)) ∪ (W : Set (K × K)) ∧
    ¬ ∃ S : Submodule K (K × K), (S : Set (K × K)) = (U : Set (K × K)) ∪ (W : Set (K × K))

end Specs.D05.M02.SumIntersection
