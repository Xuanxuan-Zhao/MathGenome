import MathGenome.Internal.Specs.D05.M02.SumIntersection
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Pi

/-!
Independent statements for K05.06.direct_sum (paper.tex:965–966).
The finite index type retains repeated summands as distinct occurrences. A
component is an element of the actual subspace, not an arbitrary coordinate.
No finite-dimensional assumption is made on the ambient space or summands.
The comparison with Mathlib's finitely supported direct sum uses its actual
linear equivalence with tuples; no decomposition is assumed in that comparison.
-/

namespace Specs.D05.M06.DirectSum

universe u v w

/-- The paper's unique-expression definition of an internal direct sum. -/
def UniqueDecomposition {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (U : ι → Submodule K V) : Prop :=
  ∀ x : V, ∃! c : ∀ i, U i, (∑ i, (c i : V)) = x

/-- The linear map that adds the included components. -/
noncomputable def summationMap {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (U : ι → Submodule K V) :
    (∀ i, U i) →ₗ[K] V where
  toFun c := ∑ i, (c i : V)
  map_add' c d := by simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum,
    RingHom.id_apply]

def internalDirectSum_type : Type (max (u+1) (v+1) (w+1)) :=
  (K : Type u) → (V : Type v) → (ι : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [Fintype ι] → (ι → Submodule K V) → Prop

def internalDirectSum_value : internalDirectSum_type.{u,v,w} :=
  fun _ _ _ _ _ _ _ U => UniqueDecomposition U

def summation_type : Type (max (u+1) (v+1) (w+1)) :=
  (K : Type u) → (V : Type v) → (ι : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [Fintype ι] →
    (U : ι → Submodule K V) → ((∀ i, U i) →ₗ[K] V)

noncomputable def summation_value : summation_type.{u,v,w} :=
  fun _ _ _ _ _ _ _ U => summationMap U

/-- Existence and uniqueness of expressions is bijectivity of the addition map. -/
def internal_iff_bijective : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V),
    UniqueDecomposition U ↔ Function.Bijective (summationMap U)

/-- The image of addition is the subspace sum, without any directness hypothesis. -/
def range_summation : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V), LinearMap.range (summationMap U) = ⨆ i, U i

/-- Uniqueness reduces to the zero sum by subtraction. -/
def zero_sum_iff_injective : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V),
    (∀ c : ∀ i, U i, (∑ i, (c i : V)) = 0 → ∀ i, (c i : V) = 0) ↔
      Function.Injective (summationMap U)

/-- The spanning condition and zero-sum condition are together equivalent to
unique expression. The supremum denotes the canonical subspace sum. -/
def internal_iff_spanning_zero_sum : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V),
    UniqueDecomposition U ↔ (⨆ i, U i) = ⊤ ∧
      ∀ c : ∀ i, U i, (∑ i, (c i : V)) = 0 → ∀ i, (c i : V) = 0

/-- Finite tuples and finitely supported tuples compare by an actual map, and
the two addition maps agree under that map. -/
def finite_sum_comparison : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (U : ι → Submodule K V)
    (c : _root_.DirectSum ι (fun i => U i)),
    _root_.DirectSum.coeLinearMap U c =
      summationMap U (_root_.DirectSum.linearEquivFunOnFintype K ι (fun i => U i) c)

/-- Bridge from the unique-expression convention to the canonical predicate. -/
def internal_iff_mathlib : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (U : ι → Submodule K V),
    UniqueDecomposition U ↔ _root_.DirectSum.IsInternal U

/-- An internal decomposition gives a linear isomorphism with precisely the
summation values, rather than merely an unrelated abstract isomorphism. -/
def summation_equiv : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V), UniqueDecomposition U →
      ∃ e : (∀ i, U i) ≃ₗ[K] V, ∀ c, e c = ∑ i, (c i : V)

/-- The binary zero-sum condition is exactly trivial intersection. -/
def pair_zero_sum_iff_inf_bot : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    (∀ (u : U) (w : W), (u : V) + (w : V) = 0 →
      (u : V) = 0 ∧ (w : V) = 0) ↔ U ⊓ W = ⊥

/-- The two indexed summands, with `false` first and `true` second, form an
internal direct sum exactly when they sum to the ambient space and intersect
trivially. The sum set reuses the upstream paper convention. -/
def pair_internal_iff_sum_intersection : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    UniqueDecomposition (fun b : Bool => if b then W else U) ↔
      Specs.D05.M02.SumIntersection.sumSet U W = Set.univ ∧ U ⊓ W = ⊥

/-- In particular the standard supremum/intersection criterion has no hidden
dimension assumptions. -/
def pair_internal_iff_sup_inf : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    UniqueDecomposition (fun b : Bool => if b then W else U) ↔
      U ⊔ W = ⊤ ∧ U ⊓ W = ⊥

/-- With no summands, every vector must be zero. This also covers `Fin 0`. -/
def empty_internal_iff_zero : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [IsEmpty ι] (U : ι → Submodule K V),
    UniqueDecomposition U ↔ ∀ x : V, x = 0

end Specs.D05.M06.DirectSum
