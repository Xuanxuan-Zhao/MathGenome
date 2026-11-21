import Mathlib.LinearAlgebra.Quotient.Defs
import MathGenome.Internal.Specs.D05.M02.Subspace

/-!
Independent statements for K05.06.quotient (paper.tex:940–943).

`V ⧸ U` is the algebraic quotient by the canonical submodule `U`. The
representative relation is exactly the paper's `v - w ∈ U`; the coset is
identified as an actual subset of `V`. The operations and their laws refer to
the canonical quotient structures, with no quotient module structure assumed
as a hypothesis. No dimension, topology, or choice of complement is required.
-/

namespace Specs.D05.M06.Quotient

universe u v

/-- Type of the quotient-space construction, retaining the original field. -/
def quotientSpace_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → Submodule K V → Type v

/-- The construction is the canonical algebraic quotient. -/
def quotientSpace_value : quotientSpace_type.{u, v} :=
  fun _ V _ _ _ U => V ⧸ U

/-- The relation displayed in the paper is an equivalence relation. -/
def relation_equivalence : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    Equivalence (fun v w : V => v - w ∈ U)

/-- Mathlib's setoid, used to form the quotient, has exactly this relation. -/
def relation_bridge : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (v w : V),
    U.quotientRel v w ↔ v - w ∈ U

/-- Two representatives define the same quotient element exactly when their
 difference belongs to the original subspace. -/
def representative_eq_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (v w : V),
    (Submodule.Quotient.mk v : V ⧸ U) = Submodule.Quotient.mk w ↔ v - w ∈ U

/-- The equivalence class of `v`, as a subset, is precisely the coset `v + U`. -/
def class_eq_coset : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (v : V),
    {w : V | (Submodule.Quotient.mk w : V ⧸ U) = Submodule.Quotient.mk v} =
      {w : V | ∃ u : V, u ∈ U ∧ w = v + u}

/-- Addition preserves the equivalence relation in both arguments. -/
def addition_well_defined : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (v v' w w' : V),
    v' - v ∈ U → w' - w ∈ U → (v' + w') - (v + w) ∈ U

/-- Scalar multiplication preserves the equivalence relation. -/
def smul_well_defined : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (a : K) (v v' : V),
    v' - v ∈ U → a • v' - a • v ∈ U

/-- The actual quotient operations have the paper's representative formulas. -/
def quotient_operations : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    (∀ v w : V,
      (Submodule.Quotient.mk v : V ⧸ U) + Submodule.Quotient.mk w =
        Submodule.Quotient.mk (v + w)) ∧
    (∀ (a : K) (v : V),
      a • (Submodule.Quotient.mk v : V ⧸ U) = Submodule.Quotient.mk (a • v))

/-- The quotient has an abelian group and a vector-space structure. The four
 scalar laws also explicitly concern the canonical quotient operations. -/
def quotient_vector_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    Nonempty (AddCommGroup (V ⧸ U)) ∧ Nonempty (Module K (V ⧸ U)) ∧
    (∀ (a : K) (x y : V ⧸ U), a • (x + y) = a • x + a • y) ∧
    (∀ (a b : K) (x : V ⧸ U), (a + b) • x = a • x + b • x) ∧
    (∀ (a b : K) (x : V ⧸ U), (a * b) • x = a • (b • x)) ∧
    (∀ x : V ⧸ U, (1 : K) • x = x)

/-- The zero quotient element is the class of zero and its coset is `U`. -/
def zero_coset : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    (Submodule.Quotient.mk (0 : V) : V ⧸ U) = 0 ∧
    {v : V | (Submodule.Quotient.mk v : V ⧸ U) = 0} = (U : Set V)

/-- The inverse of the class of `v` is the class of `-v`. -/
def neg_coset : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (v : V),
    -(Submodule.Quotient.mk v : V ⧸ U) = Submodule.Quotient.mk (-v)

/-- All quotient elements are represented by vectors of the original space. -/
def every_class_representative : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (x : V ⧸ U),
    ∃ v : V, Submodule.Quotient.mk v = x

end Specs.D05.M06.Quotient
