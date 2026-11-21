import Mathlib.Algebra.Module.Submodule.LinearMap
import MathGenome.Internal.Specs.D05.M02.VectorSpace

/-!
Independent statements for K05.02.subspace (paper.tex:449–455).

A subspace is the canonical Mathlib `Submodule` over the named field. The
criterion starts with an arbitrary subset, rather than assuming it is already
a submodule. The remaining statements record why this representation gives a
vector space with inherited operations, and identify its linear inclusion with
the actual subtype inclusion. No finite-dimensional hypothesis is used.
-/

namespace Specs.D05.M02.Subspace

/-- A subset is the underlying set of a subspace exactly when it contains zero
and is closed under addition and scalar multiplication. -/
def subspace_iff_closed : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Set V),
    (∃ S : Submodule K V, (S : Set V) = U) ↔
      (0 : V) ∈ U ∧
      (∀ u v : V, u ∈ U → v ∈ U → u + v ∈ U) ∧
      (∀ (a : K) (u : V), u ∈ U → a • u ∈ U)

/-- Closure under scalar multiplication supplies additive inverses via `-1`. -/
def neg_mem_of_smul_closed : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Set V),
    (∀ (a : K) (u : V), u ∈ U → a • u ∈ U) →
      ∀ u : V, u ∈ U → -u ∈ U

/-- The subspace subtype has an abelian group and a module structure, and its
zero, sum, inverse and scalar action are inherited from the ambient space. -/
def inherited_vector_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (S : Submodule K V),
    Nonempty (AddCommGroup S) ∧ Nonempty (Module K S) ∧
      ((0 : S) : V) = 0 ∧
      (∀ u v : S, ((u + v : S) : V) = (u : V) + (v : V)) ∧
      (∀ u : S, ((-u : S) : V) = -(u : V)) ∧
      (∀ (a : K) (u : S), ((a • u : S) : V) = a • (u : V))

/-- The actual inclusion, with domain the subspace and codomain the ambient
space, is an injective linear map. Its values are fixed, not coordinates. -/
def linear_inclusion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (S : Submodule K V),
    ∃ i : S →ₗ[K] V, (∀ u : S, i u = (u : V)) ∧ Function.Injective i

end Specs.D05.M02.Subspace
