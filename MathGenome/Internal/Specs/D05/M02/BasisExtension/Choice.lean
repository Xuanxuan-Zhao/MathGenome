import MathGenome.Internal.Specs.D05.M02.Basis
import Mathlib.Order.Preorder.Chain

/-!
Independent statements for K05.02.basis_extension, paper.tex:498.

This is the unrestricted, choice-based extension theorem. Independence of a
subset means independence of its inclusion family; thus the given vectors are
retained as actual vectors. The field, vector space, and subset may be infinite.
The empty subset and zero vector space are included. `Module.Basis` has finitely
supported coordinates, as in the upstream basis specification.

Zorn's lemma is the declared choice principle used in the implementation, not
an assumed basis or maximality certificate in the extension statement.
-/

namespace Specs.D05.M02.BasisExtension.Choice

/-- Finite relations in a chain union already lie in one member of the chain. -/
def independent_chain_union : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (C : Set (Set V)), IsChain (· ⊆ ·) C →
    (∀ S ∈ C, LinearIndependent K (fun x : S => (x : V))) →
    LinearIndependent K (fun x : ⋃₀ C => (x : V))

/-- A vector outside the old span can be adjoined without losing independence. -/
def independent_insert_of_not_mem_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V) (x : V),
    LinearIndependent K (fun s : S => (s : V)) →
    x ∉ Submodule.span K S →
    LinearIndependent K (fun s : (insert x S : Set V) => (s : V))

/-- Zorn's lemma gives a maximal independent subset containing the prescribed one. -/
def exists_maximal_independent_superset : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V), LinearIndependent K (fun s : S => (s : V)) →
    ∃ T : Set V, S ⊆ T ∧ LinearIndependent K (fun t : T => (t : V)) ∧
      ∀ U : Set V, T ⊆ U →
        LinearIndependent K (fun u : U => (u : V)) → U = T

/-- Maximal independence forces spanning, without a dimension bound. -/
def maximal_independent_spans : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Set V), LinearIndependent K (fun t : T => (t : V)) →
    (∀ U : Set V, T ⊆ U →
      LinearIndependent K (fun u : U => (u : V)) → U = T) →
    Submodule.span K T = ⊤

/-- Every independent subset extends to a basis of the whole vector space.
The basis vectors are exactly the elements of the extension subset, with the
inclusion as the basis map, rather than unrelated coordinates on that subset. -/
def basis_extension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V), LinearIndependent K (fun s : S => (s : V)) →
    ∃ T : Set V, S ⊆ T ∧
      ∃ b : Module.Basis T K V, ∀ t : T, b t = (t : V)

end Specs.D05.M02.BasisExtension.Choice
