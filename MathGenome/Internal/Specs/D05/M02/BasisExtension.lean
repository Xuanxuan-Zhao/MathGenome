import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M02.Exchange
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Independent statements for K05.02.basis_extension (paper.tex:491–499).

Finite lists are indexed by `Fin s`; selecting a `Finset` of positions retains
occurrences even when vector values repeat. Extension retains every original
index on the left of a sum type and selects additional occurrences from the
given spanning list on the right. Its basis index is a finite subtype, so this
is an actual finite basis. No finite-dimensional instance is assumed: finite
generation is supplied by the spanning list. The last statement is the separate
unrestricted, choice-based extension paragraph, formulated for independent sets.
-/

namespace Specs.D05.M02.BasisExtension

/-- A finite spanning list contains a basis consisting of selected occurrences. -/
def finite_spanning_contains_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (s : ℕ) (w : Fin s → V),
    Submodule.span K (Set.range w) = ⊤ →
      ∃ (t : Finset (Fin s)) (b : Module.Basis t K V), ∀ j, b j = w j

/-- An independent family in a space with `s` generators has finite index type
and at most `s` occurrences. The family is not assumed finite in advance. -/
def independent_family_finite : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (s : ℕ) (w : Fin s → V) (v : I → V),
    Submodule.span K (Set.range w) = ⊤ → LinearIndependent K v →
      Finite I ∧ Nat.card I ≤ s

/-- Extend an arbitrary independent indexed family using only occurrences from
the finite spanning list. All original indices occur in the finite basis. -/
def finite_basis_extension : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (s : ℕ) (w : Fin s → V) (v : I → V),
    Submodule.span K (Set.range w) = ⊤ → LinearIndependent K v →
      ∃ t : Finset (I ⊕ Fin s),
        (∀ i, Sum.inl i ∈ t) ∧
        ∃ b : Module.Basis t K V, ∀ j, b j = Sum.elim v w j

/-- With Zorn's lemma (classical choice in Lean), every independent subset of
an unrestricted vector space is contained in a basis. -/
def unrestricted_basis_extension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V), LinearIndependent K (fun x : S => (x : V)) →
      ∃ T : Set V, S ⊆ T ∧
        ∃ b : Module.Basis T K V, ∀ x, b x = (x : V)

end Specs.D05.M02.BasisExtension
