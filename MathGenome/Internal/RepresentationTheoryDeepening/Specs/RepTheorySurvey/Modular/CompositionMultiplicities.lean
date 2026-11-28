import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace RepTheorySurvey.Modular.CompositionMultiplicity

universe w

open scoped BigOperators

abbrev GroupAlgebra (F G : Type*) [Field F] [Group G] := MonoidAlgebra F G

variable (F G : Type*) [Field F] [Group G]

/-- Finite dimension for the canonical restriction of a group-algebra action
along the coefficient map. -/
abbrev GroundFinite (M : Type*) [AddCommGroup M] [Module (GroupAlgebra F G) M] : Prop :=
  @Module.Finite F M _ _ (Module.compHom M (algebraMap F (GroupAlgebra F G)))

variable {F G}
local notation "A" => GroupAlgebra F G

/-- The subquotient for an interval of submodules. -/
abbrev Subquotient {M : Type*} [AddCommGroup M] [Module A M] (L U : Submodule A M) :=
  U ⧸ L.comap U.subtype

/-- A bottom-to-top composition series of group-algebra submodules. -/
abbrev CompleteSeries (M : Type*) [AddCommGroup M] [Module A M] :=
  {s : CompositionSeries (Submodule A M) // s.head = ⊥ ∧ s.last = ⊤}

/-- The successive subquotient at the indicated step of a series. -/
abbrev Factor {M : Type*} [AddCommGroup M] [Module A M]
    (s : CompositionSeries (Submodule A M)) (j : Fin s.length) :=
  Subquotient (s j.castSucc) (s j.succ)

/-- Isomorphism of left group-algebra modules. -/
abbrev Isomorphic (M N : Type*) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] : Prop :=
  Nonempty (M ≃ₗ[A] N)

/-- A normalized invariant satisfying the short exact sequence relation; its values may
be character functions, or any other additive commutative monoid. -/
structure AdditiveCharacter (F G : Type*) [Field F] [Group G]
    (C : Type*) [AddCommMonoid C] where
  value (M : Type w) [AddCommGroup M] [Module (GroupAlgebra F G) M]
    [GroundFinite F G M] : C
  zero (M : Type w) [AddCommGroup M] [Module (GroupAlgebra F G) M]
    [GroundFinite F G M] [Subsingleton M] : value M = 0
  exact {L M N : Type w} [AddCommGroup L] [Module (GroupAlgebra F G) L] [GroundFinite F G L]
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [GroundFinite F G M]
    [AddCommGroup N] [Module (GroupAlgebra F G) N] [GroundFinite F G N]
    (f : L →ₗ[GroupAlgebra F G] M) (g : M →ₗ[GroupAlgebra F G] N) :
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    value M = value L + value N

/-- A complete family of pairwise nonisomorphic simple modules. -/
structure SimpleRepresentatives {ι : Type*} (S : ι → Type w)
    [∀ i, AddCommGroup (S i)] [∀ i, Module A (S i)] : Prop where
  simple (i : ι) : IsSimpleModule A (S i)
  distinct {i j : ι} : Isomorphic (F := F) (G := G) (S i) (S j) → i = j
  complete (T : Type w) [AddCommGroup T] [Module A T] :
    IsSimpleModule A T → ∃ i, Isomorphic (F := F) (G := G) T (S i)

namespace Spec

variable (F G) in
noncomputable def factorCount {M : Type*} [AddCommGroup M] [Module A M]
    (s : CompositionSeries (Submodule A M)) (S : Type*)
    [AddCommGroup S] [Module (GroupAlgebra F G) S] : ℕ := by
  classical
  exact ∑ j : Fin s.length, if Isomorphic (F := F) (G := G) (Factor s j) S then 1 else 0

variable (F G) in
/-- The least realized count. All complete series realize the same count in finite
dimension, including the empty list of factors for the zero module. -/
noncomputable def multiplicity (M S : Type*) [AddCommGroup M] [Module A M]
    [AddCommGroup S] [Module A S] : ℕ :=
  sInf {n | ∃ s : CompleteSeries (F := F) (G := G) M, factorCount F G s.1 S = n}

set_option linter.checkUnivs false in
def FactorCountType :=
  ∀ (F G : Type*) [Field F] [Group G] {M : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M]
    (_s : CompositionSeries (Submodule (GroupAlgebra F G) M))
    (S : Type*) [AddCommGroup S] [Module (GroupAlgebra F G) S], ℕ

set_option linter.checkUnivs false in
def MultiplicityType :=
  ∀ (F G : Type*) [Field F] [Group G]
    (M S : Type*) [AddCommGroup M] [Module (GroupAlgebra F G) M]
    [AddCommGroup S] [Module (GroupAlgebra F G) S], ℕ

def ExistsCompleteSeries : Prop :=
  ∀ {F G : Type*} [Field F] [Group G]
    (M : Type*) [AddCommGroup M] [Module (GroupAlgebra F G) M] [GroundFinite F G M],
    Nonempty (CompleteSeries (F := F) (G := G) M)

def FactorSimple : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M]
    (s : CompositionSeries (Submodule (GroupAlgebra F G) M)) (j : Fin s.length),
    IsSimpleModule (GroupAlgebra F G) (Factor s j)

def MultiplicityEqCount : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M S : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [AddCommGroup S] [Module (GroupAlgebra F G) S]
    (s : CompleteSeries (F := F) (G := G) M),
    multiplicity F G M S = factorCount F G s.1 S

def MultiplicityCongr : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M N S T : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [AddCommGroup N] [Module (GroupAlgebra F G) N]
    [AddCommGroup S] [Module (GroupAlgebra F G) S] [AddCommGroup T] [Module (GroupAlgebra F G) T]
    [GroundFinite F G M],
    (M ≃ₗ[GroupAlgebra F G] N) → (S ≃ₗ[GroupAlgebra F G] T) →
      multiplicity F G M S = multiplicity F G N T

def MultiplicityExact : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M N L S : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [AddCommGroup N] [Module (GroupAlgebra F G) N]
    [AddCommGroup L] [Module (GroupAlgebra F G) L] [AddCommGroup S] [Module (GroupAlgebra F G) S]
    [GroundFinite F G L] [GroundFinite F G N]
    (f : L →ₗ[GroupAlgebra F G] M) (g : M →ₗ[GroupAlgebra F G] N),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
      multiplicity F G M S = multiplicity F G L S + multiplicity F G N S

def MultiplicityZero : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M S : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [AddCommGroup S] [Module (GroupAlgebra F G) S]
    [Subsingleton M],
    multiplicity F G M S = 0

def MultiplicityPosIff : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M S : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [AddCommGroup S] [Module (GroupAlgebra F G) S]
    (s : CompleteSeries (F := F) (G := G) M),
    0 < multiplicity F G M S ↔
      ∃ j : Fin s.1.length, Isomorphic (F := F) (G := G) (Factor s.1 j) S

def MultiplicityOfSimple : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M S : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [AddCommGroup S] [Module (GroupAlgebra F G) S]
    [IsSimpleModule (GroupAlgebra F G) M],
    (Isomorphic (F := F) (G := G) M S → multiplicity F G M S = 1) ∧
    (¬ Isomorphic (F := F) (G := G) M S → multiplicity F G M S = 0)

def GroundFiniteIff : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {M : Type*}
    [AddCommGroup M] [Module (GroupAlgebra F G) M] [Module F M]
    [IsScalarTower F (GroupAlgebra F G) M],
    GroundFinite F G M ↔ Module.Finite F M

def GroundFiniteOfSimple : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {S : Type*}
    [AddCommGroup S] [Module (GroupAlgebra F G) S] [Finite G]
    [IsSimpleModule (GroupAlgebra F G) S],
    GroundFinite F G S

universe u v

def ExistsSimpleRepresentatives : Prop :=
  ∀ {F : Type u} {G : Type v} [Field F] [Group G] [Finite G],
    ∃ (ι : Type) (_ : Fintype ι) (S : ι → Type (max u v)) (add : ∀ i, AddCommGroup (S i)),
      let _ := add
      ∃ mod : ∀ i, Module (GroupAlgebra F G) (S i),
        @SimpleRepresentatives F G _ _ ι S add mod

def CharacterEqSum : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] {C : Type*} [AddCommMonoid C]
    (χ : AdditiveCharacter.{w} F G C) {ι : Type*} [Fintype ι]
    (V : Type w) [AddCommGroup V] [Module (GroupAlgebra F G) V] [GroundFinite F G V]
    (S : ι → Type w) [∀ i, AddCommGroup (S i)] [∀ i, Module (GroupAlgebra F G) (S i)]
    [∀ i, GroundFinite F G (S i)],
    SimpleRepresentatives (F := F) (G := G) S →
      χ.value V = ∑ i, multiplicity F G V (S i) • χ.value (S i)

end Spec

end RepTheorySurvey.Modular.CompositionMultiplicity
