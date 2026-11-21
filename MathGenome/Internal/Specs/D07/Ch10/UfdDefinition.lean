import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Field.Basic

/-!
Independent statements for K07.10.ufd_definition (paper.tex:1978–1984).
The ambient ring is always a commutative nontrivial domain. We use the
canonical `UniqueFactorizationMonoid` together with these ring hypotheses.

`Multiset.Rel Associated s t` means that, after reordering, the factors
can be paired as associates; repetitions are retained. Association of the
products allows a leading unit. The first characterization additionally
gives exact, nonempty products for nonzero nonunits. The second states the
equivalent leading-unit convention explicitly, including uniqueness.
No normalization or chosen ordering of factors is imposed.
-/

universe u

namespace Specs.D07.Ch10.UfdDefinition

/-- The UFD predicate is used only on commutative nontrivial domains. -/
def UfdType := ∀ (R : Type u) [CommRing R] [IsDomain R], Prop

/-- Canonical multiplicative predicate; the characterizations below supply
the bridge to the source's factorization definition. -/
def UfdValue : UfdType.{u} := fun R _ _ => UniqueFactorizationMonoid R

def UfdCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    UniqueFactorizationMonoid R ↔
      (∀ a : R, a ≠ 0 → ¬IsUnit a →
        ∃ s : Multiset R, s ≠ 0 ∧ (∀ p ∈ s, Irreducible p) ∧ s.prod = a) ∧
      (∀ s t : Multiset R, (∀ p ∈ s, Irreducible p) →
        (∀ p ∈ t, Irreducible p) → Associated s.prod t.prod →
        Multiset.Rel Associated s t)

def LeadingUnitCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    UniqueFactorizationMonoid R ↔
      (∀ a : R, a ≠ 0 → ∃ (v : Rˣ) (s : Multiset R),
        (∀ p ∈ s, Irreducible p) ∧ a = (v : R) * s.prod) ∧
      (∀ (v w : Rˣ) (s t : Multiset R), (∀ p ∈ s, Irreducible p) →
        (∀ p ∈ t, Irreducible p) →
        (v : R) * s.prod = (w : R) * t.prod → Multiset.Rel Associated s t)

/-- Any fixed choice of associate representatives can be used as the factors.
The unit absorbs the changes in representatives. -/
def ChosenRepresentatives : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (rep : R → R), (∀ p : R, Irreducible p → Associated p (rep p)) →
    ∀ a : R, a ≠ 0 → ∃ (v : Rˣ) (s : Multiset R),
      (∀ p ∈ s, Irreducible p) ∧
      (∀ p ∈ s.map rep, Irreducible p) ∧ a = (v : R) * (s.map rep).prod

/-- Zero cannot be a unit times a finite product of irreducibles,
including an empty product. No UFD hypothesis is needed. -/
def ZeroBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    ¬∃ (v : Rˣ) (s : Multiset R),
      (∀ p ∈ s, Irreducible p) ∧ (0 : R) = (v : R) * s.prod

/-- Units admit empty factorizations, and every irreducible factorization
of a unit is empty. No UFD hypothesis is needed. -/
def UnitBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    (∀ a : R, IsUnit a ↔ ∃ v : Rˣ, a = (v : R) * (0 : Multiset R).prod) ∧
    (∀ (a : R) (v : Rˣ) (s : Multiset R), (∀ p ∈ s, Irreducible p) →
      a = (v : R) * s.prod → (IsUnit a ↔ s = 0))

def FieldIsUfd : Prop :=
  ∀ (F : Type u) [Field F], UniqueFactorizationMonoid F

end Specs.D07.Ch10.UfdDefinition
