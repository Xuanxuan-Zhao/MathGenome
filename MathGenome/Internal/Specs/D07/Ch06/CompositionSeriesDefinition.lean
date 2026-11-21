import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic
import Mathlib.Basic.Finite.Defs

/-!
Independent specification of `K07.06.composition_series_definition`,
paper.tex:1130–1135. The chapter assumes finite groups. The underlying
finite-chain definition also makes sense without that assumption.

`Series` has exactly the data in the definition: `length + 1` subgroups,
endpoints bottom and top, strict increase, normality in the NEXT subgroup,
and simplicity of each adjacent quotient. There is no ambient-normality
field. `IsSimpleGroup` includes nontriviality as well as the assertion that
all normal subgroups are bottom or top.

The quotients are of the next subgroup by the preceding subgroup restricted
into it, using Mathlib's canonical coset quotient. `factorListValue` keeps
one entry for each index, including repeated factors; it does not take an
image as a set or remove duplicates. Existence for all finite groups and
Jordan–Hölder uniqueness are separate obligations at the next source entry.
-/

namespace Specs.D07.Ch06.CompositionSeriesDefinition

universe u

/-- Canonical shared representation of a composition series. -/
structure Series (G : Type u) [Group G] where
  length : ℕ
  term : Fin (length + 1) → Subgroup G
  first_eq_bot : term 0 = ⊥
  last_eq_top : term (Fin.last length) = ⊤
  strictMono : StrictMono term
  normal : ∀ i : Fin length, ((term i.castSucc).subgroupOf (term i.succ)).Normal
  simple : ∀ i : Fin length,
    letI := normal i
    IsSimpleGroup ((term i.succ) ⧸ (term i.castSucc).subgroupOf (term i.succ))

def SeriesType : Type (u + 1) := (G : Type u) → [Group G] → Type u

def seriesValue : SeriesType.{u} := Series

/-- A raw chain satisfies precisely the source conditions. The existential
normality witness supplies the group structure on the quotient. -/
def chainPredicateValue {G : Type u} [Group G] (r : ℕ)
    (term : Fin (r + 1) → Subgroup G) : Prop :=
  term 0 = ⊥ ∧ term (Fin.last r) = ⊤ ∧ StrictMono term ∧
    ∀ i : Fin r, ∃ hn : ((term i.castSucc).subgroupOf (term i.succ)).Normal,
      letI := hn
      IsSimpleGroup ((term i.succ) ⧸ (term i.castSucc).subgroupOf (term i.succ))

def ChainPredicateType : Type (u + 1) :=
  {G : Type u} → [Group G] → (r : ℕ) → (Fin (r + 1) → Subgroup G) → Prop

/-- The `i`th composition factor, with its canonical quotient type. -/
def factorValue {G : Type u} [Group G] (s : Series G) (i : Fin s.length) : Type u :=
  (s.term i.succ) ⧸ (s.term i.castSucc).subgroupOf (s.term i.succ)

instance factorGroup {G : Type u} [Group G] (s : Series G) (i : Fin s.length) :
    Group (factorValue s i) :=
  letI := s.normal i
  inferInstanceAs (Group ((s.term i.succ) ⧸ (s.term i.castSucc).subgroupOf (s.term i.succ)))

def FactorType : Type (u + 1) :=
  {G : Type u} → [Group G] → (s : Series G) → Fin s.length → Type u

/-- A list, rather than a set, retains multiplicity. -/
def factorListValue {G : Type u} [Group G] (s : Series G) : List (Type u) :=
  List.ofFn (factorValue s)

def FactorListType : Type (u + 1) :=
  {G : Type u} → [Group G] → Series G → List (Type u)

/-- Every raw chain satisfying the stated conditions gives a series, and
these are all series with that length and those terms. -/
def ChainCharacterization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (r : ℕ)
    (term : Fin (r + 1) → Subgroup G),
    chainPredicateValue r term ↔
      ∃ s : Series G, ∃ h : s.length = r,
        ∀ i : Fin (s.length + 1), s.term i = term (Fin.cast (congrArg (· + 1) h) i)

def SeriesConditions : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s : Series G),
    chainPredicateValue s.length s.term

def AdjacentStrict : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s : Series G) (i : Fin s.length),
    s.term i.castSucc < s.term i.succ

def AdjacentNormal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s : Series G) (i : Fin s.length),
    ((s.term i.castSucc).subgroupOf (s.term i.succ)).Normal

def FactorSimple : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s : Series G) (i : Fin s.length),
    IsSimpleGroup (factorValue s i)

/-- The list has exactly one factor per strict step. -/
def FactorListLength : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s : Series G),
    (factorListValue s).length = s.length

/-- Every list entry is the corresponding quotient; no entry is discarded. -/
def FactorListEntry : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s : Series G) (i : Fin s.length),
    (factorListValue s)[i.val]'(by simp [factorListValue]) = factorValue s i

def TrivialSeries : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Subsingleton G],
    ∃ s : Series G, s.length = 0 ∧ factorListValue s = []

def ZeroLengthIffTrivial : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s : Series G),
    s.length = 0 ↔ Subsingleton G

end Specs.D07.Ch06.CompositionSeriesDefinition
