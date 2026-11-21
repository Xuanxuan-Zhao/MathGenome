import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07Category
import Mathlib.Topology.Baire.Lemmas

/-!
# Category terminology for Chapter 7

We use the canonical predicates `IsNowhereDense`, `IsMeagre`, and `BaireSpace`
throughout. These equivalences identify them with Definition `fa2:p1:c07:category`.
In particular, the meagre-set equivalence gives equality with a countable union,
and the Baire equivalence includes finite and empty countable families.
-/

open Set TopologicalSpace

universe u

namespace ExpandedFA.P1.C07Category

/-- The canonical nowhere-dense predicate of Definition `fa2:p1:c07:category`. -/
abbrev NowhereDense {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  IsNowhereDense A

/-- The canonical meagre predicate, with its exact-union meaning proved below. -/
abbrev Meagre {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  IsMeagre A

/-- The canonical Baire property, without any completeness hypothesis. -/
abbrev Baire (X : Type u) [TopologicalSpace X] : Prop := BaireSpace X

theorem isNowhereDense_iff_empty_interior_closure
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    IsNowhereDense A ↔ interior (closure A) = ∅ :=
  Iff.rfl

theorem isMeagre_iff_countable_union
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    IsMeagre A ↔ ∃ S : Set (Set X),
      S.Countable ∧ (∀ B ∈ S, interior (closure B) = ∅) ∧ A = ⋃₀ S := by
  constructor
  · intro h
    obtain ⟨S, hnd, hc, hEq⟩ := isMeagre_iff_eq_countable_union_isNowhereDense.mp h
    exact ⟨S, hc, hnd, hEq⟩
  · rintro ⟨S, hc, hnd, hEq⟩
    exact isMeagre_iff_eq_countable_union_isNowhereDense.mpr ⟨S, hnd, hc, hEq⟩

theorem baireSpace_iff_nat_intersection
    (X : Type u) [TopologicalSpace X] :
    BaireSpace X ↔ ∀ G : ℕ → Set X,
      (∀ n, IsOpen (G n)) → (∀ n, Dense (G n)) → Dense (⋂ n, G n) :=
  baireSpace_iff X

theorem baireSpace_iff_countable_intersection
    (X : Type u) [TopologicalSpace X] :
    BaireSpace X ↔ ∀ S : Set (Set X),
      S.Countable → (∀ G ∈ S, IsOpen G) → (∀ G ∈ S, Dense G) → Dense (⋂₀ S) := by
  constructor
  · intro h S hc ho hd
    have : BaireSpace X := h
    exact dense_sInter_of_isOpen ho hc hd
  · intro h
    constructor
    intro G ho hd
    simpa only [sInter_range] using
      h (range G) (countable_range G) (forall_mem_range.mpr ho) (forall_mem_range.mpr hd)

theorem isNowhereDense_empty (X : Type u) [TopologicalSpace X] :
    IsNowhereDense (∅ : Set X) :=
  _root_.isNowhereDense_empty

theorem isMeagre_empty (X : Type u) [TopologicalSpace X] :
    IsMeagre (∅ : Set X) :=
  IsMeagre.empty

theorem baireSpace_of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    BaireSpace X := by
  constructor
  intro G ho hd x
  exact isEmptyElim x

end ExpandedFA.P1.C07Category
