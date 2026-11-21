import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products

/-! Independent specification of paper.tex, `d10:05:choice-strength`.
`Option A` is the tagged disjoint union of A (the `some` points) and the
new point `none`. All topologies below are explicit, so the standard
library topology on an option type is never used. -/

open Set
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch05.ProductCompactnessChoiceStrength

abbrev Tagged (A : Type v) := Option A

def taggedType : Type (v + 1) := Type v → Type v
def taggedValue : taggedType := fun A => Option A

def taggedTopologyType : Type (v + 1) := (A : Type v) → TopologicalSpace (Tagged A)

/-- The three opens specified in the source, including when A is empty. -/
def taggedTopologyValue : taggedTopologyType.{v} := fun A => by
  classical
  exact {
    IsOpen := fun U => U = ∅ ∨ U = {none} ∨ U = univ
    isOpen_univ := Or.inr (Or.inr rfl)
    isOpen_inter := by
      rintro U V (rfl | rfl | rfl) (rfl | rfl | rfl) <;> simp
    isOpen_sUnion := by
      intro S hS
      by_cases hu : (univ : Set (Tagged A)) ∈ S
      · right; right
        exact eq_univ_of_univ_subset (subset_sUnion_of_mem hu)
      · by_cases hn : ({none} : Set (Tagged A)) ∈ S
        · right; left
          apply Subset.antisymm
          · rintro x ⟨U, hU, hx⟩
            rcases hS U hU with rfl | rfl | rfl
            · exact hx.elim
            · exact hx
            · exact (hu hU).elim
          · exact subset_sUnion_of_mem hn
        · left
          apply eq_empty_iff_forall_notMem.mpr
          rintro x ⟨U, hU, hx⟩
          rcases hS U hU with rfl | rfl | rfl
          · exact hx.elim
          · exact hn hU
          · exact hu hU }

def originalType : Type (v + 1) := (A : Type v) → Set (Tagged A)
def originalValue : originalType := fun A => range (@Option.some A)

def allInfinityType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → (A : I → Type v) → ∀ i, Tagged (A i)
def allInfinityValue : allInfinityType := fun _ _ => none

def productTopologyType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → (A : I → Type v) → TopologicalSpace (∀ i, Tagged (A i))
def productTopologyValue : productTopologyType := fun A =>
  Specs.D10Topology.Ch03.Products.productTopologyValue (fun i => taggedTopologyValue (A i))

def cylinderType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → (A : I → Type v) → I → Set (∀ i, Tagged (A i))
def cylinderValue : cylinderType := fun A i => (fun x => x i) ⁻¹' originalValue (A i)

def arbitraryProductCompactnessType : Type := Prop

def arbitraryProductCompactness : Prop :=
  ∀ (I : Type u) (X : I → Type v) (t : ∀ i, TopologicalSpace (X i)),
    (∀ i, @Compactness.CoverCompact (X i) (t i)) →
      @Compactness.CoverCompact (∀ i, X i)
        (Specs.D10Topology.Ch03.Products.productTopologyValue t)

def tagged_opens : Prop := ∀ (A : Type v) (U : Set (Tagged A)),
  IsOpen[taggedTopologyValue A] U ↔ U = ∅ ∨ U = {none} ∨ U = univ

def tagged_compact : Prop := ∀ (A : Type v), Nonempty A →
  @Compactness.CoverCompact (Tagged A) (taggedTopologyValue A)

def allInfinity_point : Prop := ∀ {I : Type u} (A : I → Type v),
  (∀ i, allInfinityValue A i = none) ∧ Nonempty (∀ i, Tagged (A i))

def original_closed : Prop := ∀ (A : Type v),
  @IsClosed (Tagged A) (taggedTopologyValue A) (originalValue A)

def cylinder_closed : Prop := ∀ {I : Type u} (A : I → Type v) (i : I),
  @IsClosed (∀ i, Tagged (A i)) (productTopologyValue A) (cylinderValue A i)

/-- Only the displayed, finitely indexed choices are supplied. All other
coordinates of the witness are the new point. -/
def finite_choices_witness : Prop := ∀ {I : Type u} (A : I → Type v)
  (F : Finset I) (a : ∀ i, i ∈ F → A i),
  ∃ x : ∀ i, Tagged (A i),
    (∀ i (hi : i ∈ F), x i = some (a i hi)) ∧
    (∀ i, i ∉ F → x i = none)

def cylinders_fip : Prop := ∀ {I : Type u} (A : I → Type v),
  (∀ i, Nonempty (A i)) → Compactness.HasFIP (range (cylinderValue A))

def intersection_nonempty : Prop := ∀ {I : Type u} (A : I → Type v),
  (∀ i, Nonempty (A i)) →
  @Compactness.CoverCompact (∀ i, Tagged (A i)) (productTopologyValue A) →
    (⋂ i, cylinderValue A i).Nonempty

def point_yields_choice : Prop := ∀ {I : Type u} (A : I → Type v)
  (x : ∀ i, Tagged (A i)), x ∈ ⋂ i, cylinderValue A i →
    ∃ f : ∀ i, A i, ∀ i, some (f i) = x i

def compact_product_yields_choice : Prop := ∀ {I : Type u} (A : I → Type v),
  (∀ i, Nonempty (A i)) →
  @Compactness.CoverCompact (∀ i, Tagged (A i)) (productTopologyValue A) →
    Nonempty (∀ i, A i)

def product_compactness_implies_choice : Prop :=
  arbitraryProductCompactness.{u, v} →
    ∀ (I : Type u) (A : I → Type v), (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i)

/-- Specialization to subsets of a possibly varying ambient family. -/
def product_compactness_implies_set_choice : Prop :=
  arbitraryProductCompactness.{u, v} →
    ∀ (I : Type u) (X : I → Type v) (A : ∀ i, Set (X i)),
      (∀ i, (A i).Nonempty) → ∃ f : ∀ i, X i, ∀ i, f i ∈ A i

def empty_index_choice : Prop := ∀ {I : Type u} [IsEmpty I] (A : I → Type v),
  ∃! f : ∀ i, A i, True

end Specs.D10Topology.Ch05.ProductCompactnessChoiceStrength
