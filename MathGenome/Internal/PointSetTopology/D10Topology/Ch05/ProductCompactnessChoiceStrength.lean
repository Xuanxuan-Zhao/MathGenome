import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.ProductCompactnessChoiceStrength
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products

/-! The tagged-space proof of `d10:05:choice-strength`. No product compactness
instance is invoked: compactness of this product is an explicit hypothesis.
Finite intersections are handled by induction and coordinate replacement;
the final choice function is read from an intersection point. -/

open Set
open scoped Topology
universe u v

namespace D10Topology.Ch05.ChoiceStrength

abbrev Tagged (A : Type v) := Option A

@[instance_reducible] def taggedTopology (A : Type v) : TopologicalSpace (Tagged A) :=
  Specs.D10Topology.Ch05.ProductCompactnessChoiceStrength.taggedTopologyValue A

def original (A : Type v) : Set (Tagged A) := range (@Option.some A)

def allInfinity {I : Type u} (A : I → Type v) : ∀ i, Tagged (A i) := fun _ => none

@[instance_reducible] def productTopology {I : Type u} (A : I → Type v) :
    TopologicalSpace (∀ i, Tagged (A i)) :=
  Ch03.productTopology (fun i => taggedTopology (A i))

def cylinder {I : Type u} (A : I → Type v) (i : I) : Set (∀ i, Tagged (A i)) :=
  (fun x => x i) ⁻¹' original (A i)

/-- The full product-compactness assertion whose choice strength is at issue. -/
def ArbitraryProductCompactness : Prop :=
  ∀ (I : Type u) (X : I → Type v) (t : ∀ i, TopologicalSpace (X i)),
    (∀ i, @CoverCompact (X i) (t i)) →
      @CoverCompact (∀ i, X i) (Ch03.productTopology t)

theorem tagged_opens (A : Type v) (U : Set (Tagged A)) :
    IsOpen[taggedTopology A] U ↔ U = ∅ ∨ U = {none} ∨ U = univ := Iff.rfl

theorem tagged_compact (A : Type v) (hA : Nonempty A) :
    @CoverCompact (Tagged A) (taggedTopology A) := by
  obtain ⟨a⟩ := hA
  intro U hU hcover
  obtain ⟨V, hVU, haV⟩ := hcover (mem_univ (some a))
  have hV : V = univ := by
    rcases (tagged_opens A V).mp (hU V hVU) with rfl | rfl | hV
    · exact haV.elim
    · simp at haV
    · exact hV
  subst V
  exact ⟨{univ}, singleton_subset_iff.mpr hVU, finite_singleton _, by simp⟩

theorem allInfinity_point {I : Type u} (A : I → Type v) :
    (∀ i, allInfinity A i = none) ∧ Nonempty (∀ i, Tagged (A i)) :=
  ⟨fun _ => rfl, ⟨allInfinity A⟩⟩

theorem original_closed (A : Type v) :
    @IsClosed (Tagged A) (taggedTopology A) (original A) := by
  let := taggedTopology A
  have hc : (original A)ᶜ = {none} := by
    ext x
    cases x <;> simp [original]
  apply isOpen_compl_iff.mp
  rw [hc]
  exact (tagged_opens A _).mpr (Or.inr (Or.inl rfl))

theorem cylinder_closed {I : Type u} (A : I → Type v) (i : I) :
    @IsClosed (∀ i, Tagged (A i)) (productTopology A) (cylinder A i) := by
  let := productTopology A
  let := taggedTopology (A i)
  exact (original_closed (A i)).preimage
    (Ch03.projection_continuous (fun i => taggedTopology (A i)) i)

theorem finite_choices_witness {I : Type u} (A : I → Type v)
    (F : Finset I) (a : ∀ i, i ∈ F → A i) :
    ∃ x : ∀ i, Tagged (A i),
      (∀ i (hi : i ∈ F), x i = some (a i hi)) ∧
      (∀ i, i ∉ F → x i = none) := by
  classical
  refine ⟨fun i => if hi : i ∈ F then some (a i hi) else none, ?_, ?_⟩
  · intro i hi; simp [hi]
  · intro i hi; simp [hi]

/-- Induction over the finite subfamily makes only one additional selection
at each step. The empty subfamily uses the explicit all-infinity point. -/
theorem cylinders_fip {I : Type u} (A : I → Type v)
    (hA : ∀ i, Nonempty (A i)) : HasFIP (range (cylinder A)) := by
  classical
  intro B hB hfin
  induction B, hfin using Set.Finite.induction_on with
  | empty => exact ⟨allInfinity A, by simp⟩
  | @insert C B hCB hfin ih =>
    obtain ⟨i, rfl⟩ := hB (mem_insert C B)
    obtain ⟨x, hx⟩ := ih (fun V hV => hB (mem_insert_of_mem _ hV))
    obtain ⟨a⟩ := hA i
    refine ⟨Function.update x i (some a), mem_sInter.mpr ?_⟩
    intro V hV
    rcases hV with rfl | hV
    · exact ⟨a, by simp⟩
    · obtain ⟨j, rfl⟩ := hB (mem_insert_of_mem _ hV)
      by_cases hji : j = i
      · subst j
        exact ⟨a, by simp⟩
      · have hxj := mem_sInter.mp hx _ hV
        simpa only [cylinder, mem_preimage, Function.update_of_ne hji] using hxj

theorem intersection_nonempty {I : Type u} (A : I → Type v)
    (hA : ∀ i, Nonempty (A i))
    (hP : @CoverCompact (∀ i, Tagged (A i)) (productTopology A)) :
    (⋂ i, cylinder A i).Nonempty := by
  let := productTopology A
  have hc : ∀ C ∈ range (cylinder A),
      @IsClosed (∀ i, Tagged (A i)) (productTopology A) C := by
    rintro C ⟨i, rfl⟩
    exact cylinder_closed A i
  have h := (coverCompact_iff_closed_fip _).mp hP
    (range (cylinder A)) hc (cylinders_fip A hA)
  simpa only [sInter_range] using h

/-- `Option.get` reads an existing coordinate; it makes no new choice. -/
theorem point_yields_choice {I : Type u} (A : I → Type v)
    (x : ∀ i, Tagged (A i)) (hx : x ∈ ⋂ i, cylinder A i) :
    ∃ f : ∀ i, A i, ∀ i, some (f i) = x i := by
  have hs : ∀ i, (x i).isSome := by
    intro i
    obtain ⟨a, ha⟩ := mem_iInter.mp hx i
    exact Option.isSome_of_eq_some ha.symm
  exact ⟨fun i => (x i).get (hs i), fun i => Option.some_get (hs i)⟩

theorem compact_product_yields_choice {I : Type u} (A : I → Type v)
    (hA : ∀ i, Nonempty (A i))
    (hP : @CoverCompact (∀ i, Tagged (A i)) (productTopology A)) :
    Nonempty (∀ i, A i) := by
  obtain ⟨x, hx⟩ := intersection_nonempty A hA hP
  obtain ⟨f, _⟩ := point_yields_choice A x hx
  exact ⟨f⟩

/-- The premise is arbitrary-space product compactness in the source's
open-cover convention, with no separation or nonemptiness restrictions. -/
theorem product_compactness_implies_choice
    (hT : ArbitraryProductCompactness.{u, v}) :
    ∀ (I : Type u) (A : I → Type v),
      (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i) := by
  intro I A hA
  apply compact_product_yields_choice A hA
  exact hT I (fun i => Tagged (A i)) (fun i => taggedTopology (A i))
    (fun i => tagged_compact (A i) (hA i))

theorem product_compactness_implies_set_choice
    (hT : ArbitraryProductCompactness.{u, v})
    (I : Type u) (X : I → Type v) (A : ∀ i, Set (X i))
    (hA : ∀ i, (A i).Nonempty) : ∃ f : ∀ i, X i, ∀ i, f i ∈ A i := by
  have hn : ∀ i, Nonempty (A i) := by
    intro i
    obtain ⟨a, ha⟩ := hA i
    exact ⟨⟨a, ha⟩⟩
  obtain ⟨f⟩ := product_compactness_implies_choice hT I (fun i => A i) hn
  exact ⟨fun i => (f i).val, fun i => (f i).property⟩

theorem empty_index_choice {I : Type u} [IsEmpty I] (A : I → Type v) :
    ∃! f : ∀ i, A i, True := by
  refine ⟨fun i => isEmptyElim i, trivial, ?_⟩
  intro f _
  funext i
  exact isEmptyElim i

end D10Topology.Ch05.ChoiceStrength
