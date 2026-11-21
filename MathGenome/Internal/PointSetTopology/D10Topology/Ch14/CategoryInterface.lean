import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryInterface
import Mathlib.Topology.Baire.Lemmas

/-! The ambient definitions and Baire equivalences of paper.tex 14.1–14.2. -/

open Set Filter
universe u

namespace D10Topology.Ch14

def NowhereDenseIn {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  interior (closure A) = ∅

def MeagerIn {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ S : Set (Set X), S.Countable ∧ (∀ B ∈ S, NowhereDenseIn B) ∧ A = ⋃₀ S

def ResidualIn {X : Type u} [TopologicalSpace X] (A : Set X) : Prop := MeagerIn Aᶜ

def SecondCategoryIn {X : Type u} [TopologicalSpace X] (A : Set X) : Prop := ¬ MeagerIn A

def BaireIn (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ S : Set (Set X), S.Countable →
    (∀ U ∈ S, IsOpen U ∧ Dense U) → Dense (⋂₀ S)

theorem nowhereDense_iff_library {X : Type u} [TopologicalSpace X] (A : Set X) :
    NowhereDenseIn A ↔ IsNowhereDense A := Iff.rfl

theorem meager_iff_library {X : Type u} [TopologicalSpace X] (A : Set X) :
    MeagerIn A ↔ IsMeagre A := by
  rw [isMeagre_iff_eq_countable_union_isNowhereDense]
  change (∃ S : Set (Set X), S.Countable ∧ (∀ B ∈ S, IsNowhereDense B) ∧ A = ⋃₀ S) ↔ _
  constructor
  · rintro ⟨S, hc, hn, he⟩
    exact ⟨S, hn, hc, he⟩
  · rintro ⟨S, hn, hc, he⟩
    exact ⟨S, hc, hn, he⟩

theorem residual_iff_library {X : Type u} [TopologicalSpace X] (A : Set X) :
    ResidualIn A ↔ A ∈ residual X := by
  simp only [ResidualIn, meager_iff_library, IsMeagre, compl_compl]

theorem secondCategory_iff_library {X : Type u} [TopologicalSpace X] (A : Set X) :
    SecondCategoryIn A ↔ ¬ IsMeagre A := by
  simp only [SecondCategoryIn, meager_iff_library]

theorem baire_iff_library (X : Type u) [TopologicalSpace X] :
    BaireIn X ↔ BaireSpace X := by
  constructor
  · intro h
    refine ⟨fun f ho hd => ?_⟩
    simpa only [sInter_range] using h (range f) (countable_range f)
      (by rintro U ⟨n, rfl⟩; exact ⟨ho n, hd n⟩)
  · intro h
    letI := h
    intro S hc hS
    exact dense_sInter_of_isOpen (fun U hU => (hS U hU).1) hc
      (fun U hU => (hS U hU).2)

theorem empty_baire (X : Type u) [TopologicalSpace X] [IsEmpty X] : BaireIn X := by
  intro S _ _ x
  exact isEmptyElim x

theorem baire_iff_residual_dense (X : Type u) [TopologicalSpace X] :
    BaireIn X ↔ ∀ R : Set X, ResidualIn R → Dense R := by
  constructor
  · intro h R hR
    letI := (baire_iff_library X).mp h
    exact dense_of_mem_residual ((residual_iff_library R).mp hR)
  · intro h S hc hS
    apply h
    apply (residual_iff_library _).mpr
    exact (countable_sInter_mem hc).mpr fun U hU =>
      residual_of_dense_open (hS U hU).1 (hS U hU).2

theorem baire_iff_no_open_meager (X : Type u) [TopologicalSpace X] :
    BaireIn X ↔ ∀ U : Set X, IsOpen U → U.Nonempty → ¬ MeagerIn U := by
  constructor
  · intro h U ho hn hm
    letI := (baire_iff_library X).mp h
    exact not_isMeagre_of_isOpen ho hn ((meager_iff_library U).mp hm)
  · intro h
    apply (baire_iff_residual_dense X).mpr
    intro R hR
    apply dense_iff_inter_open.mpr
    intro U ho hn
    classical
    by_contra hd
    have hsub : U ⊆ Rᶜ := by
      intro x hx hxR
      exact hd ⟨x, hx, hxR⟩
    exact h U ho hn ((meager_iff_library U).mpr
      (((meager_iff_library Rᶜ).mp hR).mono hsub))

theorem baire_iff_closed_unions (X : Type u) [TopologicalSpace X] :
    BaireIn X ↔ ∀ F : Set (Set X), F.Countable →
      (∀ C ∈ F, IsClosed C ∧ interior C = ∅) → interior (⋃₀ F) = ∅ := by
  constructor
  · intro h F hc hF
    letI := (baire_iff_library X).mp h
    exact interior_sUnion_eq_empty_of_isClosed
      (fun C hC => (hF C hC).1) hc
      (fun C hC => (hF C hC).1.isNowhereDense_iff.mpr (hF C hC).2)
  · intro h
    apply (baire_iff_library X).mpr
    apply baireSpace_iff_interior_iUnion_eq_empty.mpr
    intro f hc hn
    simpa only [sUnion_range] using h (range f) (countable_range f)
      (by rintro C ⟨n, rfl⟩; exact ⟨hc n, (hc n).isNowhereDense_iff.mp (hn n)⟩)

theorem residual_contains_intersection {X : Type u} [TopologicalSpace X]
    (R : Set X) (hR : ResidualIn R) :
    ∃ S : Set (Set X), S.Countable ∧ (∀ U ∈ S, IsOpen U ∧ Dense U) ∧
      ⋂₀ S ⊆ R ∧ IsGδ (⋂₀ S) ∧ (BaireIn X → Dense (⋂₀ S)) := by
  obtain ⟨S, ho, hd, hc, hs⟩ := mem_residual_iff.mp ((residual_iff_library R).mp hR)
  exact ⟨S, hc, fun U hU => ⟨ho U hU, hd U hU⟩, hs,
    ⟨S, ho, hc, rfl⟩, fun h => h S hc (fun U hU => ⟨ho U hU, hd U hU⟩)⟩

theorem contains_dense_gdelta_residual {X : Type u} [TopologicalSpace X]
    (R G : Set X) (hsub : G ⊆ R) (hG : IsGδ G) (hd : Dense G) : ResidualIn R := by
  exact (residual_iff_library R).mpr (mem_of_superset (residual_of_dense_Gδ hG hd) hsub)

theorem residual_iff_contains_dense_gdelta {X : Type u} [TopologicalSpace X]
    (h : BaireIn X) (R : Set X) :
    ResidualIn R ↔ ∃ G : Set X, G ⊆ R ∧ IsGδ G ∧ Dense G := by
  letI := (baire_iff_library X).mp h
  exact (residual_iff_library R).trans mem_residual

end D10Topology.Ch14
