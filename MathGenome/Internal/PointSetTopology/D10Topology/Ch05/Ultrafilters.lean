import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Ultrafilters
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.ProperFilters
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness

/-! Ultrafilters as maximal proper filters, paper.tex Chapter 5.
Mathlib orders filters oppositely to their member families. The first theorem
checks its maximality and NeBot fields against the source definition.
Extension below uses Mathlib's Zorn-based atomicity of the filter lattice.
The ultranet assertions are allocated to the separate Ultranets goal. -/

open Set Filter
universe u v
namespace D10Topology.Ch05
open D10Topology.Ch04

/-- Maximality by inclusion of member families, among proper filters. -/
def IsUltrafilter {X : Type u} (F : Filter X) : Prop :=
  F.NeBot ∧ ∀ G : Filter X, G.NeBot → FilterFiner G F → G = F

def principalUltrafilter {X : Type u} (x : X) : Filter X := pure x

def FreeFilter {X : Type u} (F : Filter X) : Prop := ⋂₀ F.sets = ∅

def finiteComplements (X : Type u) : Set (Set X) :=
  {A | ∃ K : Set X, K.Finite ∧ A = Kᶜ}

def cofiniteFilter (X : Type u) : Filter X := GeneratedFilter (finiteComplements X)

theorem isUltrafilter_iff_mathlib {X : Type u} (F : Filter X) :
    IsUltrafilter F ↔ ∃ U : Ultrafilter X, (U : Filter X) = F := by
  constructor
  · intro hF
    exact ⟨{ toFilter := F
             neBot' := hF.1
             le_of_le := fun G hG hGF => le_of_eq (hF.2 G hG hGF).symm }, rfl⟩
  · rintro ⟨U, rfl⟩
    exact ⟨U.neBot, fun G hG hGU => U.unique hGU hG⟩

theorem principalUltrafilter_mem {X : Type u} (x : X) (A : Set X) :
    A ∈ principalUltrafilter x ↔ x ∈ A := Iff.rfl

theorem principalUltrafilter_isUltrafilter {X : Type u} (x : X) :
    IsUltrafilter (principalUltrafilter x) :=
  (isUltrafilter_iff_mathlib _).mpr ⟨pure x, rfl⟩

theorem no_ultrafilter_on_empty {X : Type u} [IsEmpty X] (F : Filter X) :
    ¬ IsUltrafilter F := by
  intro hF
  exact hF.1.ne (Filter.filter_eq_bot_of_isEmpty F)

theorem ultrafilter_alternative {X : Type u} (F : Filter X) (hF : F.NeBot) :
    IsUltrafilter F ↔ ∀ A : Set X,
      (A ∈ F ∨ Aᶜ ∈ F) ∧ ¬ (A ∈ F ∧ Aᶜ ∈ F) := by
  let := hF
  constructor
  · intro h
    obtain ⟨U, rfl⟩ := (isUltrafilter_iff_mathlib F).mp h
    intro A
    exact ⟨U.mem_or_compl_mem A, fun ⟨hA, hc⟩ => Filter.compl_notMem hA hc⟩
  · intro h
    refine ⟨hF, fun G hG hGF => ?_⟩
    apply le_antisymm ((finer_iff_le G F).mp hGF)
    intro A hA
    rcases (h A).1 with hAF | hc
    · exact hAF
    · exact False.elim (hG.ne (Filter.empty_mem_iff_bot.mp (by
        simpa only [inter_compl_self] using Filter.inter_mem hA (hGF hc))))

theorem ultrafilter_converges_at_cluster {X : Type u} [TopologicalSpace X]
    (F : Filter X) (hF : IsUltrafilter F) (x : X) (hx : FilterClusters F x) :
    FilterConverges F x := by
  let := hF.1
  obtain ⟨G, hG, hGF, hGx⟩ := (clusters_iff_finer_converges F x).mp hx
  rwa [hF.2 G hG hGF] at hGx

theorem ultrafilter_image {X : Type u} {Y : Type v} (f : X → Y)
    (F : Filter X) (hF : IsUltrafilter F) : IsUltrafilter (ImageFilter f F) := by
  obtain ⟨U, rfl⟩ := (isUltrafilter_iff_mathlib F).mp hF
  exact (isUltrafilter_iff_mathlib _).mpr ⟨U.map f, rfl⟩

/-- Choice enters through `Ultrafilter.exists_le`, whose proof uses Zorn's lemma. -/
theorem proper_filter_extension {X : Type u} (F : Filter X) (hF : F.NeBot) :
    ∃ U : Filter X, IsUltrafilter U ∧ FilterFiner U F := by
  let := hF
  obtain ⟨U, hUF⟩ := Ultrafilter.exists_le F
  exact ⟨U, (isUltrafilter_iff_mathlib _).mpr ⟨U, rfl⟩, hUF⟩

theorem fip_ultrafilter_extension {X : Type u} (A : Set (Set X)) (hA : HasFIP A) :
    ∃ U : Filter X, IsUltrafilter U ∧ A ⊆ U.sets := by
  obtain ⟨F, hF, hAF⟩ := (fip_iff_contained_in_proper A).mp hA
  obtain ⟨U, hU, hUF⟩ := proper_filter_extension F hF
  exact ⟨U, hU, hAF.trans hUF⟩

theorem finiteComplements_mem (X : Type u) (A : Set X) :
    A ∈ finiteComplements X ↔ Aᶜ.Finite := by
  constructor
  · rintro ⟨K, hK, rfl⟩
    simpa only [compl_compl] using hK
  · intro hA
    exact ⟨Aᶜ, hA, (compl_compl A).symm⟩

theorem cofiniteFilter_eq_mathlib (X : Type u) :
    cofiniteFilter X = (Filter.cofinite : Filter X) := by
  apply le_antisymm
  · intro A hA
    exact generated_contains _ ((finiteComplements_mem X A).mpr hA)
  · apply Filter.le_generate_iff.mpr
    intro A hA
    exact (finiteComplements_mem X A).mp hA

theorem cofiniteFilter_proper (X : Type u) [Infinite X] :
    (cofiniteFilter X).NeBot := by
  rw [cofiniteFilter_eq_mathlib]
  infer_instance

theorem finiteComplements_fip (X : Type u) [Infinite X] :
    HasFIP (finiteComplements X) :=
  (generated_proper_iff_fip _).mp (cofiniteFilter_proper X)

/-- Every extension is free; maximality is not needed for this implication. -/
theorem cofinite_extension_free {X : Type u} (F : Filter X)
    (hF : FilterFiner F (cofiniteFilter X)) : FreeFilter F := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hc : {x}ᶜ ∈ cofiniteFilter X :=
    generated_contains _ ⟨{x}, Set.finite_singleton x, rfl⟩
  have hn : x ∈ ({x} : Set X)ᶜ := Set.mem_sInter.mp hx _ (hF hc)
  exact hn (Set.mem_singleton x)

theorem cofinite_ultrafilter_extension_free {X : Type u} [Infinite X]
    (U : Filter X) (_hU : IsUltrafilter U)
    (hU : FilterFiner U (cofiniteFilter X)) : FreeFilter U :=
  cofinite_extension_free U hU

theorem exists_free_ultrafilter (X : Type u) [Infinite X] :
    ∃ U : Filter X, IsUltrafilter U ∧ FilterFiner U (cofiniteFilter X) ∧ FreeFilter U := by
  obtain ⟨U, hU, hUF⟩ := proper_filter_extension _ (cofiniteFilter_proper X)
  exact ⟨U, hU, hUF, cofinite_extension_free U hUF⟩

end D10Topology.Ch05
