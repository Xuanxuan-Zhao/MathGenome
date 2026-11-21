import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.IrreducibleContinua
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.FilteredContinua
import Mathlib.Order.Zorn

/-!
Minimal subcontinua are obtained by Zorn's lemma in reverse inclusion.
Nonempty chains have their intersection as a bound, by the accepted
filtered compact-connected intersection theorem. The whole continuum
bounds the empty chain. This proof applies to arbitrary nonempty subsets,
without assuming that they are closed or that the continuum is metrizable.
-/

open Set
universe u

namespace D10Topology.Ch06

def Continuum (K : Type u) [TopologicalSpace K] : Prop :=
  IrreducibleContinuaData.Continuum K

def Subcontinuum {K : Type u} [TopologicalSpace K] (L : Set K) : Prop :=
  IrreducibleContinuaData.Subcontinuum L

def IrreducibleBetween {K : Type u} [TopologicalSpace K]
    (L : Set K) (x y : K) : Prop :=
  IrreducibleContinuaData.IrreducibleBetween L x y

theorem subcontinuum_iff {K : Type u} [TopologicalSpace K] [T2Space K]
    (L : Set K) :
    Subcontinuum L ↔ L.Nonempty ∧ Ch05.SubspaceCompact L ∧ ConnectedSubset L := by
  constructor
  · rintro ⟨hne, hcompact, hconn, _⟩
    exact ⟨Set.nonempty_coe_sort.mp hne, hcompact, hconn⟩
  · rintro ⟨hne, hcompact, hconn⟩
    exact ⟨Set.nonempty_coe_sort.mpr hne, hcompact, hconn, inferInstance⟩

theorem univ_subcontinuum (K : Type u) [TopologicalSpace K] (hK : Continuum K) :
    Subcontinuum (univ : Set K) := by
  let : T2Space K := hK.2.2.2
  let : Nonempty K := hK.1
  let : CompactSpace K := (Ch05.coverCompact_iff_compactSpace K).mp hK.2.1
  apply (subcontinuum_iff _).mpr
  refine ⟨Set.univ_nonempty, (Ch05.subspaceCompact_iff_isCompact _).mpr isCompact_univ, ?_⟩
  apply (connectedSubset_iff_isPreconnected _).mpr
  exact (connected_iff_preconnectedSpace K).mp hK.2.2.1 |>.isPreconnected_univ

theorem exists_minimal_subcontinuum (K : Type u) [TopologicalSpace K]
    (hK : Continuum K) (A : Set K) (hA : A.Nonempty) :
    ∃ L : Set K, Subcontinuum L ∧ A ⊆ L ∧
      ∀ M : Set K, Subcontinuum M → A ⊆ M → M ⊆ L → M = L := by
  classical
  let : T2Space K := hK.2.2.2
  let : CompactSpace K := (Ch05.coverCompact_iff_compactSpace K).mp hK.2.1
  let S : Set (Set K) := {L | Subcontinuum L ∧ A ⊆ L}
  have hb : ∀ c ⊆ S, IsChain (· ⊆ ·) c →
      ∃ lb ∈ S, ∀ L ∈ c, lb ⊆ L := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · exact ⟨univ, ⟨univ_subcontinuum K hK, subset_univ _⟩, by simp⟩
    · let : Nonempty c := Set.nonempty_coe_sort.mpr hcne
      let B : c → Set K := fun L => L.val
      have hB (L : c) := (subcontinuum_iff (B L)).mp (hcS L.property).1
      have hclosed (L : c) : IsClosed (B L) :=
        ((Ch05.subspaceCompact_iff_isCompact _).mp (hB L).2.1).isClosed
      have hfilter : ∀ i j : c, ∃ k : c, B k ⊆ B i ∩ B j := by
        intro i j
        rcases hc.total i.property j.property with hij | hji
        · exact ⟨i, subset_inter Subset.rfl hij⟩
        · exact ⟨j, subset_inter hji Subset.rfl⟩
      obtain ⟨hne, hconn⟩ := filtered_continua B hK.2.1
        (fun L => hA.mono (hcS L.property).2) hclosed (fun L => (hB L).2.2) hfilter
      refine ⟨⋂ L, B L, ⟨(subcontinuum_iff _).mpr ⟨hne, ?_, hconn⟩, ?_⟩, ?_⟩
      · exact (Ch05.subspaceCompact_iff_isCompact _).mpr (isClosed_iInter hclosed).isCompact
      · intro a ha
        exact mem_iInter.mpr fun L => (hcS L.property).2 ha
      · intro L hL
        exact iInter_subset B ⟨L, hL⟩
  obtain ⟨L, hL, hmin⟩ := zorn_superset S hb
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hM hAM hML
  exact Subset.antisymm hML (hmin ⟨hM, hAM⟩ hML)

theorem exists_irreducible_between (K : Type u) [TopologicalSpace K]
    (hK : Continuum K) (x y : K) : ∃ L : Set K, IrreducibleBetween L x y := by
  obtain ⟨L, hL, hxyL, hmin⟩ :=
    exists_minimal_subcontinuum K hK {x, y} (by simp)
  refine ⟨L, hL, hxyL (by simp), hxyL (by simp), ?_⟩
  intro M hM hxM hyM hML
  exact hmin M hM (by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hxM hyM) hML

end D10Topology.Ch06
