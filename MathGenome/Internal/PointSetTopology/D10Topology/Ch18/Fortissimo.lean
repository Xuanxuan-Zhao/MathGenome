import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.Fortissimo
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import Mathlib.Topology.DiscreteSubset

open Set TopologicalSpace
open scoped Topology
universe u

namespace D10Topology.Ch18.Fortissimo

abbrev topology (D : Type u) : TopologicalSpace (Option D) :=
  Specs.D10Topology.Ch18.Fortissimo.topology D

variable (D : Type u)
local instance : TopologicalSpace (Option D) := topology D

theorem open_characterization (U : Set (Option D)) :
    IsOpen U ↔ (none ∈ U → Uᶜ.Countable) := Iff.rfl

theorem open_of_not_mem_none {U : Set (Option D)} (h : none ∉ U) : IsOpen U :=
  fun hp => (h hp).elim

theorem open_of_countable_compl {U : Set (Option D)} (h : Uᶜ.Countable) : IsOpen U :=
  fun _ => h

theorem isolated_clopen (d : D) : IsClopen ({some d} : Set (Option D)) := by
  constructor
  · apply isOpen_compl_iff.mp
    apply open_of_countable_compl
    simpa only [compl_compl] using countable_singleton (some d)
  · exact open_of_not_mem_none D (by simp)

theorem clopen_of_open_mem_none {U : Set (Option D)} (hU : IsOpen U) (hp : none ∈ U) :
    IsClopen U := by
  exact ⟨isOpen_compl_iff.mp (open_of_not_mem_none D (by simpa)), hU⟩

theorem clopen_basis :
    TopologicalSpace.IsTopologicalBasis {U : Set (Option D) | IsClopen U} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.2
  · intro x U hx hU
    cases x with
    | none => exact ⟨U, clopen_of_open_mem_none D hU hx, hx, Subset.rfl⟩
    | some d => exact ⟨{some d}, isolated_clopen D d, by simp, singleton_subset_iff.mpr hx⟩

theorem hausdorff : T2Space (Option D) := by
  apply (t2Space_iff (Option D)).mpr
  intro x y hxy
  have hsep : ∀ d : D, ∀ y : Option D, some d ≠ y →
      ∃ U V : Set (Option D), IsOpen U ∧ IsOpen V ∧
        some d ∈ U ∧ y ∈ V ∧ Disjoint U V := by
    intro d y h
    exact ⟨{some d}, {some d}ᶜ, (isolated_clopen D d).2,
      (isolated_clopen D d).1.isOpen_compl, by simp,
      by simpa [eq_comm] using h, disjoint_compl_right⟩
  cases x with
  | some d => exact hsep d y hxy
  | none =>
    cases y with
    | none => exact (hxy rfl).elim
    | some d =>
      obtain ⟨U, V, hU, hV, hd, hp, hdis⟩ := hsep d none (by simp)
      exact ⟨V, U, hV, hU, hp, hd, hdis.symm⟩

theorem normal : NormalSpace (Option D) := by
  constructor
  intro A B hA hB hdis
  have aux : ∀ A B : Set (Option D), IsClosed A → Disjoint A B → none ∉ A →
      ∃ U V : Set (Option D), IsOpen U ∧ IsOpen V ∧
        A ⊆ U ∧ B ⊆ V ∧ Disjoint U V := by
    intro A B hA hd hp
    exact ⟨A, Aᶜ, open_of_not_mem_none D hp, hA.isOpen_compl,
      Subset.rfl, (fun _ hb ha => disjoint_left.mp hd ha hb), disjoint_compl_right⟩
  by_cases hp : none ∈ A
  · have hpB : none ∉ B := fun h => disjoint_left.mp hdis hp h
    obtain ⟨U, V, hU, hV, hBU, hAV, hd⟩ := aux B A hB hdis.symm hpB
    exact ⟨V, U, hV, hU, hAV, hBU, hd.symm⟩
  · exact aux A B hA hdis hp

/-- Every neighborhood of the new point has countable complement, even
when the neighborhood is not initially assumed open. -/
theorem countable_compl_of_nhds {N : Set (Option D)} (hN : N ∈ 𝓝 (none : Option D)) :
    Nᶜ.Countable := by
  obtain ⟨U, hUN, hU, hp⟩ := mem_nhds_iff.mp hN
  exact (hU hp).mono (compl_subset_compl.mpr hUN)

theorem lindelof : LindelofSpace (Option D) := by
  classical
  apply isLindelof_univ_iff.mp
  apply isLindelof_iff_countable_subcover.mpr
  intro ι U ho hcov
  have hex : ∀ x : Option D, ∃ i, x ∈ U i := fun x => mem_iUnion.mp (hcov (mem_univ x))
  choose f hf using hex
  let i₀ := f none
  let J := insert i₀ (f '' (U i₀)ᶜ)
  refine ⟨J, ((ho i₀ (hf none)).image f).insert i₀, ?_⟩
  intro x _
  by_cases hx : x ∈ U i₀
  · exact mem_iUnion₂.mpr ⟨i₀, mem_insert _ _, hx⟩
  · exact mem_iUnion₂.mpr ⟨f x, mem_insert_of_mem _ (mem_image_of_mem f hx), hf x⟩

/-- Countable subsets of the isolated part are closed and discrete. -/
theorem closed_discrete_of_countable {A : Set (Option D)}
    (hc : A.Countable) (hp : none ∉ A) : IsClosed A ∧ IsDiscrete A := by
  refine ⟨isOpen_compl_iff.mp (open_of_countable_compl D (by simpa)), ?_⟩
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  cases x with
  | none => exact (hp hx).elim
  | some d =>
    exact ⟨{some d}, (isolated_clopen D d).2, singleton_inter_of_mem hx⟩

theorem not_compact [Uncountable D] : ¬ CompactSpace (Option D) := by
  intro h
  let := h
  obtain ⟨A, _, hAc, hAi⟩ := (infinite_univ : (univ : Set D).Infinite).exists_subset_countable_infinite
  let B : Set (Option D) := some '' A
  have hBc : B.Countable := hAc.image some
  have hp : none ∉ B := by simp [B]
  obtain ⟨hclosed, hdiscrete⟩ := closed_discrete_of_countable D hBc hp
  have hBfin : B.Finite := hclosed.isCompact.finite hdiscrete
  exact hAi (Finite.of_finite_image hBfin (Option.some_injective D).injOn)

theorem no_countable_localBase [Uncountable D] (L : Set (Set (Option D)))
    (hc : L.Countable) : ¬ Ch01.LocalBase (topology D) none L := by
  intro hL
  have hcomp : ∀ N ∈ L, Nᶜ.Countable := by
    intro N hNL
    exact countable_compl_of_nhds D
      ((Ch01.neighborhood_iff_mem_nhds (topology D) none N).mp (hL.1 N hNL))
  let E : Set (Option D) := ⋃ N ∈ L, Nᶜ
  have hE : E.Countable := hc.biUnion hcomp
  have hpre : (some ⁻¹' E : Set D).Countable := hE.preimage (Option.some_injective D)
  obtain ⟨d, hd⟩ : ∃ d : D, some d ∉ E := by
    by_contra! h
    apply not_countable_univ (α := D)
    exact hpre.mono (fun x _ => h x)
  have hp : none ∈ ({some d}ᶜ : Set (Option D)) := by simp
  have hN : Ch01.Neighborhood (topology D) none ({some d}ᶜ) :=
    ⟨{some d}ᶜ, (isolated_clopen D d).1.isOpen_compl, hp, Subset.rfl⟩
  obtain ⟨N, hNL, hsub⟩ := hL.2 _ hN
  have hdN : some d ∈ N := by
    by_contra hn
    exact hd (mem_iUnion₂.mpr ⟨N, hNL, hn⟩)
  exact hsub hdN (mem_singleton (some d))

theorem not_first_countable [Uncountable D] : ¬ FirstCountableTopology (Option D) := by
  intro h
  obtain ⟨L, hc, hL⟩ := (Ch08.firstCountable_iff_mathlib.mpr h) (none : Option D)
  exact no_countable_localBase D L hc hL

theorem not_separable [Uncountable D] : ¬ SeparableSpace (Option D) := by
  intro h
  obtain ⟨A, hc, hd⟩ := h.exists_countable_dense
  have hall : ∀ d : D, some d ∈ A := by
    intro d
    obtain ⟨x, hx, hxa⟩ := hd.inter_open_nonempty {some d}
      (isolated_clopen D d).2 (singleton_nonempty _)
    simpa only [mem_singleton_iff] using hx ▸ hxa
  apply not_countable_univ (α := D)
  exact (hc.preimage (Option.some_injective D)).mono (fun d _ => hall d)

end D10Topology.Ch18.Fortissimo
