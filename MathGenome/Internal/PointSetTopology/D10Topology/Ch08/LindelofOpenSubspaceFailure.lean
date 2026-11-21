import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.LindelofOpenSubspaceFailure
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions

/-! The elementary cofinite-neighborhood extension of a discrete set.
Compactness is proved by selecting a cover member at `none` and then
covering its finite complement. No one-point compactification is imported. -/

open Set TopologicalSpace
universe u

namespace D10Topology.Ch08.CofinitePoint

abbrev topology (E : Type u) : TopologicalSpace (Option E) :=
  Specs.D10Topology.Ch08.LindelofOpenSubspaceFailure.topology E

theorem open_iff (E : Type u) (s : Set (Option E)) :
    @IsOpen _ (topology E) s ↔
      (none ∈ s → (Option.some ⁻¹' sᶜ).Finite) := Iff.rfl

theorem open_images (E : Type u) (A : Set E) :
    @IsOpen _ (topology E) (Option.some '' A) := by
  intro h
  obtain ⟨e, _, he⟩ := h
  cases he

section
variable (E : Type u)
local instance : TopologicalSpace (Option E) := topology E

theorem open_copy : IsOpen (range (Option.some : E → Option E)) := by
  simpa only [image_univ] using open_images E univ

private theorem open_singleton (e : E) : IsOpen ({some e} : Set (Option E)) := by
  simpa using open_images E {e}

private theorem open_complement_singleton (e : E) :
    IsOpen ({some e}ᶜ : Set (Option E)) := by
  intro _
  convert (finite_singleton e) using 1
  ext x
  simp

theorem compact : CompactSpace (Option E) := by
  classical
  refine ⟨isCompact_of_finite_subcover ?_⟩
  intro ι U ho hcov
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov (mem_univ (none : Option E)))
  have hf : (Option.some ⁻¹' (U i)ᶜ).Finite := ho i hi
  have hcover : ∀ e : E, ∃ j, some e ∈ U j :=
    fun e => mem_iUnion.mp (hcov (mem_univ (some e)))
  choose j hj using hcover
  refine ⟨insert i (hf.toFinset.image j), ?_⟩
  intro x _
  cases x with
  | none => exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hi⟩
  | some e =>
    by_cases he : some e ∈ U i
    · exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, he⟩
    · exact mem_iUnion₂.mpr ⟨j e, Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨e, hf.mem_toFinset.mpr he, rfl⟩), hj e⟩

theorem hausdorff : T2Space (Option E) := by
  apply (t2Space_iff (Option E)).mpr
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => exact (hxy rfl).elim
    | some e =>
      exact ⟨{some e}ᶜ, {some e}, open_complement_singleton E e,
        open_singleton E e, by simp, by simp, disjoint_compl_left⟩
  | some e =>
    refine ⟨{some e}, {some e}ᶜ, open_singleton E e,
      open_complement_singleton E e, by simp, ?_, disjoint_compl_right⟩
    simpa [eq_comm] using hxy

theorem lindelof : LindelofSpace (Option E) := by
  let := compact E
  infer_instance

theorem induced_discrete : (topology E).induced Option.some = (⊥ : TopologicalSpace E) := by
  apply TopologicalSpace.ext
  funext A
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨Option.some '' A, open_images E A, (Option.some_injective E).preimage_image A⟩

theorem subspace_discrete : DiscreteTopology (range (Option.some : E → Option E)) := by
  apply discreteTopology_iff_forall_isOpen.mpr
  intro A
  have h : IsOpen ((Subtype.val : range (Option.some : E → Option E) → Option E) '' A) := by
    intro hn
    obtain ⟨x, _, hx⟩ := hn
    obtain ⟨e, he⟩ := x.property
    exact ((Option.some_ne_none e) (he.trans hx)).elim
  exact isOpen_induced_iff.mpr ⟨_, h, Subtype.val_injective.preimage_image A⟩

theorem singleton_fiber (e : E) :
    {x : range (Option.some : E → Option E) | x.val = some e} =
      {⟨some e, mem_range_self e⟩} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff, Subtype.ext_iff]

theorem singleton_cover [Uncountable E] :
    let U : E → Set (range (Option.some : E → Option E)) :=
      fun e => {x | x.val = some e}
    (∀ e, IsOpen (U e)) ∧ (⋃ e, U e) = univ ∧
      ∀ J : Set E, J.Countable → (⋃ e ∈ J, U e) ≠ univ := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact (open_singleton E e).preimage continuous_subtype_val
  · apply eq_univ_of_forall
    intro x
    obtain ⟨e, he⟩ := x.property
    exact mem_iUnion.mpr ⟨e, he.symm⟩
  · intro J hJ hcov
    have hJU : J = univ := by
      apply eq_univ_of_forall
      intro e
      have hm := (eq_univ_iff_forall.mp hcov) ⟨some e, mem_range_self e⟩
      obtain ⟨f, hf, he⟩ := mem_iUnion₂.mp hm
      have hef : e = f := (Option.some_injective E) he
      exact hef.symm ▸ hf
    exact Set.not_countable_univ (α := E) (hJU ▸ hJ)

theorem subspace_not_lindelof [Uncountable E] :
    ¬ LindelofSpace (range (Option.some : E → Option E)) := by
  intro h
  obtain ⟨ho, hc, hn⟩ := singleton_cover E
  obtain ⟨J, hJ, hcov⟩ := lindelof_indexed_countable_subcover h
    (fun e => {x : range (Option.some : E → Option E) | x.val = some e}) ho hc
  exact hn J hJ hcov

theorem failure_of_open_heredity [Uncountable E] :
    CompactSpace (Option E) ∧ T2Space (Option E) ∧ LindelofSpace (Option E) ∧
      IsOpen (range (Option.some : E → Option E)) ∧
      DiscreteTopology (range (Option.some : E → Option E)) ∧
      ¬ LindelofSpace (range (Option.some : E → Option E)) :=
  ⟨compact E, hausdorff E, lindelof E, open_copy E,
    subspace_discrete E, subspace_not_lindelof E⟩

end
end D10Topology.Ch08.CofinitePoint
