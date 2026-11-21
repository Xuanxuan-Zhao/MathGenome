import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CocountableCountability
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions

/-! The cocountable example of paper.tex, d10:08:cocountable.
No representation of the underlying uncountable type by the real line is used.
Countable intersections of nonempty open sets have countable complements;
this rules out both singleton G_delta sets and countable local bases. -/

open Set TopologicalSpace
open scoped Topology
universe u
namespace D10Topology.Ch08

open Ch01

theorem cocountable_t1 (X : Type u) : @T1Space X (cocountableTopology X) := by
  let := cocountableTopology X
  exact { t1 := fun x => cocountable_countable_closed X {x} (countable_singleton x) }

theorem cocountable_lindelof (X : Type u) :
    @LindelofSpace X (cocountableTopology X) := by
  classical
  let := cocountableTopology X
  rcases isEmpty_or_nonempty X with hX | hX
  · infer_instance
  obtain ⟨x₀⟩ := hX
  apply (lindelof_iff_countable_subcover).mpr
  intro ι U ho hc
  have hex : ∀ x : X, ∃ i, x ∈ U i := fun x => mem_iUnion.mp (hc.symm ▸ mem_univ x)
  choose f hf using hex
  have hcount : (U (f x₀))ᶜ.Countable := by
    exact (ho (f x₀) : (U (f x₀)).Nonempty → _ ) ⟨x₀, hf x₀⟩
  refine ⟨insert (f x₀) (f '' (U (f x₀))ᶜ), (hcount.image f).insert _, ?_⟩
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ U (f x₀)
  · exact mem_iUnion₂.mpr ⟨f x₀, mem_insert _ _, hx⟩
  · exact mem_iUnion₂.mpr ⟨f x, mem_insert_of_mem _ (mem_image_of_mem f hx), hf x⟩

theorem cocountable_not_separable (X : Type u) (hX : ¬ (univ : Set X).Countable) :
    ¬ @SeparableSpace X (cocountableTopology X) := by
  let := cocountableTopology X
  intro hs
  obtain ⟨D, hD, hd⟩ := hs.exists_countable_dense
  have heq : D = univ := (cocountable_countable_closed X D hD).closure_eq.symm.trans hd.closure_eq
  exact hX (heq ▸ hD)

/-- A countable intersection of nonempty cocountable opens is co-countable. -/
theorem cocountable_iInter_complement_countable {X : Type u} (U : ℕ → Set X)
    (ho : ∀ n, IsOpen[cocountableTopology X] (U n))
    (hne : ∀ n, (U n).Nonempty) : (⋂ n, U n)ᶜ.Countable := by
  rw [compl_iInter]
  exact countable_iUnion (fun n => ho n (hne n))

theorem cocountable_singleton_not_gdelta (X : Type u)
    (hX : ¬ (univ : Set X).Countable) (x : X) :
    ¬ @IsGδ X (cocountableTopology X) ({x} : Set X) := by
  let := cocountableTopology X
  intro hg
  obtain ⟨U, ho, heq⟩ := isGδ_iff_eq_iInter_nat.mp hg
  have hx : ∀ n, x ∈ U n := fun n =>
    mem_iInter.mp (heq ▸ mem_singleton x) n
  have hc := cocountable_iInter_complement_countable U ho (fun n => ⟨x, hx n⟩)
  rw [← heq] at hc
  apply hX
  simpa only [union_compl_self] using (countable_singleton x).union hc

theorem cocountable_not_firstCountable (X : Type u)
    (hX : ¬ (univ : Set X).Countable) : ¬ FirstCountable (cocountableTopology X) := by
  classical
  let := cocountableTopology X
  intro hf
  have hn : Nonempty X := by
    by_contra h
    have : IsEmpty X := not_nonempty_iff.mp h
    exact hX (to_countable univ)
  obtain ⟨x⟩ := hn
  obtain ⟨U, _, ho, hbase⟩ := (firstCountable_iff_decreasing_open_localBases).mp hf x
  apply cocountable_singleton_not_gdelta X hX x
  apply isGδ_iff_eq_iInter_nat.mpr
  refine ⟨U, ho, ?_⟩
  ext y
  constructor
  · intro hy
    have hyx : y = x := mem_singleton_iff.mp hy
    subst y
    exact mem_iInter.mpr fun n => neighborhood_contains _ x (U n)
      (hbase.1 _ (mem_range_self n))
  · intro hy
    by_contra hne
    have hxy : x ∈ ({y} : Set X)ᶜ := by simpa only [mem_compl_iff, mem_singleton_iff] using Ne.symm hne
    have hopen : IsOpen ({y} : Set X)ᶜ :=
      (cocountable_countable_closed X {y} (countable_singleton y)).isOpen_compl
    obtain ⟨V, ⟨n, rfl⟩, hV⟩ := hbase.2 ({y}ᶜ) ⟨_, hopen, hxy, Subset.rfl⟩
    exact hV (mem_iInter.mp hy n) (mem_singleton y)

end D10Topology.Ch08
