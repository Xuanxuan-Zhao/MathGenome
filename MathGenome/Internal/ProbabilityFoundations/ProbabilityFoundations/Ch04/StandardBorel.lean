import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.StandardBorel

namespace ProbabilityFoundations.Ch04

open Set MeasureTheory TopologicalSpace

universe u v

/-- A measurable space is standard Borel in the sense of §4.1 of the source. -/
def IsStandardBorel (T : Type u) [MeasurableSpace T] : Prop :=
  Specs.StandardBorelValue T

/-- Transport a compatible Polish topology along a measurable isomorphism. -/
theorem standardBorelSpace_of_measurableEquiv {T : Type u} {S : Type v}
    [mT : MeasurableSpace T] [MeasurableSpace S] [StandardBorelSpace S]
    (e : T ≃ᵐ S) : StandardBorelSpace T := by
  let := upgradeStandardBorel S
  let : TopologicalSpace T := TopologicalSpace.induced e inferInstance
  have : PolishSpace T := e.toEquiv.polishSpace_induced
  have : BorelSpace T := ⟨by
    rw [borel_comap, ← BorelSpace.measurable_eq]
    exact e.measurableEmbedding.comap_eq.symm⟩
  infer_instance

/-- The source definition agrees with Mathlib on the specified sigma-algebra. -/
theorem isStandardBorel_iff (T : Type u) [mT : MeasurableSpace T] :
    IsStandardBorel T ↔ StandardBorelSpace T := by
  constructor
  · rintro ⟨M, d, hc, hs, B, hB, ⟨e⟩⟩
    let := d
    let := hc
    let := hs
    let : MeasurableSpace M := borel M
    have : BorelSpace M := ⟨rfl⟩
    have : StandardBorelSpace B := hB.standardBorel
    exact standardBorelSpace_of_measurableEquiv e
  · intro h
    let := h
    let := upgradeStandardBorel T
    let := upgradeIsCompletelyMetrizable T
    refine ⟨T, inferInstance, inferInstance, inferInstance, univ, MeasurableSet.univ, ?_⟩
    have hm : mT = borel T := BorelSpace.measurable_eq
    change Nonempty (@MeasurableEquiv T (univ : Set T) mT
      (MeasurableSpace.comap Subtype.val (borel T)))
    rw [← hm]
    exact ⟨(MeasurableEquiv.Set.univ T).symm⟩

/-- Coding by a Borel subset of the real line; no nonemptiness assumption is needed. -/
theorem exists_real_coding (T : Type u) [MeasurableSpace T] (hT : IsStandardBorel T) :
    ∃ B : Set ℝ, MeasurableSet B ∧ Nonempty (T ≃ᵐ B) := by
  let := (isStandardBorel_iff T).mp hT
  exact exists_subset_real_measurableEquiv T

/-- Pulling back rational lower half-lines and adjoining the empty set and the
entire space gives a countable generating family closed under all binary intersections.
We state the full closure explicitly, since Mathlib's `IsPiSystem` only requires it
for non-disjoint pairs. -/
theorem exists_countable_generating_piSystem (T : Type u) [mT : MeasurableSpace T]
    (hT : IsStandardBorel T) :
    ∃ C : Set (Set T), C.Countable ∧ IsPiSystem C ∧
      (∀ A ∈ C, ∀ B ∈ C, A ∩ B ∈ C) ∧ univ ∈ C ∧
      MeasurableSpace.generateFrom C = mT := by
  let := (isStandardBorel_iff T).mp hT
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real T
  let D : Set (Set ℝ) := ⋃ q : ℚ, {Iic (q : ℝ)}
  let C := insert ∅ (insert univ ((fun s ↦ f ⁻¹' s) '' D))
  have hpi : IsPiSystem C := (Real.isPiSystem_Iic_rat.comap f).insert_univ.insert_empty
  refine ⟨C, ?_, hpi, ?_, ?_, ?_⟩
  · exact (((countable_iUnion fun q : ℚ ↦ countable_singleton (Iic (q : ℝ))).image _).insert _).insert _
  · intro A hA B hB
    by_cases hAB : (A ∩ B).Nonempty
    · exact hpi A hA B hB hAB
    · rw [Set.not_nonempty_iff_eq_empty.mp hAB]
      exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_insert _ _)
  · rw [MeasurableSpace.generateFrom_insert_empty, MeasurableSpace.generateFrom_insert_univ,
      ← MeasurableSpace.comap_generateFrom, ← Real.borel_eq_generateFrom_Iic_rat]
    exact hf.comap_eq

/-- Finite products carry the product sigma-algebra. This includes an empty index type. -/
theorem finite_products (ι : Type v) [Finite ι] (T : ι → Type u)
    [∀ i, MeasurableSpace (T i)] (hT : ∀ i, IsStandardBorel (T i)) :
    IsStandardBorel (∀ i, T i) := by
  have : ∀ i, StandardBorelSpace (T i) := fun i ↦ (isStandardBorel_iff (T i)).mp (hT i)
  exact (isStandardBorel_iff (∀ i, T i)).mpr inferInstance

end ProbabilityFoundations.Ch04
