import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.NonuniqueExtensionExample
import MathGenome.Internal.RealAnalysis.D11.Ch03.BorelGenerators
import Mathlib.Order.Interval.Set.Infinite

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch02.NonuniqueExtensionExample

private lemma cell_empty : (∅ : Set ℝ) ∈ intervalFamily := Or.inl rfl
private lemma cell_univ : (univ : Set ℝ) ∈ intervalFamily := Or.inr (Or.inl rfl)
private lemma cell_Iic (b : ℝ) : Iic b ∈ intervalFamily :=
  Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))
private lemma cell_Ioi (a : ℝ) : Ioi a ∈ intervalFamily :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))
private lemma cell_Ioc (a b : ℝ) : Ioc a b ∈ intervalFamily := by
  by_cases h : a < b
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, h, rfl⟩)))
  · rw [Ioc_eq_empty h]
    exact cell_empty

/-- Intersections of elementary intervals remain elementary, allowing emptiness. -/
private lemma cell_inter {s t : Set ℝ} (hs : s ∈ intervalFamily)
    (ht : t ∈ intervalFamily) : s ∩ t ∈ intervalFamily := by
  rcases hs with rfl | rfl | ⟨b, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, _, rfl⟩
  · simpa using cell_empty
  · simpa using ht
  all_goals rcases ht with rfl | rfl | ⟨d, rfl⟩ | ⟨c, rfl⟩ | ⟨c, d, _, rfl⟩
  · simpa using cell_empty
  · simpa using cell_Iic b
  · simpa only [Iic_inter_Iic] using cell_Iic (min b d)
  · rw [inter_comm, Ioi_inter_Iic]
    exact cell_Ioc c b
  · rw [inter_comm, Ioc_inter_Iic]
    exact cell_Ioc _ _
  · simpa using cell_empty
  · simpa using cell_Ioi a
  · exact cell_Ioc a d
  · simpa only [Ioi_inter_Ioi] using cell_Ioi (max a c)
  · have heq : Ioi a ∩ Ioc c d = Ioc (max a c) d := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc, max_lt_iff]
      tauto
    rw [heq]
    exact cell_Ioc _ _
  · simpa using cell_empty
  · simpa using cell_Ioc a b
  · rw [Ioc_inter_Iic]
    exact cell_Ioc _ _
  · have heq : Ioc a b ∩ Ioi c = Ioc (max a c) b := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc, max_lt_iff]
      tauto
    rw [heq]
    exact cell_Ioc _ _
  · have heq : Ioc a b ∩ Ioc c d = Ioc (max a c) (min b d) := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
      tauto
    rw [heq]
    exact cell_Ioc _ _

private lemma cell_biInter {C : Set (Set ℝ)} (hC : C.Finite)
    (hc : ∀ t ∈ C, t ∈ intervalFamily) : (⋂ t ∈ C, t) ∈ intervalFamily := by
  induction C, hC using Set.Finite.induction_on with
  | empty => simpa using cell_univ
  | @insert t C ht hC ih =>
    rw [biInter_insert]
    exact cell_inter (hc t (mem_insert t C))
      (ih (fun u hu => hc u (mem_insert_of_mem t hu)))

theorem algebra_isSetAlgebra : Specs.D11.Ch02.NonuniqueExtensionExample.algebra_isSetAlgebra :=
  isSetAlgebra_generateSetAlgebra

private lemma cell_mem_algebra {s : Set ℝ} (hs : s ∈ intervalFamily) :
    s ∈ intervalAlgebra := by
  rcases hs with rfl | rfl | ⟨b, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, _, rfl⟩
  · exact algebra_isSetAlgebra.empty_mem
  · exact algebra_isSetAlgebra.univ_mem
  · exact self_subset_generateSetAlgebra (mem_range_self b)
  · rw [← compl_Iic]
    exact algebra_isSetAlgebra.compl_mem
      (self_subset_generateSetAlgebra (mem_range_self a))
  · rw [← Ioi_inter_Iic]
    apply algebra_isSetAlgebra.inter_mem
    · rw [← compl_Iic]
      exact algebra_isSetAlgebra.compl_mem
        (self_subset_generateSetAlgebra (mem_range_self a))
    · exact self_subset_generateSetAlgebra (mem_range_self b)

theorem algebra_description : Specs.D11.Ch02.NonuniqueExtensionExample.algebra_description := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨C, hC, hfin, hc, heq⟩ := mem_generateSetAlgebra_elim hs
    let f : Set (Set ℝ) → Set ℝ := fun c => ⋂ t ∈ c, t
    refine ⟨hC.toFinset.image f, ?_, ?_⟩
    · intro t ht
      obtain ⟨c, hcC, rfl⟩ := Finset.mem_image.mp ht
      have hcC' : c ∈ C := hC.mem_toFinset.mp hcC
      apply cell_biInter (hfin c hcC')
      intro u hu
      rcases hc c hcC' u hu with ⟨b, rfl⟩ | ⟨a, ha⟩
      · exact cell_Iic b
      · have he : u = Ioi a := by rw [← compl_compl u, ← ha, compl_Iic]
        rw [he]
        exact cell_Ioi a
    · simpa only [f, Finset.set_biUnion_finset_image, Set.Finite.mem_toFinset] using heq
  · rintro ⟨C, hc, rfl⟩
    exact algebra_isSetAlgebra.biUnion_mem C (fun t ht => cell_mem_algebra (hc t ht))

/-- The finite-union description retains a nondegenerate piece in every
nonempty member; in particular this algebra contains no singleton. -/
theorem nonempty_contains_interval :
    Specs.D11.Ch02.NonuniqueExtensionExample.nonempty_contains_interval := by
  intro s hs hne
  rw [algebra_description] at hs
  obtain ⟨C, hc, rfl⟩ := hs
  obtain ⟨x, hx⟩ := hne
  obtain ⟨t, htC, hxt⟩ := mem_iUnion₂.mp hx
  have hsub : t ⊆ ⋃ u ∈ C, u := subset_iUnion₂_of_subset t htC Subset.rfl
  rcases hc t htC with rfl | rfl | ⟨b, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact False.elim hxt
  · exact ⟨0, 1, by norm_num, (subset_univ _).trans hsub⟩
  · refine ⟨b - 1, b, by linarith, ?_⟩
    exact Ioc_subset_Iic_self.trans hsub
  · refine ⟨a, a + 1, by linarith, ?_⟩
    exact Ioc_subset_Ioi_self.trans hsub
  · exact ⟨a, b, hab, hsub⟩

theorem generated_eq_borel : Specs.D11.Ch02.NonuniqueExtensionExample.generated_eq_borel := by
  change MeasurableSpace.generateFrom (generateSetAlgebra (range (Iic : ℝ → Set ℝ))) = _
  rw [generateFrom_generateSetAlgebra_eq]
  exact D11.Ch03.BorelGenerators.real_left_closed_rays.symm

private lemma algebra_measurable {s : Set ℝ} (hs : s ∈ intervalAlgebra) :
    MeasurableSet s := by
  change MeasurableSet[borel ℝ] s
  rw [← generated_eq_borel]
  exact MeasurableSpace.measurableSet_generateFrom hs

/-- The lattice's top measure has the literal zero-or-infinity formula. -/
private lemma top_value (s : Set ℝ) :
    (⊤ : Measure ℝ) s = if s = ∅ then 0 else ∞ := by
  change (⊤ : OuterMeasure ℝ) s = _
  split_ifs with h
  · simp [h]
  · exact OuterMeasure.top_apply (nonempty_iff_ne_empty.mpr h)

theorem infinite_measure_values :
    Specs.D11.Ch02.NonuniqueExtensionExample.infinite_measure_values := by
  intro s _
  exact top_value s

private lemma value_eq_top (s : intervalAlgebra) :
    premeasureValue s = (⊤ : Measure ℝ) s.1 := (top_value s.1).symm

/-- Countable additivity is inherited from the everywhere-infinite measure;
no sigma-finiteness or finite-cost covering hypothesis is used. -/
theorem is_premeasure : Specs.D11.Ch02.NonuniqueExtensionExample.is_premeasure := by
  intro hA
  refine ⟨{ value := premeasureValue, empty := ?_, iUnion := ?_ }, rfl⟩
  · simp [premeasureValue]
  · intro E hU hd
    simp_rw [value_eq_top]
    exact measure_iUnion hd (fun n => algebra_measurable (E n).2)

theorem counting_extends : Specs.D11.Ch02.NonuniqueExtensionExample.counting_extends := by
  intro s
  by_cases h : s.1 = ∅
  · simp [premeasureValue, h]
  · obtain ⟨a, b, hab, hsub⟩ := nonempty_contains_interval s.1 s.2
      (nonempty_iff_ne_empty.mpr h)
    rw [Measure.count_apply_infinite ((Ioc_infinite hab).mono hsub)]
    simp [premeasureValue, h]

theorem infinite_extends : Specs.D11.Ch02.NonuniqueExtensionExample.infinite_extends := by
  intro s
  exact (value_eq_top s).symm

theorem singleton_values : Specs.D11.Ch02.NonuniqueExtensionExample.singleton_values := by
  intro x
  exact ⟨Measure.count_singleton x, by simp [top_value]⟩

theorem distinct_extensions : Specs.D11.Ch02.NonuniqueExtensionExample.distinct_extensions := by
  refine ⟨Measure.count, ⊤, ?_, ?_, singleton_values⟩
  · intro h
    have he : (1 : ℝ≥0∞) = ∞ :=
      (singleton_values 0).1.symm.trans ((congrArg (fun μ : Measure ℝ => μ {0}) h).trans
        (singleton_values 0).2)
    exact ENNReal.one_ne_top he
  · intro s
    exact ⟨counting_extends s, infinite_extends s⟩

end D11.Ch02.NonuniqueExtensionExample
