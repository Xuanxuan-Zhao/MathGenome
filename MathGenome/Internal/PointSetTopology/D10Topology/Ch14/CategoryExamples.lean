import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryExamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.BaireSubspaces
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.MetricBaire
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.SumsAndFinalTopologies
import Mathlib.Topology.Baire.BaireMeasurable

/-! Category examples in the usual real line, the rationals with their
induced metric topology, one-point subspaces, and the actual disjoint sum. -/

open Set Topology
namespace D10Topology.Ch14

/-- Countable subsets of a T₁ space without isolated points are meager. -/
theorem countable_meager {X : Type*} [TopologicalSpace X] [T1Space X]
    [∀ x : X, Filter.NeBot (nhdsWithin x ({x}ᶜ))] (A : Set X) (hc : A.Countable) : MeagerIn A := by
  apply (meager_iff_library A).mpr
  rw [← biUnion_of_singleton A]
  exact isMeagre_biUnion hc fun x _ =>
    ((isClosed_singleton : IsClosed ({x} : Set X)).isNowhereDense_iff.mpr
      (interior_singleton x)).isMeagre

theorem real_baire : BaireIn ℝ := by
  exact complete_metric_baire Real.metricSpace
    ((Ch09.sequentiallyComplete_iff_mathlib _).mpr inferInstance)

theorem rationals_dense_meager :
    Dense (range (Rat.cast : ℚ → ℝ)) ∧
      MeagerIn (range (Rat.cast : ℚ → ℝ)) ∧
      ¬ ResidualIn (range (Rat.cast : ℚ → ℝ)) := by
  have hm := countable_meager (range (Rat.cast : ℚ → ℝ)) (countable_range _)
  refine ⟨Rat.denseRange_cast, hm, ?_⟩
  let : BaireSpace ℝ := (baire_iff_library ℝ).mp real_baire
  intro hr
  exact not_isMeagre_of_mem_residual ((residual_iff_library _).mp hr)
    ((meager_iff_library _).mp hm)

theorem irrationals_residual : ResidualIn {x : ℝ | Irrational x} := by
  exact (residual_iff_library _).mpr eventually_residual_irrational

theorem irrationals_baire : BaireIn {x : ℝ // Irrational x} := by
  exact dense_gdelta_subspace_baire real_baire _ .setOfPred_irrational dense_irrational

theorem rational_singletons (q : ℚ) :
    IsClosed ({q} : Set ℚ) ∧ interior ({q} : Set ℚ) = ∅ :=
  ⟨isClosed_singleton, interior_singleton q⟩

theorem rationals_meager_self : MeagerIn (univ : Set ℚ) :=
  countable_meager univ (to_countable _)

theorem rationals_empty_residual_not_dense :
    ResidualIn (∅ : Set ℚ) ∧ ¬ Dense (∅ : Set ℚ) := by
  constructor
  · simpa only [ResidualIn, compl_empty] using rationals_meager_self
  · intro hd
    simpa using hd (0 : ℚ)

theorem singleton_ambient_intrinsic (x : ℝ) :
    NowhereDenseIn ({x} : Set ℝ) ∧
      SecondCategoryIn (univ : Set ({x} : Set ℝ)) := by
  constructor
  · exact isClosed_singleton.isNowhereDense_iff.mpr (interior_singleton x)
  · let : BaireSpace ({x} : Set ℝ) := baire_of_finite
    exact (secondCategory_iff_library _).mpr
      (not_isMeagre_of_isOpen isOpen_univ ⟨⟨x, rfl⟩, mem_univ _⟩)

theorem real_rat_sum_opens (U : Set (ℝ ⊕ ℚ)) :
    IsOpen U ↔ IsOpen (Sum.inl ⁻¹' U) ∧ IsOpen (Sum.inr ⁻¹' U) :=
  isOpen_sum_iff

theorem real_rat_sum_second_category_not_baire :
    Nonempty (ℝ ⊕ ℚ) ∧ SecondCategoryIn (univ : Set (ℝ ⊕ ℚ)) ∧
      ¬ BaireIn (ℝ ⊕ ℚ) := by
  refine ⟨⟨Sum.inl 0⟩, ?_, ?_⟩
  · intro hm
    have hmR : IsMeagre (univ : Set ℝ) := by
      simpa using IsMeagre.preimage_of_isOpenMap
        (continuous_inl : Continuous (Sum.inl : ℝ → ℝ ⊕ ℚ)) isOpenMap_inl
        ((meager_iff_library _).mp hm)
    exact ((baire_iff_no_open_meager ℝ).mp real_baire univ isOpen_univ
      ⟨0, mem_univ _⟩) ((meager_iff_library _).mpr hmR)
  · intro hb
    have hmQ : MeagerIn (range (Sum.inr : ℚ → ℝ ⊕ ℚ)) := by
      apply (meager_iff_library _).mpr
      simpa using (IsEmbedding.inr.isInducing.isMeagre_image
        ((meager_iff_library _).mp rationals_meager_self) :
        IsMeagre ((Sum.inr : ℚ → ℝ ⊕ ℚ) '' univ))
    exact ((baire_iff_no_open_meager _).mp hb _ isOpen_range_inr
      ⟨Sum.inr 0, mem_range_self _⟩) hmQ

theorem no_countable_dense_gdelta (D : Set ℝ) (hc : D.Countable) (hd : Dense D) :
    ¬ IsGδ D := by
  let : BaireSpace ℝ := (baire_iff_library ℝ).mp real_baire
  intro hg
  exact not_isMeagre_of_isGδ_of_dense hg hd
    ((meager_iff_library _).mp (countable_meager D hc))

end D10Topology.Ch14
