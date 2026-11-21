import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.SubgraphCavalieri
import MathGenome.Internal.RealAnalysis.D11.Ch08.CompletedProduct
import MathGenome.Internal.RealAnalysis.D11.Ch08.EuclideanProductCompletion

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Specs.D11.Ch02.Completion
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch08.SubgraphCavalieri
open D11.Ch03 D11.Ch08.EuclideanProductCompletion

universe u v
namespace D11.Ch08.SubgraphCavalieri

/-- Canonical coordinate equivalence from the existing Euclidean line. -/
abbrev realCoordinate : Point 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.funUnique (Fin 1) ℝ)

lemma realCoordinate_measurePreserving : MeasurePreserving realCoordinate
    (borelMeasure_value 1) (volume : Measure ℝ) :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 1))

theorem real_borel_identification :
    Specs.D11.Ch08.SubgraphCavalieri.real_borel_identification :=
  realCoordinate_measurePreserving.map_eq

theorem real_completion_identification :
    Specs.D11.Ch08.SubgraphCavalieri.real_completion_identification := by
  intro A
  have hiff : NullMeasurableSet A (volume : Measure ℝ) ↔
      NullMeasurableSet (realCoordinate ⁻¹' A) (borelMeasure_value 1) := by
    constructor
    · intro hA
      exact hA.preimage realCoordinate_measurePreserving.quasiMeasurePreserving
    · intro hA
      have h := hA.preimage (realCoordinate_measurePreserving.symm
        realCoordinate).quasiMeasurePreserving
      simpa only [preimage_preimage, realCoordinate.apply_symm_apply, preimage_id'] using h
  have hiff' : MeasurableSet[completedSpace_value (volume : Measure ℝ)] A ↔
      MeasurableSet[lebesgueSpace_value 1] (realCoordinate ⁻¹' A) := by
    rw [D11.Ch03.LebesgueCompletion.completion_space 1]
    exact hiff
  refine ⟨hiff', fun hA => ?_⟩
  change completedMeasure_value (volume : Measure ℝ) A =
    lebesgue_value 1 (realCoordinate ⁻¹' A)
  rw [D11.Ch03.LebesgueCompletion.completion_value 1 _ (hiff'.mp hA)]
  exact (realCoordinate_measurePreserving.measure_preimage_emb
    realCoordinate.measurableEmbedding A).symm

lemma strictSubgraph_measurable {X : Type u} [MeasurableSpace X]
    (f : X → ℝ≥0∞) (hf : Measurable f) : MeasurableSet (strictSubgraph f) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      (hf.comp measurable_fst))

/-- The vertical section has exactly its extended height as length. -/
lemma vertical_length (a : ℝ≥0∞) :
    volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = a := by
  by_cases ha : a = ∞
  · subst a
    have he : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ∞} = Ioi 0 := by
      ext t
      simp only [mem_ofPred_eq, ENNReal.ofReal_lt_top, and_true, mem_Ioi]
    rw [he, Real.volume_Ioi]
  · have he : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨ht, hta⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mp hta⟩
      · rintro ⟨ht, hta⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hta⟩
    rw [he, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

theorem borel_subgraph : Specs.D11.Ch08.SubgraphCavalieri.borel_subgraph.{u} := by
  intro X m μ _ f hf
  have hm := strictSubgraph_measurable f hf
  refine ⟨hm, ?_⟩
  rw [D11.Ch05.NonnegativeIntegral.eq_lintegral μ f hf, Measure.prod_apply hm]
  exact lintegral_congr fun x => vertical_length (f x)

lemma borel_le_completed_real_product {X : Type u} [m : MeasurableSpace X] :
    (inferInstance : MeasurableSpace (X × ℝ)) ≤
      m.prod (completedSpace_value (volume : Measure ℝ)) :=
  sup_le_sup le_rfl (MeasurableSpace.comap_mono
    (D11.Ch08.CompletedProduct.original_le_completion (volume : Measure ℝ)))

/-- Agreement of the ordinary completed-real-factor product on the entire
original product domain. This does not assert completeness of that product. -/
lemma completed_real_product_restriction {X : Type u} [m : MeasurableSpace X]
    (μ : Measure X) (E : Set (X × ℝ)) (hE : MeasurableSet E) :
    (@Measure.prod X ℝ m (completedSpace_value (volume : Measure ℝ)) μ
      (completedMeasure_value (volume : Measure ℝ))) E =
        (μ.prod (volume : Measure ℝ)) E := by
  let ν := completedMeasure_value (volume : Measure ℝ)
  have hEc := borel_le_completed_real_product E hE
  let h := D11.Ch08.CompletedProduct.original_le_completion (volume : Measure ℝ)
  let : SigmaFinite (ν.trim h) := by
    change SigmaFinite ((completedMeasure_value (volume : Measure ℝ)).trim h)
    rw [D11.Ch08.CompletedProduct.completion_trim]
    infer_instance
  let : @SigmaFinite ℝ (completedSpace_value (volume : Measure ℝ)) ν :=
    SigmaFinite.of_trim h
  exact (@Measure.prod_apply X ℝ m (completedSpace_value (volume : Measure ℝ))
    μ ν inferInstance E hEc).trans (Measure.prod_apply hE).symm

theorem completed_factor_subgraph :
    Specs.D11.Ch08.SubgraphCavalieri.completed_factor_subgraph.{u} := by
  intro X m μ hμ f hf
  have h := borel_subgraph μ hμ f hf
  exact ⟨borel_le_completed_real_product _ h.1,
    (completed_real_product_restriction μ _ h.1).trans h.2⟩

/-- A completed-product set has measurable sections almost everywhere when
the second factor is complete, and its raw section masses have a measurable
version. No claim about every section is made. -/
lemma sections_of_nullMeasurableSet {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite ν] [ν.IsComplete] (S : Set (X × Y))
    (hS : NullMeasurableSet S (μ.prod ν)) :
    (∀ᵐ x ∂μ, MeasurableSet (Prod.mk x ⁻¹' S)) ∧
      AEMeasurable (fun x => ν (Prod.mk x ⁻¹' S)) μ := by
  obtain ⟨T, hT, hST⟩ := hS
  have hae := ae_ae_of_ae_prod hST
  constructor
  · filter_upwards [hae] with x hx
    have hx' : (Prod.mk x ⁻¹' S) =ᵐ[ν] (Prod.mk x ⁻¹' T) := hx
    have ht : NullMeasurableSet (Prod.mk x ⁻¹' T) ν :=
      (hT.preimage measurable_prodMk_left).nullMeasurableSet
    exact (ht.congr hx'.symm).measurable_of_complete
  · have hm : Measurable (fun x => ν (Prod.mk x ⁻¹' T)) :=
      measurable_measure_prodMk_left hT
    apply hm.aemeasurable.congr
    filter_upwards [hae] with x hx
    have hx' : (Prod.mk x ⁻¹' S) =ᵐ[ν] (Prod.mk x ⁻¹' T) := hx
    exact (measure_congr hx').symm

theorem cavalieri : Specs.D11.Ch08.SubgraphCavalieri.cavalieri := by
  classical
  intro m n _ _ E hE
  let S : Set (Point m × Point n) := (coordinates m n).symm ⁻¹' E
  have hS : MeasurableSet[completedSpace_value (m :=
      Specs.D11.Ch08.EuclideanProductCompletion.factorSpace m n)
      (Specs.D11.Ch08.EuclideanProductCompletion.factorProduct m n)] S := by
    rw [factor_completion_space m n]
    exact ⟨E, hE, rfl⟩
  have hmass := factor_completion_value m n S hS
  have himage : (coordinates m n).symm '' S = E :=
    (coordinates m n).symm.surjective.image_preimage E
  rw [himage] at hmass
  let : MeasurableSpace (Point m) := lebesgueSpace_value m
  let : MeasurableSpace (Point n) := lebesgueSpace_value n
  let μ : Measure (Point m) := lebesgue_value m
  let ν : Measure (Point n) := lebesgue_value n
  let : SigmaFinite μ := D11.Ch03.LebesgueMeasures.lebesgue_sigmaFinite m
  let : SigmaFinite ν := D11.Ch03.LebesgueMeasures.lebesgue_sigmaFinite n
  let : μ.IsComplete := D11.Ch03.LebesgueMeasures.lebesgue_complete m
  let : ν.IsComplete := D11.Ch03.LebesgueMeasures.lebesgue_complete n
  have hSn : NullMeasurableSet S (μ.prod ν) := hS
  obtain ⟨hae, ha⟩ := sections_of_nullMeasurableSet μ ν S hSn
  have heq : sectionMass m n E =ᵐ[μ] (fun x => ν (Prod.mk x ⁻¹' S)) := by
    filter_upwards [hae] with x hx
    change (if MeasurableSet (euclideanSection m n E x) then _ else 0) = _
    exact ite_eq_left hx
  have hm : Measurable (sectionMass m n E) :=
    aemeasurable_iff_measurable.mp (ha.congr heq.symm)
  refine ⟨hae, hm, ?_⟩
  rw [D11.Ch05.NonnegativeIntegral.eq_lintegral μ _ hm]
  exact hmass.symm.trans ((Measure.prod_apply₀ hSn).trans (lintegral_congr_ae heq.symm))

end D11.Ch08.SubgraphCavalieri
