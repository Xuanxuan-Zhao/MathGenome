import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction

/-!
Finite-measure exhaustions and restriction (paper.tex:283–295, 326–341).
All objects use the shared native measure and the shared subtype trace space.
The type `Measure E` supplies the empty-set and countable-additivity laws on
that trace space; the evaluation lemmas identify it with the source formula.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch01.ExhaustionRestriction

theorem sigmaFinite_iff_disjoint_partition {α : Type u} [MeasurableSpace α]
    (μ : Measure α) :
    SigmaFinite μ ↔ ∃ D : ℕ → Set α,
      (∀ n, MeasurableSet (D n) ∧ μ (D n) < ∞) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧ (⋃ n, D n) = univ := by
  constructor
  · intro hμ
    let : SigmaFinite μ := hμ
    refine ⟨disjointed (spanningSets μ), fun n => ⟨?_, ?_⟩,
      disjoint_disjointed _, ?_⟩
    · exact MeasurableSet.disjointed (measurableSet_spanningSets μ) n
    · exact (measure_mono (disjointed_subset _ n)).trans_lt
        (measure_spanningSets_lt_top μ n)
    · rw [iUnion_disjointed, iUnion_spanningSets]
  · rintro ⟨D, hD, _, hU⟩
    exact (MeasureDefinitions.sigmaFinite_iff μ).mpr ⟨D, hD, hU⟩

theorem sigmaFinite_iff_increasing_exhaustion {α : Type u} [MeasurableSpace α]
    (μ : Measure α) :
    SigmaFinite μ ↔ ∃ F : ℕ → Set α,
      (∀ n, MeasurableSet (F n) ∧ μ (F n) < ∞) ∧
      Monotone F ∧ (⋃ n, F n) = univ := by
  constructor
  · intro hμ
    let : SigmaFinite μ := hμ
    exact ⟨spanningSets μ, fun n => ⟨measurableSet_spanningSets μ n,
      measure_spanningSets_lt_top μ n⟩, monotone_spanningSets μ, iUnion_spanningSets μ⟩
  · rintro ⟨F, hF, _, hU⟩
    exact (MeasureDefinitions.sigmaFinite_iff μ).mpr ⟨F, hF, hU⟩

/-- Restriction as a measure on the original measurable space. -/
noncomputable def restrictOnSpace {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) : Measure α := μ.restrict E

/-- Restriction as a measure on the trace measurable space E.
Its source interpretation is used with measurable E, as in the lemmas below. -/
noncomputable def restrictToSubtype {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) : Measure E := μ.comap (Subtype.val : E → α)

theorem restrictOnSpace_apply {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (_hE : MeasurableSet E)
    (A : Set α) (hA : MeasurableSet A) :
    restrictOnSpace μ E A = μ (A ∩ E) :=
  Measure.restrict_apply hA

theorem restrictToSubtype_apply {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (hE : MeasurableSet E)
    (B : Set E) (_hB : MeasurableSet B) :
    restrictToSubtype μ E B = μ ((Subtype.val : E → α) '' B) :=
  comap_subtype_coe_apply hE μ B

theorem restrictToSubtype_apply_subset {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (hE : MeasurableSet E)
    (A : Set α) (hA : MeasurableSet A) (hAE : A ⊆ E) :
    restrictToSubtype μ E ((Subtype.val : E → α) ⁻¹' A) = μ A := by
  rw [restrictToSubtype_apply μ E hE _ (hA.preimage measurable_subtype_coe),
    Subtype.image_preimage_coe, inter_eq_right.mpr hAE]

theorem restriction_mass {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (hE : MeasurableSet E) :
    restrictOnSpace μ E univ = μ E ∧ restrictToSubtype μ E univ = μ E := by
  constructor
  · exact Measure.restrict_apply_univ E
  · rw [restrictToSubtype_apply μ E hE univ MeasurableSet.univ,
      image_univ, Subtype.range_coe]

theorem restriction_finite {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (_hE : MeasurableSet E) (hμ : IsFiniteMeasure μ) :
    IsFiniteMeasure (restrictOnSpace μ E) ∧
      IsFiniteMeasure (restrictToSubtype μ E) := by
  let : IsFiniteMeasure μ := hμ
  exact ⟨inferInstanceAs (IsFiniteMeasure (μ.restrict E)),
    inferInstanceAs (IsFiniteMeasure (μ.comap (Subtype.val : E → α)))⟩

theorem restriction_sigmaFinite {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (hE : MeasurableSet E) (hμ : SigmaFinite μ) :
    SigmaFinite (restrictOnSpace μ E) ∧
      SigmaFinite (restrictToSubtype μ E) := by
  let : SigmaFinite μ := hμ
  refine ⟨inferInstanceAs (SigmaFinite (μ.restrict E)), ?_⟩
  apply (MeasureDefinitions.sigmaFinite_iff (restrictToSubtype μ E)).mpr
  refine ⟨fun n => (Subtype.val : E → α) ⁻¹' spanningSets μ n, fun n => ⟨?_, ?_⟩, ?_⟩
  · exact (measurableSet_spanningSets μ n).preimage measurable_subtype_coe
  · rw [restrictToSubtype_apply μ E hE _
      ((measurableSet_spanningSets μ n).preimage measurable_subtype_coe),
      Subtype.image_preimage_coe]
    exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)
  · rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]

theorem map_restrictToSubtype {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (hE : MeasurableSet E) :
    (restrictToSubtype μ E).map (Subtype.val : E → α) = restrictOnSpace μ E :=
  map_comap_subtype_coe hE μ

end D11.Ch01.ExhaustionRestriction
