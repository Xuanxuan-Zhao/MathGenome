import MathGenome.Internal.RealAnalysis.D11.Ch19.RecoverOpenCompactMass
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.RadonCaratheodoryLocalization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The outer values of the full splitting extension equal those of the original
Borel measure. Regularity consequently transfers to that extension, and native
finite-set inner approximation applies on its full domain. For compact testing,
first exhaust each finite-mass open set by compacts modulo a null remainder.
Then every finite-outer-mass splitting test lies in one such open set.
-/
open Set MeasureTheory
open scoped ENNReal
namespace D11.Ch20.RadonCaratheodoryLocalization
universe u
noncomputable section

abbrev outerMeasure :
    Specs.D11.Ch20.RadonCaratheodoryLocalization.outerMeasure_type.{u} :=
  @Specs.D11.Ch20.RadonCaratheodoryLocalization.outerMeasure_value.{u}
abbrev measurableSpace :
    Specs.D11.Ch20.RadonCaratheodoryLocalization.measurableSpace_type.{u} :=
  @Specs.D11.Ch20.RadonCaratheodoryLocalization.measurableSpace_value.{u}
abbrev measure :
    Specs.D11.Ch20.RadonCaratheodoryLocalization.measure_type.{u} :=
  @Specs.D11.Ch20.RadonCaratheodoryLocalization.measure_value.{u}

variable {X : Type u} [TopologicalSpace X]

theorem borel_measurable (μ : @Measure X (borel X)) :
    borel X ≤ measurableSpace μ :=
  @le_toOuterMeasure_caratheodory X (borel X) μ

/-- Agreement of outer values on every subset; this does not enlarge the
original Borel sigma-algebra. -/
theorem measure_apply (μ : @Measure X (borel X)) (A : Set X) :
    measure μ A = μ A := by
  letI : MeasurableSpace X := borel X
  apply le_antisymm
  · calc
      measure μ A ≤ measure μ (@toMeasurable X (borel X) μ A) :=
        (measure μ).mono (subset_toMeasurable μ A)
      _ = μ (@toMeasurable X (borel X) μ A) :=
        Ch02.Caratheodory.measure_apply (outerMeasure μ) _
          (borel_measurable μ _ (measurableSet_toMeasurable μ A))
      _ = μ A := measure_toMeasurable A
  · exact @le_toMeasure_apply X (measurableSpace μ) (outerMeasure μ) le_rfl A

theorem complete (μ : @Measure X (borel X)) :
    @Measure.IsComplete X (measurableSpace μ) (measure μ) :=
  Ch02.Caratheodory.measure_isComplete (outerMeasure μ)

variable [T2Space X] [LocallyCompactSpace X]

theorem outerMeasure_formula (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (A : Set X) :
    outerMeasure μ A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), μ U := by
  letI : MeasurableSpace X := borel X
  letI : Measure.Regular μ := (Ch18.isRadon_iff_regular μ).mp hμ
  exact A.measure_eq_iInf_isOpen μ

/-- The functional is the actual absolutely convergent integral on Cc. -/
theorem content_agreement (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ) :
    ∃ I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ,
      ∃ hI : Specs.D11.Ch19.PositiveContentOuterMeasure.Positive I,
      (letI : MeasurableSpace X := borel X
       ∀ f : CompactlySupportedContinuousMap X ℝ,
         Integrable f μ ∧ I f = ∫ x, f x ∂μ) ∧
      outerMeasure μ = Ch19.PositiveContentOuterMeasure.outerMeasure I hI := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : IsFiniteMeasureOnCompacts μ := (Ch18.compactFinite_iff μ).mp hμ.1
  obtain ⟨I, hI, hrep⟩ := Ch19.PositiveRieszMarkov.radon_induces_real_functional μ hμ
  refine ⟨I, hI, ?_, ?_⟩
  · intro f
    obtain ⟨hf, heq⟩ := hrep.2 f
    exact ⟨f.integrable, heq⟩
  · have heq := Ch19.RecoverOpenCompactMass.representing_measure_eq I hI μ hrep
    change μ.toOuterMeasure =
      (Ch19.PositiveContentOuterMeasure.borelMeasure I hI).toOuterMeasure
    exact congrArg Measure.toOuterMeasure heq

/-- Transfer regularity to the full splitting domain, not to a mere ordinary
completion. Only open masses and outer values are used. -/
lemma extension_regular (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ) :
    @Measure.Regular X (measurableSpace μ) _ (measure μ) := by
  letI : MeasurableSpace X := measurableSpace μ
  refine {
    lt_top_of_isCompact := fun K hK => ?_
    outerRegular := fun {A} _ r hr => ?_
    innerRegular := ?_
  }
  · rw [measure_apply]
    exact hμ.1 K hK
  · letI : MeasurableSpace X := borel X
    letI : Measure.Regular μ := (Ch18.isRadon_iff_regular μ).mp hμ
    rw [measure_apply] at hr
    obtain ⟨U, hAU, hU, hrU⟩ := A.exists_isOpen_lt_of_lt r hr
    exact ⟨U, hAU, hU, by rw [measure_apply]; exact hrU⟩
  · intro U hU r hr
    rw [measure_apply, hμ.2.2 U hU] at hr
    obtain ⟨K, hKU, hK, hrK⟩ : ∃ K, K ⊆ U ∧ IsCompact K ∧ r < μ K := by
      simpa only [lt_iSup_iff, exists_prop] using hr
    exact ⟨K, hKU, hK, by rw [measure_apply]; exact hrK⟩

theorem finite_inner_regular (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (A : Set X) (hA : MeasurableSet[measurableSpace μ] A)
    (hfin : measure μ A < ∞) :
    measure μ A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), measure μ K := by
  letI : MeasurableSpace X := measurableSpace μ
  letI : Measure.Regular (measure μ) := extension_regular μ hμ
  exact hA.measure_eq_iSup_isCompact_of_ne_top hfin.ne

/-- Compact tests make every intersection with a finite-mass open measurable.
The compact approximants may depend on that open set. -/
lemma measurable_inter_finite_open (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (B : Set X) (hB : ∀ K : Set X, IsCompact K →
      MeasurableSet[measurableSpace μ] (B ∩ K))
    (U : Set X) (hU : IsOpen U) (hfin : measure μ U < ∞) :
    MeasurableSet[measurableSpace μ] (B ∩ U) := by
  letI : MeasurableSpace X := measurableSpace μ
  letI : OpensMeasurableSpace X := ⟨borel_measurable μ⟩
  letI : Measure.Regular (measure μ) := extension_regular μ hμ
  letI : (measure μ).IsComplete := complete μ
  have hex (n : ℕ) : ∃ K : Set X, K ⊆ U ∧ IsCompact K ∧
      measure μ (U \ K) < (1 / 2 : ℝ≥0∞) ^ n :=
    hU.measurableSet.exists_isCompact_sdiff_lt hfin.ne (pow_ne_zero n (by norm_num))
  choose K hKU hK herror using hex
  let S : Set X := ⋃ n, B ∩ K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n => hB (K n) (hK n)
  have hSU : S ⊆ B ∩ U := iUnion_subset fun n =>
    inter_subset_inter_right B (hKU n)
  have hN : measure μ ((B ∩ U) \ S) = 0 := by
    apply le_antisymm ?_ bot_le
    apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
    apply Filter.Eventually.of_forall
    intro n
    refine (measure_mono ?_).trans (herror n).le
    intro x hx
    refine ⟨hx.1.2, fun hxK => hx.2 ?_⟩
    exact mem_iUnion.mpr ⟨n, hx.1.1, hxK⟩
  have hNm : MeasurableSet ((B ∩ U) \ S) := measurableSet_of_null hN
  have heq : S ∪ ((B ∩ U) \ S) = B ∩ U := by
    ext x
    constructor
    · intro hx
      exact hx.elim (fun h => hSU h) (fun h => h.1)
    · intro hx
      by_cases hs : x ∈ S
      · exact Or.inl hs
      · exact Or.inr ⟨hx, hs⟩
  rw [← heq]
  exact hS.union hNm

/-- Exact compact-testing criterion for the full Carathéodory sigma-algebra. -/
theorem local_measurable_iff (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (B : Set X) :
    MeasurableSet[measurableSpace μ] B ↔
      ∀ K : Set X, IsCompact K → MeasurableSet[measurableSpace μ] (B ∩ K) := by
  constructor
  · intro hB K hK
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    exact @MeasurableSet.inter X (measurableSpace μ) B K hB
      (borel_measurable μ _ hK.isClosed.measurableSet)
  · intro hB
    apply (Ch02.Caratheodory.isMeasurable_iff_finite (outerMeasure μ) B).mpr
    intro A hA
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    letI : Measure.Regular μ := (Ch18.isRadon_iff_regular μ).mp hμ
    obtain ⟨U, hAU, hU, hUfin⟩ := A.exists_isOpen_lt_of_lt ∞ hA
    have hBU := measurable_inter_finite_open μ hμ B hB U hU
      (by rw [measure_apply]; exact hUfin)
    have hsplit := hBU A
    have hAi : A ∩ (B ∩ U) = A ∩ B := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, hAU hx.1⟩⟩
    have hAd : A \ (B ∩ U) = A \ B := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, fun hxB => hx.2 ⟨hxB, hAU hx.1⟩⟩
      · intro hx
        exact ⟨hx.1, fun hxBU => hx.2 hxBU.1⟩
    rw [hAi, hAd] at hsplit
    exact hsplit.ge

end
end D11.Ch20.RadonCaratheodoryLocalization
