import MathGenome.Internal.RealAnalysis.D11.Ch14.TotalVariation
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.DensityMeasureVariation
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! Variation of a real or complex density, paper.tex:4723–4747.
The density measure is the canonical countably additive vector measure of set
integrals. Mathlib's variation theorem identifies its partition variation with
the integral of the norm on an arbitrary positive measure space. For real
densities the two nonnegative densities are mutually singular, and the shared
Jordan uniqueness theorem identifies the canonical parts. -/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch14.DensityMeasureVariation
open D11.Ch06.ScalarIntegral (scalarIntegrable scalarIntegrable_iff)
open D11.Ch14.TotalVariation D11.Ch14.Jordan

variable {X : Type u} [MeasurableSpace X]
variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

def densityMeasure (μ : Measure X) (h : X → 𝕜) (_ : scalarIntegrable μ h) :
    VectorMeasure X 𝕜 := μ.withDensityᵥ h

theorem densityMeasure_apply (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable μ h) (E : Set X) (hE : MeasurableSet E) :
    densityMeasure μ h hh E = ∫ x in E, h x ∂μ :=
  withDensityᵥ_apply ((scalarIntegrable_iff μ h).mp hh).2 hE

theorem densityMeasure_variation (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable μ h) :
    totalVariation (densityMeasure μ h hh) =
      μ.withDensity (fun x => ENNReal.ofReal ‖h x‖) := by
  simp_rw [ofReal_norm]
  exact Measure.variation_withDensityᵥ ((scalarIntegrable_iff μ h).mp hh).2

theorem densityMeasure_finite (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable μ h) :
    IsFiniteMeasure (totalVariation (densityMeasure μ h hh)) := by
  rw [densityMeasure_variation]
  apply isFiniteMeasure_withDensity
  simpa only [ofReal_norm] using
    ((scalarIntegrable_iff μ h).mp hh).2.hasFiniteIntegral.ne

theorem densityMeasure_countable_additivity (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable μ h) (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    HasSum (fun n => densityMeasure μ h hh (E n))
      (densityMeasure μ h hh (⋃ n, E n)) :=
  (densityMeasure μ h hh).m_iUnion hE hd

theorem densityMeasure_variation_apply (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable μ h) (E : Set X) (hE : MeasurableSet E) :
    totalVariation (densityMeasure μ h hh) E = ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ := by
  rw [densityMeasure_variation, withDensity_apply _ hE]

theorem densityMeasure_partition_variation (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable μ h) (E : Set X) (hE : MeasurableSet E) :
    (⨆ (P : Finpartition (⟨E, hE⟩ : Subtype MeasurableSet)),
      ∑ A ∈ P.parts, ENNReal.ofReal ‖densityMeasure μ h hh A‖) =
        ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ := by
  rw [← totalVariation_partition_formula _ E hE, densityMeasure_variation_apply μ h hh E hE]

/-- The positive and negative density measures form a Jordan decomposition. -/
theorem densityMeasure_jordan (μ : Measure X) (h : X → ℝ)
    (hh : scalarIntegrable μ h) :
    positivePart (densityMeasure μ h hh) =
      μ.withDensity (fun x => ENNReal.ofReal (D11.Ch06.ScalarIntegral.positivePart h x)) ∧
    negativePart (densityMeasure μ h hh) =
      μ.withDensity (fun x => ENNReal.ofReal (D11.Ch06.ScalarIntegral.negativePart h x)) := by
  have hi : Integrable h μ := ((scalarIntegrable_iff μ h).mp hh).2
  let p := μ.withDensity (fun x => ENNReal.ofReal (h x))
  let n := μ.withDensity (fun x => ENNReal.ofReal (-h x))
  let : IsFiniteMeasure p := isFiniteMeasure_withDensity_ofReal hi.2
  let : IsFiniteMeasure n := isFiniteMeasure_withDensity_ofReal hi.neg.2
  have hs : D11.Ch14.ScalarInterfaces.positiveSingular p n :=
    (D11.Ch14.ScalarInterfaces.positiveSingular_native_iff p n).mpr
      (withDensity_ofReal_mutuallySingular hh.1)
  have he : ∀ E : Set X, MeasurableSet E →
      densityMeasure μ h hh E = (p E).toReal - (n E).toReal := by
    intro E hE
    change μ.withDensityᵥ h E = _
    rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hi,
      Measure.toSignedMeasure_sub_apply hE]
    rfl
  obtain ⟨hp, hn⟩ := jordan_unique (densityMeasure μ h hh) p n hs he
  have hmax (a : ℝ) : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
    · rw [max_eq_right (le_of_not_ge ha), ENNReal.ofReal_zero,
        ENNReal.ofReal_eq_zero.mpr (le_of_not_ge ha)]
  constructor
  · simpa only [p, D11.Ch06.ScalarIntegral.positivePart, hmax] using hp.symm
  · simpa only [n, D11.Ch06.ScalarIntegral.negativePart, hmax] using hn.symm

theorem densityMeasure_jordan_apply (μ : Measure X) (h : X → ℝ)
    (hh : scalarIntegrable μ h) (E : Set X) (hE : MeasurableSet E) :
    positivePart (densityMeasure μ h hh) E =
      (∫⁻ x in E, ENNReal.ofReal (D11.Ch06.ScalarIntegral.positivePart h x) ∂μ) ∧
    negativePart (densityMeasure μ h hh) E =
      (∫⁻ x in E, ENNReal.ofReal (D11.Ch06.ScalarIntegral.negativePart h x) ∂μ) := by
  obtain ⟨hp, hn⟩ := densityMeasure_jordan μ h hh
  rw [hp, hn, withDensity_apply _ hE, withDensity_apply _ hE]
  exact ⟨rfl, rfl⟩

end D11.Ch14.DensityMeasureVariation
