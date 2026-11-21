import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.PolarDecomposition
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNSignedComplex
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! Polar decomposition, paper.tex:4983–4996. RN relative to the finite
partition variation gives a measurable density. Variation of that density
forces its norm to equal one almost everywhere. Patching its measurable
exceptional set by the constant one preserves measurability and all integrals.
-/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch15.PolarDecomposition

open Ch14.TotalVariation

variable {X : Type u} [MeasurableSpace X]

/-- A density with respect to its own variation has unit norm almost everywhere. -/
theorem norm_ae_eq_one {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : VectorMeasure X 𝕜) [IsFiniteMeasure (totalVariation ν)]
    (h : X → 𝕜) (hm : Measurable h) (hi : Integrable h (totalVariation ν))
    (hr : (totalVariation ν).withDensityᵥ h = ν) :
    ∀ᵐ x ∂(totalVariation ν), ‖h x‖ = 1 := by
  have hv : (totalVariation ν).withDensity (fun x => ENNReal.ofReal ‖h x‖) =
      totalVariation ν := by
    have hs : Ch06.ScalarIntegral.scalarIntegrable (totalVariation ν) h :=
      (Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mpr ⟨hm, hi⟩
    simpa only [Ch14.DensityMeasureVariation.densityMeasure, hr] using
      (Ch14.DensityMeasureVariation.densityMeasure_variation
        (totalVariation ν) h hs).symm
  have he : (fun x => ENNReal.ofReal ‖h x‖) =ᵐ[totalVariation ν]
      (fun _ => (1 : ℝ≥0∞)) := by
    apply (withDensity_eq_iff_of_sigmaFinite
      hm.norm.ennreal_ofReal.aemeasurable measurable_const.aemeasurable).mp
    exact hv.trans (withDensity_one (μ := totalVariation ν)).symm
  filter_upwards [he] with x hx
  have hx' := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_one] using hx'

/-- Replace precisely the measurable set of nonunit values by one. -/
theorem exists_unit_representative {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (h : X → 𝕜) (hm : Measurable h) (hi : Integrable h μ)
    (hu : ∀ᵐ x ∂μ, ‖h x‖ = 1) :
    ∃ u : X → 𝕜, Measurable u ∧ Integrable u μ ∧
      (∀ x, ‖u x‖ = 1) ∧ u =ᵐ[μ] h := by
  let s : Set X := {x | ‖h x‖ = 1}
  have hs : MeasurableSet s := measurableSet_eq_fun hm.norm measurable_const
  let u : X → 𝕜 := s.piecewise h (fun _ => 1)
  have he : u =ᵐ[μ] h := by
    filter_upwards [hu] with x hx
    exact ite_eq_left hx
  refine ⟨u, hm.piecewise hs measurable_const, hi.congr he.symm, ?_, he⟩
  intro x
  by_cases hx : x ∈ s
  · change ‖h x‖ = 1 at hx
    simpa only [u, Set.piecewise_eq_of_mem s h (fun _ => 1) hx] using hx
  · simp only [u, Set.piecewise_eq_of_notMem s h (fun _ => 1) hx, norm_one]

theorem polar_complex : Specs.D11.Ch15.PolarDecomposition.polar_complex := by
  intro X _ ν
  let := complex_finite ν
  obtain ⟨h, hm, hi, hr⟩ := RNSignedComplex.exists_complex_density
    (totalVariation ν) ν Measure.AbsolutelyContinuous.rfl
  obtain ⟨u, um, ui, uu, ue⟩ := exists_unit_representative
    (totalVariation ν) h hm hi (norm_ae_eq_one ν h hm hi hr)
  have ur : (totalVariation ν).withDensityᵥ u = ν := by
    rw [WithDensityᵥEq.congr_ae ue, hr]
  obtain ⟨urep, _, uunique⟩ :=
    RNSignedComplex.density_conclusions (totalVariation ν) ν u um ui ur
  exact ⟨u, um, ui, uu, urep, uunique⟩

theorem polar_signed : Specs.D11.Ch15.PolarDecomposition.polar_signed := by
  intro X _ ν
  let := signed_finite ν
  obtain ⟨h, hm, hi, hr⟩ := RNSignedComplex.exists_signed_density
    (totalVariation ν) ν Measure.AbsolutelyContinuous.rfl
  obtain ⟨u, um, ui, uu, ue⟩ := exists_unit_representative
    (totalVariation ν) h hm hi (norm_ae_eq_one ν h hm hi hr)
  have ur : (totalVariation ν).withDensityᵥ u = ν := by
    rw [WithDensityᵥEq.congr_ae ue, hr]
  obtain ⟨urep, _, uunique⟩ :=
    RNSignedComplex.density_conclusions (totalVariation ν) ν u um ui ur
  refine ⟨u, um, ui, ?_, urep, uunique⟩
  intro x
  have hx : |u x| = 1 := uu x
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx with hp | hn
  · exact Or.inr hp
  · exact Or.inl hn

theorem zero_complex : Specs.D11.Ch15.PolarDecomposition.zero_complex := by
  intro X _
  simp [Specs.D11.Ch14.TotalVariation.totalVariation_value]

theorem zero_signed : Specs.D11.Ch15.PolarDecomposition.zero_signed := by
  intro X _
  simp [Specs.D11.Ch14.TotalVariation.totalVariation_value]

end D11.Ch15.PolarDecomposition
