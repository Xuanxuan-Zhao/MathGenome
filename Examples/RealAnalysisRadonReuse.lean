import MathGenome.RealAnalysis
import Examples.RealAnalysisRadonReuseSpecs

/-! Three compositions through the released public import. The independently
stated expected types are in `Examples.RealAnalysisRadonReuseSpecs`. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
universe u v

namespace RealAnalysisRadonReuse

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

theorem arbitrary_radon_swap :
    RealAnalysisRadonReuseSpecs.arbitrary_radon_swap.{u, v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν
  letI : MeasurableSpace (X × Y) := borel (X × Y)
  letI : MeasurableSpace (Y × X) := borel (Y × X)
  refine ⟨D11.Ch18.RadonProduct.radonProduct_isRadon X Y μ ν hμ hν, ?_⟩
  intro E hE
  have hmap := D11.Ch18.RadonProductSwap.map_swap X Y μ ν hμ hν
  have hm : @Measurable (X × Y) (Y × X)
      (borel (X × Y)) (borel (Y × X)) Prod.swap := continuous_swap.measurable
  have hpre : MeasurableSet[borel (Y × X)] (Prod.swap ⁻¹' E) :=
    hE.preimage continuous_swap.measurable
  have he := congrArg
    (fun ρ : @Measure (Y × X) (borel (Y × X)) => ρ (Prod.swap ⁻¹' E)) hmap
  have hdouble : (Prod.swap : X × Y → Y × X) ⁻¹'
      ((Prod.swap : Y × X → X × Y) ⁻¹' E) = E := by
    ext p
    change Prod.swap (Prod.swap p) ∈ E ↔ p ∈ E
    rw [Prod.swap_swap]
  rw [Measure.map_apply hm hpre, hdouble] at he
  exact he

theorem positive_riesz_roundtrip :
    RealAnalysisRadonReuseSpecs.positive_riesz_roundtrip.{u} := by
  intro X _ _ _ I hI
  obtain ⟨μ, hμ, _⟩ := D11.Ch19.PositiveRieszMarkov.real_representation I hI
  obtain ⟨J, hJ, hJrep⟩ :=
    D11.Ch19.PositiveRieszMarkov.radon_induces_real_functional μ hμ.1
  refine ⟨μ, hμ.1, ?_, J, hJ, ?_, ?_⟩
  · intro f
    obtain ⟨hf, he⟩ := hμ.2 f
    exact ⟨((D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ f).mp hf).2, he⟩
  · intro f
    obtain ⟨hf, he⟩ := hJrep.2 f
    exact ⟨((D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ f).mp hf).2, he⟩
  · ext f
    exact (hJrep.2 f).2.trans (hμ.2 f).2.symm

theorem compact_haar_normalization_unique :
    RealAnalysisRadonReuseSpecs.compact_haar_normalization_unique.{u} := by
  intro G _ _ _ _ _ μ hμ
  obtain ⟨hnorm, hmass⟩ :=
    D11.Ch21.HaarFiniteIffCompact.normalize_probability μ hμ
  obtain ⟨ρ, hρ, hunique⟩ := D11.Ch21.HaarFiniteIffCompact.unique_probability G
  refine ⟨hnorm, hmass, ?_⟩
  intro ν hν hνmass
  have hνρ : ν = ρ := hunique ν ⟨hν, hνmass⟩
  have hnormalizedρ : (μ univ)⁻¹ • μ = ρ :=
    hunique ((μ univ)⁻¹ • μ) ⟨hnorm, hmass⟩
  exact hνρ.trans hnormalizedρ.symm

end RealAnalysisRadonReuse
