import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarPositiveOpen
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactTranslateIntegralContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of compact-support translate integrals

At a fixed parameter choose a compact neighborhood T. Every section
`t ↦ g (t * x)` for `x ∈ T` vanishes outside the compact set
`tsupport g * T⁻¹`. The compact-support parameter-integral theorem uses
uniform control on this compact set in the neighborhood topology. Thus no
countability, metrizability or sigma-finiteness assumption enters the proof.

The translated functions are themselves Cc functions. Compact finiteness gives
their scalar integrability, and the shared Haar positivity theorem applies to
each nonzero nonnegative translate.
-/
namespace D11.Ch21.CompactTranslateIntegralContinuity

open Set MeasureTheory
open scoped Topology Pointwise
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Right translation preserves continuous compact support. -/
private def translate {𝕜 : Type} [RCLike 𝕜] (g : D11.Ch19.Cc G 𝕜) (x : G) :
    D11.Ch19.Cc G 𝕜 :=
  ⟨⟨fun t => g (t * x), g.continuous.comp (continuous_id.mul continuous_const)⟩,
    g.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight x)⟩

theorem translate_integrable {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (ν : @Measure G (borel G))
    (hν : D11.Ch18.isRadon ν) (g : D11.Ch19.Cc G 𝕜) (x : G) :
    D11.Ch06.ScalarIntegral.scalarIntegrable ν (fun t => g (t * x)) := by
  let : IsFiniteMeasureOnCompacts ν := (D11.Ch18.compactFinite_iff ν).mp hν.1
  let hf := translate g x
  change D11.Ch06.ScalarIntegral.scalarIntegrable ν (fun t => hf t)
  exact (D11.Ch06.ScalarIntegral.scalarIntegrable_iff ν _).mpr
    ⟨hf.continuous.measurable,
      hf.continuous.integrable_of_hasCompactSupport hf.hasCompactSupport⟩

theorem continuous_translate_integral {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (ν : @Measure G (borel G))
    (hν : D11.Ch18.isRadon ν) (g : D11.Ch19.Cc G 𝕜) :
    Continuous (fun x : G => ∫ t, g (t * x) ∂ν) := by
  let : IsFiniteMeasureOnCompacts ν := (D11.Ch18.compactFinite_iff ν).mp hν.1
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨T, hT, hx₀⟩ := exists_compact_mem_nhds x₀
  have hK : IsCompact (tsupport g * T⁻¹) := g.hasCompactSupport.mul hT.inv
  have hcont : ContinuousOn (fun x : G => ∫ t, g (t * x) ∂ν) T := by
    apply continuousOn_integral_of_compact_support hK
    · exact (g.continuous.comp (continuous_snd.mul continuous_fst)).continuousOn
    · intro x t hx ht
      contrapose! ht
      exact ⟨t * x, subset_tsupport _ ht, x⁻¹, by simpa, by simp⟩
  exact hcont.continuousAt hx₀

theorem haar_translate_integral_pos (ν : @Measure G (borel G))
    (hν : isLeftHaarMeasure ν ∨ isRightHaarMeasure ν)
    (g : D11.Ch19.Cc G ℝ) (hg : ∀ t, 0 ≤ g t) (hne : g ≠ 0) (x : G) :
    D11.Ch06.ScalarIntegral.scalarIntegrable ν (fun t => g (t * x)) ∧
      0 < ∫ t, g (t * x) ∂ν := by
  have htranslate : translate g x ≠ 0 := by
    intro h
    apply hne
    apply DFunLike.ext
    intro t
    have ht := DFunLike.congr_fun h (t * x⁻¹)
    change g ((t * x⁻¹) * x) = 0 at ht
    simpa using ht
  exact HaarPositiveOpen.integral_pos ν hν (translate g x) (fun t => hg _) htranslate

end D11.Ch21.CompactTranslateIntegralContinuity
