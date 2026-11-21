import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.Disintegration
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.CompletedMeasurableVersions
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalLaws

/-! Conditional laws on the original space and for inputs admitting measurable
versions, including arbitrary measurable conditioning targets. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04

universe u v w

theorem conditional_joint_law :
    Specs.ProbabilityFoundations.Ch04.ConditionalLaws.jointLawType.{u,v,w} := by
  intro Ω S T _ _ _ _ P _ hT X Y hX hY
  let M := P.map (fun ω => (X ω, Y ω))
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have : IsProbabilityMeasure M := Ch01.law_probability P _ hXY
  apply disintegration hT M (P.map X)
  exact Measure.map_map measurable_fst hXY

theorem conditional_law :
    Specs.ProbabilityFoundations.Ch04.ConditionalLaws.conditionalLawType.{u,w} := by
  intro Ω T F _ _ P _ G hG hT Y hY
  obtain ⟨K, hK, hM⟩ :=
    @conditional_joint_law Ω Ω T F G _ _ P _ hT id Y (measurable_id'' hG) hY
  have := hK
  rw [← trim_eq_map hG] at hM
  refine ⟨K, hK, ?_⟩
  intro A hA B hB
  have h := congrArg (fun M : @Measure (Ω × T) (G.prod inferInstance) => M (A ×ˢ B)) hM
  rw [Measure.map_apply ((measurable_id'' hG).prodMk hY) (hA.prod hB)] at h
  change P (A ∩ Y ⁻¹' B) = kernelMeasure (P.trim hG) K (A ×ˢ B) at h
  have : @IsProbabilityMeasure Ω G (P.trim hG) :=
    ⟨by rw [trim_measurableSet_eq hG MeasurableSet.univ, measure_univ]⟩
  exact (h.trans (Measure.compProd_apply_prod hA hB)).symm

theorem completed_conditional_joint_law :
    Specs.ProbabilityFoundations.Ch04.ConditionalLaws.completedJointLawType.{u,v,w} := by
  intro Ω S T _ _ _ _ P _ hT X X0 Y Y0 hX0 hY0 hX hY
  obtain ⟨K, hK, hM⟩ := conditional_joint_law P hT X0 Y0 hX0 hY0
  refine ⟨K, hK, ?_⟩
  have hXc := (hX0.nullMeasurable.congr hX.symm).measurable'
  have hYc := (hY0.nullMeasurable.congr hY.symm).measurable'
  have hXY : (fun ω => (X ω, Y ω)) =ᵐ[P] (fun ω => (X0 ω, Y0 ω)) := by
    filter_upwards [hX, hY] with ω hx hy
    exact Prod.ext hx hy
  rw [Ch01.completed_version_law P _ _ (hXc.prodMk hYc) (hX0.prodMk hY0) hXY,
    Ch01.completed_version_law P X X0 hXc hX0 hX]
  exact hM

theorem completed_conditional_law :
    Specs.ProbabilityFoundations.Ch04.ConditionalLaws.completedConditionalLawType.{u,w} := by
  intro Ω T F _ _ P _ G hG hT Y Y0 hY0 hY
  obtain ⟨K, hK, h⟩ := @conditional_law Ω T F _ _ P _ G hG hT Y0 hY0
  refine ⟨K, hK, ?_⟩
  intro A hA B hB
  rw [h A hA B hB]
  change P (A ∩ Y0 ⁻¹' B) = P (A ∩ Y ⁻¹' B)
  apply measure_congr
  filter_upwards [hY] with ω hω
  simp only [Set.mem_inter_iff, Set.mem_preimage, hω]

end ProbabilityFoundations.Ch04
