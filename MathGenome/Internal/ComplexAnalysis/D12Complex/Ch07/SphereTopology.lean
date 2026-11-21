import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereTopology
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Sphere
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
The compact connected Hausdorff sphere, its dense finite plane, and its two
topological coordinates. Inversion tends to zero along the cobounded filter,
and tends to the cobounded filter at a punctured zero. Since ℂ is proper, these
are exactly the two limits needed for continuity at the added point.
-/

open scoped Topology
open Filter
noncomputable section
namespace D12Complex

theorem sphere_compact : CompactSpace RiemannSphere := inferInstance

theorem sphere_hausdorff : T2Space RiemannSphere := inferInstance

theorem sphere_connected : ConnectedSpace RiemannSphere := inferInstance

theorem sphereFinite_denseRange : DenseRange sphereFinite := OnePoint.denseRange_coe

theorem continuous_sphereFinite : Continuous sphereFinite := OnePoint.continuous_coe

theorem continuousOn_finiteCoordinate : ContinuousOn finiteCoordinate finiteChart.source := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  induction p using OnePoint.rec with
  | infty => exact False.elim (hp rfl)
  | coe z => exact OnePoint.continuousAt_coe.mpr continuousAt_id

theorem continuousAt_infinityCoordinate_infty :
    ContinuousAt infinityCoordinate sphereInfty := by
  apply OnePoint.continuousAt_infty'.mpr
  change Tendsto (fun z : ℂ => z⁻¹) (coclosedCompact ℂ) (𝓝 0)
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  exact tendsto_inv₀_cobounded

theorem continuousOn_infinityCoordinate :
    ContinuousOn infinityCoordinate infinityChart.source := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  induction p using OnePoint.rec with
  | infty => exact continuousAt_infinityCoordinate_infty
  | coe z =>
    have hz : z ≠ 0 := fun hz => hp (congrArg sphereFinite hz)
    exact OnePoint.continuousAt_coe.mpr (continuousAt_inv₀ hz)

theorem continuous_infinityParametrization : Continuous infinityParametrization := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : w = 0
  · subst w
    rw [continuousAt_iff_punctured_nhds, infinityParametrization_zero]
    have hi : Tendsto (fun z : ℂ => sphereFinite z⁻¹) (𝓝[≠] 0) (𝓝 sphereInfty) := by
      apply OnePoint.tendsto_coe_infty.comp
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero
    apply hi.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (infinityParametrization_ne_zero z hz).symm
  · have hi : ContinuousAt (fun z : ℂ => sphereFinite z⁻¹) w :=
      continuous_sphereFinite.continuousAt.comp (continuousAt_inv₀ hw)
    apply hi.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hw] with z hz
    exact infinityParametrization_ne_zero z hz

theorem finiteChart_homeomorph :
    IsOpen finiteChart.source ∧ IsOpen finiteChart.target ∧
      ∃ e : PartialHomeomorph RiemannSphere ℂ, e.toPartialEquiv = finiteChart := by
  refine ⟨isClosed_singleton.isOpen_compl, isOpen_univ, ?_⟩
  exact ⟨⟨finiteChart, continuousOn_finiteCoordinate,
    continuous_sphereFinite.continuousOn⟩, rfl⟩

theorem infinityChart_homeomorph :
    IsOpen infinityChart.source ∧ IsOpen infinityChart.target ∧
      ∃ e : PartialHomeomorph RiemannSphere ℂ, e.toPartialEquiv = infinityChart := by
  refine ⟨isClosed_singleton.isOpen_compl, isOpen_univ, ?_⟩
  exact ⟨⟨infinityChart, continuousOn_infinityCoordinate,
    continuous_infinityParametrization.continuousOn⟩, rfl⟩

theorem sphere_chart_overlap :
    finiteChart.target ∩ finiteChart.symm ⁻¹' infinityChart.source = ({0}ᶜ : Set ℂ) ∧
    infinityChart.target ∩ infinityChart.symm ⁻¹' finiteChart.source = ({0}ᶜ : Set ℂ) := by
  constructor
  · ext z
    change (True ∧ sphereFinite z ≠ sphereFinite 0) ↔ z ≠ 0
    simp [sphereFinite]
  · ext z
    change (True ∧ infinityParametrization z ≠ sphereInfty) ↔ z ≠ 0
    by_cases hz : z = 0
    · simp [hz]
    · simp [infinityParametrization, hz, sphereFinite, sphereInfty]

theorem sphere_chart_transition_formulas (z : ℂ) (hz : z ≠ 0) :
    infinityChart (finiteChart.symm z) = z⁻¹ ∧
    finiteChart (infinityChart.symm z) = z⁻¹ := by
  exact ⟨rfl, by simp [infinityChart, finiteChart, infinityParametrization, hz,
    finiteCoordinate, sphereFinite]⟩

theorem sphere_chart_transition_biholomorphic :
    BiholomorphicPair ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ)
      (fun z => infinityChart (finiteChart.symm z))
      (fun w => finiteChart (infinityChart.symm w)) := by
  have heq : (fun w => finiteChart (infinityChart.symm w)) = (fun w : ℂ => w⁻¹) := by
    funext w
    change finiteCoordinate (infinityParametrization w) = w⁻¹
    by_cases hw : w = 0
    · simp [hw, finiteCoordinate, sphereInfty]
    · exact (sphere_chart_transition_formulas w hw).2
  change BiholomorphicPair ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) (fun z => z⁻¹) _
  rw [heq]
  have hh : HolomorphicOn ({0}ᶜ : Set ℂ) (fun z => z⁻¹) :=
    ⟨isClosed_singleton.isOpen_compl, fun z hz => differentiableAt_inv_iff.mpr hz⟩
  exact ⟨hh, hh, fun z hz => inv_ne_zero hz, fun z hz => inv_ne_zero hz,
    fun z _ => inv_inv z, fun z _ => inv_inv z⟩

end D12Complex
