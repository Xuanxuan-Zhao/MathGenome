import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.DominatedConvergence
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated and bounded convergence, paper.tex:1903–1949. The scalar bridge
retains actual measurability before any use of the totalized Bochner integral.
The lower-integral bridge identifies the absolute error integral with the
paper's nonnegative integral. All measure spaces may be incomplete and have
arbitrary mass, except for the explicitly finite-domain specialization. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace D11.Ch06.DominatedConvergence
open ScalarIntegral
open D11.Ch05.NonnegativeIntegral
open D11.Ch04.AeCommonException

theorem dominated_convergence : Specs.D11.Ch06.DominatedConvergence.dominated_convergence := by
  intro X 𝕜 _ _ _ _ μ F f g hFm hfm hg _hg0 hbound hlim
  have hgi := (scalarIntegrable_iff μ g).mp hg |>.2
  have hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x :=
    fun n => (almostEverywhere_iff_native μ _).mp (hbound n)
  have hl : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    (almostEverywhere_iff_native μ _).mp hlim
  have hFi : ∀ n, scalarIntegrable μ (F n) := fun n =>
    (scalarIntegrable_iff μ (F n)).mpr
      ⟨hFm n, hgi.mono' (hFm n).aestronglyMeasurable (hb n)⟩
  have hfi : scalarIntegrable μ f := (scalarIntegrable_iff μ f).mpr
    ⟨hfm, hfm.aestronglyMeasurable,
      hasFiniteIntegral_of_dominated_convergence hgi.hasFiniteIntegral hb hl⟩
  refine ⟨hFi, hfi, ?_, ?_, ?_⟩
  · intro n
    exact (scalarIntegrable_iff μ _).mpr
      ⟨((hFm n).sub hfm).norm,
        (((scalarIntegrable_iff μ (F n)).mp (hFi n)).2.sub
          ((scalarIntegrable_iff μ f).mp hfi).2).norm⟩
  · change Tendsto (fun n => nonnegativeIntegral μ
      (fun x => ENNReal.ofReal ‖F n x - f x‖)) atTop (𝓝 0)
    simp only [integral_eq_lintegral]
    exact tendsto_lintegral_norm_of_dominated_convergence
      (fun n => (hFm n).aestronglyMeasurable) hgi.hasFiniteIntegral hb hl
  · exact tendsto_integral_of_dominated_convergence g
      (fun n => (hFm n).aestronglyMeasurable) hgi hb hl

theorem bounded_convergence_fixed_support :
    Specs.D11.Ch06.DominatedConvergence.bounded_convergence_fixed_support := by
  intro X 𝕜 _ _ _ _ μ F f E M hE hEfin hFm hfm hsupp hbound hlim
  let g : X → ℝ := E.indicator (fun _ => max M 0)
  have hgm : Measurable g := measurable_const.indicator hE
  have hg0 : ∀ x, 0 ≤ g x := fun x => indicator_nonneg (fun _ _ => le_max_right _ _) x
  have hg : scalarIntegrable μ g := (scalarIntegrable_iff μ g).mpr
    ⟨hgm, (integrable_indicator_iff hE).mpr
      (integrableOn_const (C := max M 0) hEfin.ne)⟩
  apply dominated_convergence μ F f g hFm hfm hg hg0 _ hlim
  intro n
  apply (almostEverywhere_iff_native μ _).mpr
  have hb := (almostEverywhere_iff_native μ _).mp (hbound n)
  filter_upwards [hb] with x hx
  by_cases hxE : x ∈ E
  · exact (by simpa only [g, indicator_of_mem hxE] using hx.trans (le_max_left M 0))
  · simp [g, hxE, hsupp n x hxE]

theorem bounded_convergence : Specs.D11.Ch06.DominatedConvergence.bounded_convergence := by
  intro X 𝕜 _ _ _ _ μ F f M hμ hFm hfm hbound hlim
  exact bounded_convergence_fixed_support μ F f univ M MeasurableSet.univ hμ hFm hfm
    (fun _ _ hx => False.elim (hx (mem_univ _))) hbound hlim

end D11.Ch06.DominatedConvergence
