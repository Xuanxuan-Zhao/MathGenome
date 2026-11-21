import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.LpTranslationContinuity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
C_c density and translation continuity, paper.tex:17307–17314.
Lebesgue measure on `Fin d → ℝ` is regular and locally finite. Mathlib's
C_c approximation theorem applies to this measure and arbitrary real normed
codomains. For translations, continuous dependence of measure-preserving
composition in finite Lᵖ gives continuity on the quotient directly. This
argument uses no convolution or approximate-identity theorem.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology
universe u

namespace ExpandedFA.Distributions

/-- Translation τ_h f(x) = f(x-h), well defined modulo a.e. equality. -/
def lpTranslation : LpTranslationContinuitySpec.LpTranslationType.{u} :=
  fun p _ h f => Lp.compMeasurePreserving (p := p) (fun x => x - h)
    (measurePreserving_sub_right volume h) f

theorem compactlySupportedContinuous_dense :
    LpTranslationContinuitySpec.CompactlySupportedContinuousDense.{u} := by
  intro E _ _ d p _ hp f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  obtain ⟨g, hgcompact, hgerror, hgcont, hgmem⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp hε.ne'
  refine ⟨hgmem.toLp g, ⟨g, hgcont, hgcompact, hgmem.coeFn_toLp⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]

theorem lpTranslation_representative :
    LpTranslationContinuitySpec.LpTranslationRepresentative.{u} := by
  intro E _ d p _ h f
  exact Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume h)

theorem lpTranslation_isometry :
    LpTranslationContinuitySpec.LpTranslationIsometry.{u} := by
  intro E _ d p _ h
  exact Lp.isometry_compMeasurePreserving (measurePreserving_sub_right volume h)

theorem lpTranslation_continuous :
    LpTranslationContinuitySpec.LpTranslationContinuous.{u} := by
  intro E _ d p _ hp f
  let g : (Fin d → ℝ) → C(Fin d → ℝ, Fin d → ℝ) :=
    fun h => ⟨fun x => x - h, continuous_id.sub continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g
      (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun h => measurePreserving_sub_right volume h) hp

theorem lpTranslation_norm_tendsto_zero :
    LpTranslationContinuitySpec.LpTranslationNormTendstoZero.{u} := by
  intro E _ d p _ hp f
  have hzero : LpTranslationContinuitySpec.LpTranslationValue p 0 f = f := by
    apply Lp.ext
    filter_upwards [lpTranslation_representative p (0 : Fin d → ℝ) f] with x hx
    simpa only [sub_zero] using hx
  have hc := ((lpTranslation_continuous p hp f).sub
    (continuous_const (y := f))).norm.tendsto 0
  simpa only [Pi.sub_apply, hzero, sub_self, norm_zero] using hc

end ExpandedFA.Distributions
