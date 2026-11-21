import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import Mathlib.Analysis.Calculus.MeanValue

/-! A generator determines its C₀ semigroup. We differentiate the comparison
orbit S(t-s)T(s)x by difference quotients and local operator bounds. This uses
strong continuity only, without assuming operator-norm continuity. -/

noncomputable section
open Filter Topology Set
open scoped NNReal

namespace ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

/-- A uniformly bounded varying operator sends a vanishing vector to zero. -/
theorem tendsto_apply_zero_of_bounded (S : C0Semigroup 𝕜 X)
    {ι : Type*} {l : Filter ι} (u : ι → ℝ≥0) {v : ι → X} {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖S.operators (u i)‖ ≤ C)
    (hv : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => S.operators (u i) (v i)) l (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [hbound] with i hi
    exact ((S.operators (u i)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  · simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hv.norm

/-- Strong continuity and local boundedness allow the initial vector to vary. -/
theorem tendsto_apply (S : C0Semigroup 𝕜 X)
    {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0} {v : ι → X} {t : ℝ≥0} {x : X}
    (hu : Tendsto u l (𝓝 t)) (hv : Tendsto v l (𝓝 x)) :
    Tendsto (fun i => S.operators (u i) (v i)) l (𝓝 (S.operators t x)) := by
  obtain ⟨C, _, hC⟩ := S.bounded_on_interval (t + 1)
  have hbound : ∀ᶠ i in l, ‖S.operators (u i)‖ ≤ C := by
    filter_upwards [hu.eventually (gt_mem_nhds (show t < t + 1 by simp))] with i hi
    exact hC _ hi.le
  have hz := tendsto_apply_zero_of_bounded S u hbound (by
    simpa only [sub_self] using hv.sub_const x)
  have hx := ((S.continuous_orbit x).tendsto t).comp hu
  simpa only [Function.comp_def, map_sub, sub_add_cancel, zero_add] using hz.add hx

/-- The comparison orbit is continuous, including both endpoints. -/
theorem continuous_comparison (S T : C0Semigroup 𝕜 X) (t : ℝ≥0) (x : X) :
    Continuous (fun s : ℝ => S.operators ((t : ℝ) - s).toNNReal
      (T.operators s.toNNReal x)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact tendsto_apply S
    (continuous_real_toNNReal.continuousAt.comp (continuous_const.sub continuous_id).continuousAt)
    (T.continuous_real_orbit x).continuousAt

/-- The two generator quotients at a common domain vector cancel in the limit. -/
theorem tendsto_differenceQuotient_sub (S T : C0Semigroup 𝕜 X)
    (hgen : generator S = generator T) (x : (generator T).domain) :
    Tendsto (fun h => differenceQuotient T h x - differenceQuotient S h x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have heq := (Unbounded.equality_iff (generator S) (generator T)).mp hgen
  have hxS : (x : X) ∈ (generator S).domain := by
    rw [heq.1]
    exact x.2
  have hAx : generator S ⟨x, hxS⟩ = generator T x := heq.2 x hxS x.2
  have hS := generator_has_limit S ⟨x, hxS⟩
  have hT := generator_has_limit T x
  change Tendsto (fun h => differenceQuotient S h x) _ (𝓝 (generator S ⟨x, hxS⟩)) at hS
  change Tendsto (fun h => differenceQuotient T h x) _ (𝓝 (generator T x)) at hT
  simpa only [hAx, sub_self] using hT.sub hS

/-- The comparison orbit has zero right derivative before the final endpoint. -/
theorem comparison_hasDerivWithinAt_right (S T : C0Semigroup 𝕜 X)
    (hgen : generator S = generator T) (x : (generator T).domain)
    (t : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) (hst : s < (t : ℝ)) :
    HasDerivWithinAt (fun r : ℝ => S.operators ((t : ℝ) - r).toNNReal
      (T.operators r.toNNReal x)) 0 (Ici s) s := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  let y : (generator T).domain :=
    ⟨T.operators s.toNNReal x,
      SemigroupGrowthAndGenerator.domain_invariant T s.toNNReal x x.2⟩
  have hshift : Tendsto (fun r : ℝ => r - s) (𝓝[>] s) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert! ((tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => r) (𝓝[>] s) (𝓝 s)).sub_const s) using 1
      simp
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (show s < r from hr)
  have hlim := (tendsto_differenceQuotient_sub S T hgen y).comp hshift
  obtain ⟨C, _, hC⟩ := S.bounded_on_interval t
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] s,
      ‖S.operators ((t : ℝ) - r).toNNReal‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply hC
    have hr0 : 0 ≤ r := hs.trans (show s ≤ r from le_of_lt hr)
    simpa only [Real.toNNReal_coe] using
      Real.toNNReal_le_toNNReal (show (t : ℝ) - r ≤ (t : ℝ) by linarith)
  have hz := tendsto_apply_zero_of_bounded S (fun r : ℝ => ((t : ℝ) - r).toNNReal)
    hbound hlim
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds] with r hrs hrt
  rw [slope_def_module]
  change S.operators ((t : ℝ) - r).toNNReal
    (differenceQuotient T (r - s) (T.operators s.toNNReal x) -
      differenceQuotient S (r - s) (T.operators s.toNNReal x)) = _
  rw [T.differenceQuotient_real, S.differenceQuotient_real]
  rw [← smul_sub, (S.operators ((t : ℝ) - r).toNNReal).map_smul_of_tower]
  congr 1
  rw [map_sub, map_sub, map_sub]
  simp only [sub_sub_sub_cancel_right]
  have hTtime : (r - s).toNNReal + s.toNNReal = r.toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr (le_of_lt hrs)),
      Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (hs.trans (le_of_lt hrs))]
    ring
  have hStime : ((t : ℝ) - r).toNNReal + (r - s).toNNReal =
      ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr (le_of_lt hrt)),
      Real.coe_toNNReal _ (sub_nonneg.mpr (le_of_lt hrs)),
      Real.coe_toNNReal _ (sub_nonneg.mpr hst.le)]
    ring
  rw [← T.add_apply, hTtime, ← S.add_apply, hStime]

/-- Equality first holds on the common generator domain. -/
theorem operators_eq_on_domain (S T : C0Semigroup 𝕜 X)
    (hgen : generator S = generator T) (t : ℝ≥0) (x : (generator T).domain) :
    S.operators t x = T.operators t x := by
  have hc := (continuous_comparison S T t x).continuousOn (s := Icc (0 : ℝ) (t : ℝ))
  have hd : ∀ s ∈ Ico (0 : ℝ) (t : ℝ),
      HasDerivWithinAt (fun r : ℝ => S.operators ((t : ℝ) - r).toNNReal
        (T.operators r.toNNReal x)) 0 (Ici s) s := by
    intro s hs
    exact comparison_hasDerivWithinAt_right S T hgen x t s hs.1 hs.2
  have heq := constant_of_has_deriv_right_zero hc hd (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  simpa only [sub_self, Real.toNNReal_zero, C0Semigroup.zero_apply,
    sub_zero, Real.toNNReal_coe] using heq.symm

/-- Two semigroups with identical exact-domain generators agree at all times. -/
theorem generator_determines_semigroup (S T : C0Semigroup 𝕜 X)
    (hgen : generator S = generator T) (t : ℝ≥0) :
    S.operators t = T.operators t := by
  have hd : Dense ((generator T).domain : Set X) := T.generator_domain_dense
  have heq : EqOn (S.operators t) (T.operators t) ((generator T).domain : Set X) := by
    intro x hx
    exact operators_eq_on_domain S T hgen t ⟨x, hx⟩
  ext x
  exact congrFun ((S.operators t).continuous.ext_on hd (T.operators t).continuous heq) x

end ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
