import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.LpTranslationContinuity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.KolmogorovRiesz
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
universe u

namespace ExpandedFA.Sobolev

/-!
Kolmogorov--Riesz, paper.tex:17857--17886. Finite norm nets give the necessary
conditions. For local sufficiency, finite cell averages approximate the family
uniformly by a bounded subset of a finite-dimensional space; Jensen and Tonelli
bound the error using the uniform translation modulus. Uniform tails then
assemble the local compactness conclusion into global relative norm compactness.
-/

def lpRestrict : KolmogorovRieszSpec.LpRestrictType :=
  KolmogorovRieszSpec.LpRestrictValue

section Restriction
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure X}

theorem lpRestrict_representative (s : Set X) (f : Lp E p μ) :
    lpRestrict p μ s f =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

theorem lpRestrict_sub (s : Set X) (f g : Lp E p μ) :
    lpRestrict p μ s (f - g) = lpRestrict p μ s f - lpRestrict p μ s g := by
  apply Lp.ext
  filter_upwards [lpRestrict_representative s (f - g),
    lpRestrict_representative s f, lpRestrict_representative s g,
    Lp.coeFn_sub (lpRestrict p μ s f) (lpRestrict p μ s g),
    ae_restrict_of_ae (Lp.coeFn_sub f g)] with x hfg hf hg hsub hsub'
  simp only [Pi.sub_apply] at *
  rw [hfg, hsub, hf, hg, hsub']

theorem norm_lpRestrict_le (s : Set X) (f : Lp E p μ) :
    ‖lpRestrict p μ s f‖ ≤ ‖f‖ := by
  rw [lpRestrict, KolmogorovRieszSpec.LpRestrictValue, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le f p μ s)

/-- Passing to a smaller region can only decrease the restriction norm. -/
theorem norm_lpRestrict_mono {s t : Set X} (hst : s ⊆ t) (f : Lp E p μ) :
    ‖lpRestrict p μ s f‖ ≤ ‖lpRestrict p μ t f‖ := by
  simp only [lpRestrict, KolmogorovRieszSpec.LpRestrictValue, Lp.norm_toLp]
  exact ENNReal.toReal_mono ((Lp.memLp f).restrict t).eLpNorm_ne_top
    (eLpNorm_mono_measure f (Measure.restrict_mono_set μ hst))

theorem dist_lpRestrict_le (s : Set X) (f g : Lp E p μ) :
    dist (lpRestrict p μ s f) (lpRestrict p μ s g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← lpRestrict_sub]
  exact norm_lpRestrict_le s (f - g)

theorem lpRestrict_lipschitz (s : Set X) : LipschitzWith 1 (lpRestrict (E := E) p μ s) := by
  exact LipschitzWith.of_dist_le_mul fun f g => by
    simpa using dist_lpRestrict_le s f g

/-- Multiplication by a measurable indicator, in the original Lᵖ space. -/
def lpCut (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) : Lp E p μ :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)

theorem lpCut_representative (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) :
    lpCut s hs f =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp _

theorem norm_lpCut_eq (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) :
    ‖lpCut s hs f‖ = ‖lpRestrict p μ s f‖ := by
  rw [lpCut, Lp.norm_toLp, lpRestrict, KolmogorovRieszSpec.LpRestrictValue,
    Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]

theorem lpCut_add_compl (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) :
    lpCut s hs f + lpCut sᶜ hs.compl f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (lpCut s hs f) (lpCut sᶜ hs.compl f),
    lpCut_representative s hs f, lpCut_representative sᶜ hs.compl f] with x hx hf hg
  rw [hx, Pi.add_apply, hf, hg]
  by_cases h : x ∈ s <;> simp [h]

/-- Splitting into a region and its complement loses at most the sum of norms. -/
theorem norm_le_lpRestrict_add_compl (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) :
    ‖f‖ ≤ ‖lpRestrict p μ s f‖ + ‖lpRestrict p μ sᶜ f‖ := by
  calc
    ‖f‖ = ‖lpCut s hs f + lpCut sᶜ hs.compl f‖ := by rw [lpCut_add_compl]
    _ ≤ ‖lpCut s hs f‖ + ‖lpCut sᶜ hs.compl f‖ := norm_add_le _ _
    _ = _ := by rw [norm_lpCut_eq, norm_lpCut_eq]

theorem dist_le_lpRestrict_add_tails (s : Set X) (hs : MeasurableSet s) (f g : Lp E p μ) :
    dist f g ≤ dist (lpRestrict p μ s f) (lpRestrict p μ s g) +
      ‖lpRestrict p μ sᶜ f‖ + ‖lpRestrict p μ sᶜ g‖ := by
  have H := norm_le_lpRestrict_add_compl s hs (f - g)
  rw [lpRestrict_sub, lpRestrict_sub] at H
  have H' := norm_sub_le (lpRestrict p μ sᶜ f) (lpRestrict p μ sᶜ g)
  simp only [dist_eq_norm]
  linarith

end Restriction

section NecessaryConditions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every single finite-Lᵖ vector has small tails. C_c density avoids any
extra measurability choice or sigma-finiteness hypothesis for representatives. -/
theorem lp_tail_eventually_small (hp : p ≠ ∞) (f : KolmogorovRieszSpec.Space E d p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop,
      ‖lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ f‖ < ε := by
  obtain ⟨g, ⟨v, _hv, hvc, hgv⟩, hfg⟩ := Metric.mem_closure_iff.mp
    (Distributions.compactlySupportedContinuous_dense (E := E) d p hp f) ε hε
  obtain ⟨r, hr⟩ := hvc.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  filter_upwards [eventually_ge_atTop r] with R hR
  have hgzero : lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ g = 0 := by
    apply Lp.ext
    filter_upwards [lpRestrict_representative _ g, ae_restrict_of_ae hgv,
      ae_restrict_mem measurableSet_closedBall.compl,
      (Lp.coeFn_zero (E := E) (p := p) (μ := volume.restrict
        (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ))] with x hx hxv hxR hx0
    rw [hx, hxv, hx0]
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    exact hxR (Metric.closedBall_subset_closedBall hR (hr hxs))
  have H := dist_lpRestrict_le (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ f g
  rw [hgzero, dist_zero_right] at H
  exact H.trans_lt hfg

/-- Finite norm nets make individual tail estimates uniform over a precompact set. -/
theorem totallyBounded_uniformLpTails (hp : p ≠ ∞)
    {A : Set (KolmogorovRieszSpec.Space E d p)} (hA : TotallyBounded A) :
    KolmogorovRieszSpec.UniformLpTails p A := by
  intro ε hε
  obtain ⟨t, _htA, ht, hcover⟩ := Metric.finite_approx_of_totallyBounded hA (ε / 2)
    (half_pos hε)
  have htTail : ∀ᶠ R : ℝ in atTop, ∀ g ∈ t,
      ‖lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ g‖ < ε / 2 :=
    ht.eventually_all.mpr fun g _hg => lp_tail_eventually_small hp g (half_pos hε)
  obtain ⟨R, hR, hRpos⟩ := (htTail.and (eventually_gt_atTop 0)).exists
  refine ⟨R, hRpos, fun f hf => ?_⟩
  obtain ⟨g, hgt, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  have hdist := dist_lpRestrict_le (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ f g
  have hnorm := dist_triangle (lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ f)
    (lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ g) 0
  rw [dist_zero_right, dist_zero_right] at hnorm
  have hg := hR g hgt
  have hfclose : dist f g < ε / 2 := hfg
  change ‖lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ f‖ < ε
  linarith

end NecessaryConditions

section TranslationCondition
variable {E : Type*} [NormedAddCommGroup E] {d : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem translation_difference_bound (h : Fin d → ℝ)
    (f g : KolmogorovRieszSpec.Space E d p) :
    ‖Distributions.lpTranslation p h f - f‖ ≤
      dist f g + ‖Distributions.lpTranslation p h g - g‖ + dist f g := by
  have H := dist_triangle4 (Distributions.lpTranslation p h f)
    (Distributions.lpTranslation p h g) g f
  have hi : Isometry (Distributions.lpTranslation (E := E) p h) :=
    Distributions.lpTranslation_isometry p h
  rw [hi.dist_eq f g, dist_comm g f] at H
  simpa only [dist_eq_norm] using H

/-- Uniform translation continuity on a totally bounded family, proved with
finite nets and the accepted translation isometry and individual continuity. -/
theorem totallyBounded_uniformTranslationContinuous (hp : p ≠ ∞)
    {A : Set (KolmogorovRieszSpec.Space E d p)} (hA : TotallyBounded A) :
    KolmogorovRieszSpec.UniformTranslationContinuous p A := by
  intro ε hε
  obtain ⟨t, _htA, ht, hcover⟩ := Metric.finite_approx_of_totallyBounded hA (ε / 3)
    (by positivity)
  have htTrans : ∀ᶠ h : Fin d → ℝ in 𝓝 0, ∀ g ∈ t,
      ‖Distributions.lpTranslation p h g - g‖ < ε / 3 := by
    apply ht.eventually_all.mpr
    intro g _hg
    exact (Distributions.lpTranslation_norm_tendsto_zero p hp g).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))
  obtain ⟨δ, hδ, hδt⟩ := Metric.nhds_basis_ball.eventually_iff.mp htTrans
  refine ⟨δ, hδ, fun h hh f hf => ?_⟩
  obtain ⟨g, hgt, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  have H := translation_difference_bound h f g
  have hg := hδt (by simpa only [Metric.mem_ball, dist_zero_right] using hh) g hgt
  have hfclose : dist f g < ε / 3 := hfg
  change ‖Distributions.lpTranslation p h f - f‖ < ε
  linarith

end TranslationCondition

theorem compact_implies_uniformConditions :
    KolmogorovRieszSpec.CompactImpliesUniformConditions := by
  intro 𝕜 _ d p _ hp A hA
  have ht : TotallyBounded A := hA.totallyBounded.subset subset_closure
  exact ⟨totallyBounded_uniformLpTails hp ht,
    totallyBounded_uniformTranslationContinuous hp ht⟩

section GlobalAssembly
variable {E : Type*} [NormedAddCommGroup E] {d : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Tightness upgrades total boundedness on every closed ball to total
boundedness globally. Centers of the local nets are chosen in the image of A,
so their tails obey exactly the same bound as the original family. -/
theorem totallyBounded_of_uniformLpTails_of_local
    {A : Set (KolmogorovRieszSpec.Space E d p)}
    (htail : KolmogorovRieszSpec.UniformLpTails p A)
    (hloc : ∀ R : ℝ, 0 < R → TotallyBounded
      (lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R) '' A)) :
    TotallyBounded A := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨R, hRpos, hR⟩ := htail (ε / 3) (by positivity)
  let s := Metric.closedBall (0 : Fin d → ℝ) R
  obtain ⟨t, hts, ht, hcover⟩ := Metric.finite_approx_of_totallyBounded
    (hloc R hRpos) (ε / 3) (by positivity)
  have hpre : ∀ y ∈ t, ∃ g ∈ A, lpRestrict p volume s g = y := fun y hy => hts hy
  choose g hgA hgy using hpre
  have : Finite t := ht.to_subtype
  let centers := (fun y : t => g y y.property) '' (Set.univ : Set t)
  have hcenters : centers.Finite := (Set.toFinite (Set.univ : Set t)).image _
  refine ⟨centers, hcenters, fun f hf => ?_⟩
  obtain ⟨y, hyt, hfy⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem _ hf))
  refine mem_iUnion₂.mpr ⟨g y hyt, ?_, ?_⟩
  · exact ⟨⟨y, hyt⟩, mem_univ _, rfl⟩
  · have H := dist_le_lpRestrict_add_tails s measurableSet_closedBall f (g y hyt)
    have hfTail := hR f hf
    have hgTail := hR (g y hyt) (hgA y hyt)
    have hlocal : dist (lpRestrict p volume s f) (lpRestrict p volume s (g y hyt)) < ε / 3 := by
      rw [hgy y hyt]
      exact hfy
    change dist f (g y hyt) < ε
    change ‖lpRestrict p volume sᶜ f‖ < ε / 3 at hfTail
    change ‖lpRestrict p volume sᶜ (g y hyt)‖ < ε / 3 at hgTail
    linarith

end GlobalAssembly

/-- Uniform tails and the local compactness conclusion give the full global
Kolmogorov--Riesz equivalence. -/
theorem kolmogorovRiesz_of_localCompactness
    (hloc : KolmogorovRieszSpec.LocalCompactness.{u}) :
    KolmogorovRieszSpec.KolmogorovRiesz.{u} := by
  intro 𝕜 _ d p _ hp A hbounded
  constructor
  · exact compact_implies_uniformConditions d p hp A
  · rintro ⟨htail, htrans⟩
    have ht : TotallyBounded A := totallyBounded_of_uniformLpTails_of_local htail
      (fun R _hR => (hloc d p hp A hbounded htrans (Metric.closedBall 0 R)
        measurableSet_closedBall (isCompact_closedBall (0 : Fin d → ℝ) R).isBounded).totallyBounded.subset
          subset_closure)
    exact ht.closure.isCompact_of_isClosed isClosed_closure

/-- Uniform approximation by totally bounded sets, useful for assembling the
local averaging proof without making any assumption about a fixed approximant. -/
theorem totallyBounded_of_totallyBounded_approximations
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ B : Set X, TotallyBounded B ∧
      ∀ x ∈ A, ∃ y ∈ B, dist x y < ε) : TotallyBounded A := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨B, hB, hnear⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hB (ε / 2) (half_pos hε)
  refine ⟨t, ht, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hnear x hx
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
  refine mem_iUnion₂.mpr ⟨z, hz, ?_⟩
  have hyz' : dist y z < ε / 2 := hyz
  have H := dist_triangle x y z
  change dist x z < ε
  linarith

section FiniteAverages
variable {X : Type*} [MeasurableSpace X] {𝕜 : Type*} [RCLike 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure X}

/-- The finite-measure Hölder estimate for the integral of an Lᵖ class. -/
theorem norm_setIntegral_le_lpNorm (hp : p ≠ ∞) (s : Set X)
    (hfin : μ s ≠ ∞) (f : Lp 𝕜 p μ) :
    ‖∫ x in s, f x ∂μ‖ ≤ ‖f‖ * μ.real s ^ (1 - 1 / p.toReal) := by
  have hp1 : (1 : ℝ) ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_mono hp (Fact.out : 1 ≤ p))
  have hexp : 0 ≤ 1 - 1 / p.toReal := sub_nonneg.mpr (by
    exact (div_le_one (by linarith)).mpr hp1)
  have hle : ‖∫ x in s, f x ∂μ‖ₑ ≤
      eLpNorm f p μ * (μ s) ^ (1 - 1 / p.toReal) := by
    calc
      _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ.restrict s := enorm_integral_le_lintegral_enorm _
      _ ≤ eLpNorm f 1 (μ.restrict s) := lintegral_enorm_le_eLpNorm_one
      _ ≤ eLpNorm f p (μ.restrict s) *
          (μ.restrict s) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ Fact.out (Lp.aestronglyMeasurable f).restrict
      _ ≤ _ := by
        simpa only [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one, mul_comm] using
          mul_le_mul_right (eLpNorm_restrict_le f p μ s) ((μ s) ^ (1 - 1 / p.toReal))
  have H := ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
    (ENNReal.rpow_ne_top_of_nonneg hexp hfin)) hle
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow, toReal_enorm,
    Lp.norm_def, measureReal_def] using H

/-- Integration over a finite-measure cell is a continuous linear functional
on the original Lᵖ space, including the endpoint p=1. -/
def lpCellIntegral (hp : p ≠ ∞) (s : Set X) (hfin : μ s ≠ ∞) :
    Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x in s, f x ∂μ
      map_add' := fun f g => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
        exact integral_add (integrableOn_Lp_of_measure_ne_top f Fact.out hfin)
          (integrableOn_Lp_of_measure_ne_top g Fact.out hfin)
      map_smul' := fun c f => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
        exact integral_smul c f }
    (μ.real s ^ (1 - 1 / p.toReal))
    (fun f => by
      change ‖∫ x in s, f x ∂μ‖ ≤ μ.real s ^ (1 - 1 / p.toReal) * ‖f‖
      simpa only [mul_comm] using norm_setIntegral_le_lpNorm hp s hfin f)

/-- Cell averages as continuous linear functionals. The value is zero on
null cells, so this construction never assumes positive measure implicitly. -/
def lpCellAverage (hp : p ≠ ∞) (s : Set X) (hfin : μ s ≠ ∞) :
    Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  (μ.real s)⁻¹ • lpCellIntegral hp s hfin

theorem lpCellAverage_apply (hp : p ≠ ∞) (s : Set X) (hfin : μ s ≠ ∞)
    (f : Lp 𝕜 p μ) :
    lpCellAverage hp s hfin f = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ := rfl

/-- Synthesis of an Lᵖ step function from its finitely many scalar values. -/
def lpStepSynthesis {ι : Type*} [Fintype ι]
    (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i)) (hfin : ∀ i, μ (Q i) ≠ ∞) :
    (ι → 𝕜) →L[𝕜] Lp 𝕜 p μ :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (indicatorConstLp p (hQ i) (hfin i) (1 : 𝕜))

/-- Finite cell averaging, defined on the a.e. quotient. -/
def lpFiniteAverage {ι : Type*} [Fintype ι] (hp : p ≠ ∞)
    (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i)) (hfin : ∀ i, μ (Q i) ≠ ∞) :
    Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  (lpStepSynthesis Q hQ hfin).comp
    (ContinuousLinearMap.pi fun i => lpCellAverage hp (Q i) (hfin i))

/-- The finite averaging operator sends every bounded family to a set with
compact norm closure. Disjointness is needed only for the later error bound. -/
theorem isCompact_closure_lpFiniteAverage_image {ι : Type*} [Fintype ι]
    (hp : p ≠ ∞) (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i))
    (hfin : ∀ i, μ (Q i) ≠ ∞) {A : Set (Lp 𝕜 p μ)} (hA : Bornology.IsBounded A) :
    IsCompact (closure (lpFiniteAverage hp Q hQ hfin '' A)) := by
  let C : Lp 𝕜 p μ →L[𝕜] (ι → 𝕜) :=
    ContinuousLinearMap.pi fun i => lpCellAverage hp (Q i) (hfin i)
  have hC : IsCompact (closure (C '' A)) :=
    (C.lipschitzWith.isBounded_image hA).isCompact_closure
  have hS := hC.image (lpStepSynthesis (p := p) Q hQ hfin).continuous
  apply hS.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hS.isClosed
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨C f, subset_closure (mem_image_of_mem C hf), rfl⟩

theorem lpStepSynthesis_apply {ι : Type*} [Fintype ι]
    (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i)) (hfin : ∀ i, μ (Q i) ≠ ∞)
    (a : ι → 𝕜) :
    lpStepSynthesis (p := p) Q hQ hfin a =
      ∑ i, a i • indicatorConstLp p (hQ i) (hfin i) (1 : 𝕜) := by
  simp [lpStepSynthesis]

/-- Explicit pointwise step-function representative of the finite average. -/
theorem lpFiniteAverage_representative {ι : Type*} [Fintype ι]
    (hp : p ≠ ∞) (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i))
    (hfin : ∀ i, μ (Q i) ≠ ∞) (f : Lp 𝕜 p μ) :
    lpFiniteAverage hp Q hQ hfin f =ᵐ[μ]
      fun x => ∑ i, (Q i).indicator (fun _ => lpCellAverage hp (Q i) (hfin i) f) x := by
  classical
  change lpStepSynthesis Q hQ hfin _ =ᵐ[μ] _
  rw [lpStepSynthesis_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  simp only [← Finset.sum_apply]
  apply eventuallyEq_sum
  intro i _
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hQ i) (hμs := hfin i)
    (c := (1 : 𝕜))] with x hx
  dsimp only [Pi.smul_apply]
  rw [hx]
  by_cases h : x ∈ Q i <;> simp [h]

/-- On each disjoint cell, the finite average takes its prescribed scalar value. -/
theorem lpFiniteAverage_eq_average_on_cell {ι : Type*} [Fintype ι]
    (hp : p ≠ ∞) (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i))
    (hfin : ∀ i, μ (Q i) ≠ ∞) (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (f : Lp 𝕜 p μ) (i : ι) :
    lpFiniteAverage hp Q hQ hfin f =ᵐ[μ.restrict (Q i)]
      fun _ => lpCellAverage hp (Q i) (hfin i) f := by
  classical
  filter_upwards [ae_restrict_of_ae (lpFiniteAverage_representative hp Q hQ hfin f),
    ae_restrict_mem (hQ i)] with x hx hxi
  rw [hx, Finset.sum_eq_single i]
  · simp [hxi]
  · intro j _ hji
    have hxj : x ∉ Q j := fun hxj => Set.disjoint_left.mp (hdisj hji) hxj hxi
    simp [hxj]
  · simp

end FiniteAverages

section AveragingInequality
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Probability-space Jensen inequality for the pth power of the norm,
 obtained directly from the finite-measure Hölder inequality. -/
theorem enorm_integral_rpow_le [IsProbabilityMeasure μ] (hp : p ≠ ∞)
    {f : X → E} (hf : AEStronglyMeasurable f μ) :
    ‖∫ x, f x ∂μ‖ₑ ^ p.toReal ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  calc
    _ ≤ (eLpNorm f p μ) ^ p.toReal :=
      ENNReal.rpow_le_rpow
        ((enorm_integral_le_lintegral_enorm f).trans
          (lintegral_enorm_le_eLpNorm_one.trans (eLpNorm_le_eLpNorm_of_exponent_le Fact.out)))
        hpR.le
    _ = _ := by
      rw [eLpNorm_eq_eLpNorm' hp0 hp hf,
        lintegral_rpow_enorm_eq_rpow_eLpNorm' hpR]

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The pointwise Jensen bound for a single cell. No regularity of its boundary
is required: finite positive measure is sufficient. -/
theorem enorm_sub_lpCellAverage_rpow_le (hp : p ≠ ∞)
    (Q : Set X) (h0 : μ Q ≠ 0) (hfin : μ Q ≠ ∞)
    (f : Lp 𝕜 p μ) (x : X) :
    ‖f x - lpCellAverage hp Q hfin f‖ₑ ^ p.toReal ≤
      (μ Q)⁻¹ * ∫⁻ z in Q, ‖f x - f z‖ₑ ^ p.toReal ∂μ := by
  letI : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hfin.lt_top⟩
  letI : NeZero (μ.restrict Q) := ⟨by
    intro h
    have H := congrArg (fun m : Measure X => m univ) h
    exact h0 (by simpa using H)⟩
  have hrepr : f x - lpCellAverage hp Q hfin f = ⨍ z in Q, f x - f z ∂μ := by
    rw [average_fun_sub (integrable_const _) (integrableOn_Lp_of_measure_ne_top f Fact.out hfin),
      average_const]
    congr 1
    simp [lpCellAverage_apply, average_eq, measureReal_def]
  rw [hrepr]
  have H := enorm_integral_rpow_le hp (f := fun z => f x - f z)
    ((stronglyMeasurable_const.sub (Lp.stronglyMeasurable f)).aestronglyMeasurable
      (μ := ((μ.restrict Q) univ)⁻¹ • μ.restrict Q))
  change ‖∫ z, f x - f z ∂((μ.restrict Q) univ)⁻¹ • μ.restrict Q‖ₑ ^ p.toReal ≤ _
  simpa only [Measure.restrict_apply_univ, lintegral_smul_measure, smul_eq_mul] using H

end AveragingInequality

section GridGeometry

/-- A half-open cell in the scalar-coordinate grid of mesh ℓ. -/
def lpGridCell {d : ℕ} (ℓ : ℝ) (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.pi univ fun i => Ico (ℓ * k i) (ℓ * (k i + 1))

theorem measurableSet_lpGridCell {d : ℕ} (ℓ : ℝ) (k : Fin d → ℤ) :
    MeasurableSet (lpGridCell ℓ k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_lpGridCell {d : ℕ} (ℓ : ℝ) (k : Fin d → ℤ) :
    volume (lpGridCell ℓ k) = ENNReal.ofReal ℓ ^ d := by
  rw [lpGridCell, Real.volume_pi_Ico]
  simp only [mul_add, mul_one, add_sub_cancel_left, Finset.prod_const, Fintype.card_fin,
    Finset.card_univ]

/-- A point belongs to precisely the cell indexed by its coordinate floors. -/
theorem mem_lpGridCell_iff {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (k : Fin d → ℤ) (x : Fin d → ℝ) :
    x ∈ lpGridCell ℓ k ↔ (fun i => ⌊x i / ℓ⌋) = k := by
  simp only [lpGridCell, Set.mem_pi, mem_univ, forall_const, mem_Ico, funext_iff]
  apply forall_congr'
  intro i
  rw [Int.floor_eq_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨(le_div_iff₀ hℓ).mpr (by nlinarith),
      (div_lt_iff₀ hℓ).mpr (by nlinarith)⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨by nlinarith [(le_div_iff₀ hℓ).mp hlo],
      by nlinarith [(div_lt_iff₀ hℓ).mp hhi]⟩

theorem pairwiseDisjoint_lpGridCell {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Pairwise (fun k l : Fin d → ℤ => Disjoint (lpGridCell ℓ k) (lpGridCell ℓ l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hkl (((mem_lpGridCell_iff hℓ k x).mp hx).symm.trans
    ((mem_lpGridCell_iff hℓ l x).mp hy))

/-- The product/sup norm gives the precise mesh bound without a positive
 dimension assumption. -/
theorem norm_sub_lt_of_mem_lpGridCell {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {k : Fin d → ℤ} {x y : Fin d → ℝ}
    (hx : x ∈ lpGridCell ℓ k) (hy : y ∈ lpGridCell ℓ k) : ‖x - y‖ < ℓ := by
  apply (pi_norm_lt_iff hℓ).mpr
  intro i
  have hx' := hx i (mem_univ i)
  have hy' := hy i (mem_univ i)
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  apply abs_lt.mpr
  constructor <;> nlinarith [hx'.1, hx'.2, hy'.1, hy'.2]

/-- Only finitely many grid cells are needed to cover a prescribed closed ball. -/
theorem finite_lpGridCell_cover {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    ∃ K : Finset (Fin d → ℤ),
      Metric.closedBall (0 : Fin d → ℝ) R ⊆ ⋃ k ∈ K, lpGridCell ℓ k := by
  classical
  let a : Fin d → ℤ := fun _ => ⌊-R / ℓ⌋
  let b : Fin d → ℤ := fun _ => ⌊R / ℓ⌋
  refine ⟨Fintype.piFinset (fun i => Finset.Icc (a i) (b i)), ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  let k : Fin d → ℤ := fun i => ⌊x i / ℓ⌋
  have hk : k ∈ Fintype.piFinset (fun i => Finset.Icc (a i) (b i)) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.floor_mono
      apply (div_le_div_iff_of_pos_right hℓ).mpr
      have hi := (norm_le_pi_norm x i).trans hx
      rw [Real.norm_eq_abs] at hi
      exact (abs_le.mp hi).1
    · apply Int.floor_mono
      apply (div_le_div_iff_of_pos_right hℓ).mpr
      have hi := (norm_le_pi_norm x i).trans hx
      rw [Real.norm_eq_abs] at hi
      exact (abs_le.mp hi).2
  exact mem_iUnion₂.mpr ⟨k, hk, (mem_lpGridCell_iff hℓ k x).mpr rfl⟩

end GridGeometry

section TranslationError
variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Changing variables z=x-h bounds a cellwise difference integral by the
translation differences in a ball of shifts. -/
theorem cell_difference_lintegral_le (f : KolmogorovRieszSpec.Space 𝕜 d p)
    {ℓ : ℝ} {Q : Set (Fin d → ℝ)} (hQ : MeasurableSet Q)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ ℓ) {x : Fin d → ℝ} (hx : x ∈ Q) :
    ∫⁻ z in Q, ‖f x - f z‖ₑ ^ p.toReal ≤
      ∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ,
        ‖f x - f (x - h)‖ₑ ^ p.toReal := by
  have hm : Measurable (fun z => ‖f x - f z‖ₑ ^ p.toReal) :=
    (measurable_const.sub (Lp.stronglyMeasurable f).measurable).enorm.pow_const _
  have heq :
      (∫⁻ h in (fun h => x - h) ⁻¹' Q, ‖f x - f (x - h)‖ₑ ^ p.toReal) =
        ∫⁻ z in Q, ‖f x - f z‖ₑ ^ p.toReal :=
    (volume.measurePreserving_sub_left x).setLIntegral_comp_preimage hQ hm
  rw [← heq]
  apply lintegral_mono_set
  intro h hh
  rw [Metric.mem_closedBall, dist_zero_right]
  simpa only [sub_sub_cancel] using hdiam x hx (x - h) hh

/-- The analytic error estimate for finitely many disjoint equal-volume cells.
This is the Jensen--Tonelli step; the scalar may be real or complex. -/
theorem lpFiniteAverage_energy_error_le {ι : Type*} [Fintype ι]
    (hp : p ≠ ∞) (Q : ι → Set (Fin d → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hfin : ∀ i, volume (Q i) ≠ ∞)
    (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (v : ℝ≥0∞) (hv0 : v ≠ 0) (hvol : ∀ i, volume (Q i) = v)
    (ℓ : ℝ) (hdiam : ∀ i, ∀ x ∈ Q i, ∀ y ∈ Q i, ‖x - y‖ ≤ ℓ)
    (f : KolmogorovRieszSpec.Space 𝕜 d p) :
    ∫⁻ x in ⋃ i, Q i, ‖f x - lpFiniteAverage hp Q hQ hfin f x‖ₑ ^ p.toReal ≤
      v⁻¹ * ∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ,
        ∫⁻ x, ‖f x - f (x - h)‖ₑ ^ p.toReal := by
  classical
  let F : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞ :=
    fun x h => ‖f x - f (x - h)‖ₑ ^ p.toReal
  have hcell (i : ι) :
      (∫⁻ x in Q i, ‖f x - lpFiniteAverage hp Q hQ hfin f x‖ₑ ^ p.toReal) ≤
        v⁻¹ * ∫⁻ x in Q i, ∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ, F x h := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hv0)]
    apply lintegral_mono_ae
    filter_upwards [lpFiniteAverage_eq_average_on_cell hp Q hQ hfin hdisj f i,
      ae_restrict_mem (hQ i)] with x hx hxi
    rw [hx]
    have H := enorm_sub_lpCellAverage_rpow_le hp (Q i) (hvol i ▸ hv0) (hfin i) f x
    rw [hvol i] at H
    exact H.trans (mul_le_mul_right (cell_difference_lintegral_le f (hQ i) (hdiam i) hxi) v⁻¹)
  have hmeas : Measurable (Function.uncurry F) := by
    exact ((Lp.stronglyMeasurable f).measurable.comp measurable_fst |>.sub
      ((Lp.stronglyMeasurable f).measurable.comp (measurable_fst.sub measurable_snd))).enorm.pow_const _
  calc
    _ = ∑ i, ∫⁻ x in Q i, ‖f x - lpFiniteAverage hp Q hQ hfin f x‖ₑ ^ p.toReal := by
      rw [lintegral_iUnion hQ hdisj, tsum_fintype]
    _ ≤ ∑ i, v⁻¹ * ∫⁻ x in Q i, ∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ, F x h :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = v⁻¹ * ∫⁻ x in ⋃ i, Q i, ∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ, F x h := by
      rw [lintegral_iUnion hQ hdisj, tsum_fintype, Finset.mul_sum]
    _ ≤ v⁻¹ * ∫⁻ x, ∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ, F x h :=
      mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _
    _ = _ := by
      rw [lintegral_lintegral_swap hmeas.aemeasurable]

/-- Power-integral formula for the restriction norm of an Lᵖ difference. -/
theorem enorm_lpRestrict_sub_rpow (hp : p ≠ ∞) (s : Set (Fin d → ℝ))
    (f g : KolmogorovRieszSpec.Space 𝕜 d p) :
    ‖lpRestrict p volume s (f - g)‖ₑ ^ p.toReal =
      ∫⁻ x in s, ‖f x - g x‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  rw [lpRestrict, KolmogorovRieszSpec.LpRestrictValue, Lp.enorm_toLp,
    eLpNorm_eq_eLpNorm' hp0 hp ((Lp.memLp (f - g)).restrict s).aestronglyMeasurable,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]
  exact lintegral_congr_ae ((ae_restrict_of_ae (Lp.coeFn_sub f g)).mono fun x hx => by
    dsimp only
    rw [hx, Pi.sub_apply])

/-- The integral of the translation error is exactly its Lᵖ norm power. -/
theorem translation_difference_energy (hp : p ≠ ∞)
    (f : KolmogorovRieszSpec.Space 𝕜 d p) (h : Fin d → ℝ) :
    ∫⁻ x, ‖f x - f (x - h)‖ₑ ^ p.toReal =
      ‖Distributions.lpTranslation p h f - f‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' hp0 hp (Lp.aestronglyMeasurable _),
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]
  apply lintegral_congr_ae
  filter_upwards [Distributions.lpTranslation_representative p h f,
    Lp.coeFn_sub (Distributions.lpTranslation p h f) f] with x hx hsub
  have hx' : Distributions.lpTranslation p h f x = f (x - h) := hx
  rw [hsub, Pi.sub_apply, hx', enorm_sub_rev]

/-- A uniform translation modulus controls the averaging error on every subset
of the cells. The convenient bound 2^d η is independent of the mesh and of the
number of cells; no tail condition is used. -/
theorem norm_lpRestrict_finiteAverage_sub_le {ι : Type*} [Fintype ι]
    (hp : p ≠ ∞) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Q : ι → Set (Fin d → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hfin : ∀ i, volume (Q i) ≠ ∞)
    (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hvol : ∀ i, volume (Q i) = ENNReal.ofReal ℓ ^ d)
    (hdiam : ∀ i, ∀ x ∈ Q i, ∀ y ∈ Q i, ‖x - y‖ ≤ ℓ)
    (f : KolmogorovRieszSpec.Space 𝕜 d p) {η : ℝ} (hη : 0 ≤ η)
    (htrans : ∀ h : Fin d → ℝ, ‖h‖ ≤ ℓ →
      ‖Distributions.lpTranslation p h f - f‖ ≤ η)
    {s : Set (Fin d → ℝ)} (hs : s ⊆ ⋃ i, Q i) :
    ‖lpRestrict p volume s (f - lpFiniteAverage hp Q hQ hfin f)‖ ≤ (2 : ℝ) ^ d * η := by
  have hpR : (1 : ℝ) ≤ p.toReal := by
    exact_mod_cast ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hpR0 : 0 < p.toReal := by linarith
  let v : ℝ≥0∞ := ENNReal.ofReal ℓ ^ d
  have hv0 : v ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hℓ)
  have hvfin : v ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hshift :
      (∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ,
        ∫⁻ x, ‖f x - f (x - h)‖ₑ ^ p.toReal) ≤
      ENNReal.ofReal η ^ p.toReal * volume (Metric.closedBall (0 : Fin d → ℝ) ℓ) := by
    rw [← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with h hh
    rw [translation_difference_energy hp f h]
    apply ENNReal.rpow_le_rpow _ hpR0.le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (htrans h (by simpa using hh))
  have hball : volume (Metric.closedBall (0 : Fin d → ℝ) ℓ) = (2 : ℝ≥0∞) ^ d * v := by
    rw [Real.volume_pi_closedBall _ hℓ.le]
    dsimp [v]
    rw [Fintype.card_fin, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_mul (by positivity), mul_pow]
    norm_num
  have hc : (2 : ℝ≥0∞) ^ d ≤ ((2 : ℝ≥0∞) ^ d) ^ p.toReal :=
    ENNReal.le_rpow_self_of_one_le (one_le_pow₀ (by norm_num)) hpR
  have henergy :
      (∫⁻ x in s, ‖f x - lpFiniteAverage hp Q hQ hfin f x‖ₑ ^ p.toReal) ≤
        ENNReal.ofReal ((2 : ℝ) ^ d * η) ^ p.toReal := by
    calc
      _ ≤ ∫⁻ x in ⋃ i, Q i, ‖f x - lpFiniteAverage hp Q hQ hfin f x‖ₑ ^ p.toReal :=
        lintegral_mono_set hs
      _ ≤ v⁻¹ * ∫⁻ h in Metric.closedBall (0 : Fin d → ℝ) ℓ,
          ∫⁻ x, ‖f x - f (x - h)‖ₑ ^ p.toReal :=
        lpFiniteAverage_energy_error_le hp Q hQ hfin hdisj v hv0 hvol ℓ hdiam f
      _ ≤ v⁻¹ * (ENNReal.ofReal η ^ p.toReal * ((2 : ℝ≥0∞) ^ d * v)) := by
        rw [← hball]
        exact mul_le_mul_right hshift _
      _ = (2 : ℝ≥0∞) ^ d * ENNReal.ofReal η ^ p.toReal := by
        calc
          _ = ((2 : ℝ≥0∞) ^ d * ENNReal.ofReal η ^ p.toReal) * (v⁻¹ * v) := by ac_rfl
          _ = _ := by rw [ENNReal.inv_mul_cancel hv0 hvfin, mul_one]
      _ ≤ ((2 : ℝ≥0∞) ^ d) ^ p.toReal * ENNReal.ofReal η ^ p.toReal :=
        mul_le_mul_left hc _
      _ = _ := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hpR0.le,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
        norm_num
  rw [← enorm_lpRestrict_sub_rpow hp s] at henergy
  have hnorm := (ENNReal.rpow_le_rpow_iff hpR0).mp henergy
  have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 : ℝ) ^ d * η)] at H
  simpa only [toReal_enorm] using H

end TranslationError


/-- Uniform translation continuity gives norm precompactness on each bounded
region by approximation with finite cell averages. -/
theorem local_compactness : KolmogorovRieszSpec.LocalCompactness.{u} := by
  intro 𝕜 _ d p _ hp A hA htrans s _hs hsbounded
  have ht : TotallyBounded (lpRestrict p volume s '' A) := by
    apply totallyBounded_of_totallyBounded_approximations
    intro ε hε
    let η : ℝ := ε / (2 * (2 : ℝ) ^ d)
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨δ, hδ, hδtrans⟩ := htrans η hη
    let ℓ : ℝ := δ / 2
    have hℓ : 0 < ℓ := half_pos hδ
    obtain ⟨R, hR⟩ := hsbounded.subset_closedBall (0 : Fin d → ℝ)
    obtain ⟨K, hK⟩ := finite_lpGridCell_cover hℓ R
    let Q : K → Set (Fin d → ℝ) := fun k => lpGridCell ℓ k.val
    have hQ : ∀ k, MeasurableSet (Q k) := fun k => measurableSet_lpGridCell ℓ k.val
    have hvol : ∀ k, volume (Q k) = ENNReal.ofReal ℓ ^ d :=
      fun k => volume_lpGridCell ℓ k.val
    have hfin : ∀ k, volume (Q k) ≠ ∞ := fun k => by
      rw [hvol k]
      exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)) := by
      intro i j hij
      exact pairwiseDisjoint_lpGridCell hℓ (fun h => hij (Subtype.ext h))
    have hdiam : ∀ i, ∀ x ∈ Q i, ∀ y ∈ Q i, ‖x - y‖ ≤ ℓ :=
      fun _ _ hx _ hy => (norm_sub_lt_of_mem_lpGridCell hℓ hx hy).le
    have hscover : s ⊆ ⋃ i, Q i := by
      intro x hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (hK (hR hx))
      exact mem_iUnion.mpr ⟨⟨k, hk⟩, hxk⟩
    let P := lpFiniteAverage (𝕜 := 𝕜) (p := p) hp Q hQ hfin
    have hP : TotallyBounded (P '' A) :=
      (isCompact_closure_lpFiniteAverage_image hp Q hQ hfin hA).totallyBounded.subset
        subset_closure
    refine ⟨lpRestrict p volume s '' (P '' A),
      hP.image (lpRestrict_lipschitz s).uniformContinuous, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨lpRestrict p volume s (P f),
      mem_image_of_mem _ (mem_image_of_mem _ hf), ?_⟩
    have he := norm_lpRestrict_finiteAverage_sub_le hp hℓ Q hQ hfin hdisj
      hvol hdiam f hη.le (fun h hh =>
        (hδtrans h (by dsimp [ℓ] at hh; linarith) f hf).le) hscover
    rw [dist_eq_norm, ← lpRestrict_sub]
    apply lt_of_le_of_lt he
    dsimp [η]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    field_simp
    nlinarith
  exact ht.closure.isCompact_of_isClosed isClosed_closure

/-- Kolmogorov--Riesz for bounded scalar Lᵖ families, including p=1. -/
theorem kolmogorovRiesz : KolmogorovRieszSpec.KolmogorovRiesz.{u} :=
  kolmogorovRiesz_of_localCompactness local_compactness

end ExpandedFA.Sobolev
