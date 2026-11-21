import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullSigmafiniteBridge
import MathGenome.Internal.RealAnalysis.D11.Ch20.LocalNullVariant
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
universe u
namespace D11.Ch20.LocalNullSigmafiniteBridge

open D11.Ch20.LocalNullVariant

theorem null_locallyNull : Specs.D11.Ch20.LocalNullSigmafiniteBridge.null_locallyNull := by
  intro X _ μ N hN hz
  exact ⟨hN, fun E _ _ => measure_mono_null inter_subset_left hz⟩

theorem locallyNull_iff_null : Specs.D11.Ch20.LocalNullSigmafiniteBridge.locallyNull_iff_null := by
  intro X _ μ _ N
  constructor
  · intro hN
    obtain ⟨F, hF, _, hcover⟩ :=
      (D11.Ch01.ExhaustionRestriction.sigmaFinite_iff_increasing_exhaustion μ).mp
        inferInstance
    refine ⟨hN.1, ?_⟩
    have hzero : μ (⋃ n, N ∩ F n) = 0 :=
      measure_iUnion_null fun n => hN.2 (F n) (hF n).1 (hF n).2
    simpa only [← inter_iUnion, hcover, inter_univ] using hzero
  · rintro ⟨hN, hz⟩
    exact null_locallyNull μ N hN hz

/-- Equality of null ideals on measurable sets gives equality of the full
a.e. filters via measurable null envelopes, without completing the space. -/
theorem testingMeasure_ae_eq {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] : ae (TestingMeasure μ) = ae μ := by
  apply le_antisymm
  · apply Measure.AbsolutelyContinuous.ae_le
    apply Measure.AbsolutelyContinuous.mk
    intro N hN hz
    exact (testingMeasure_null_iff μ N hN).mpr (null_locallyNull μ N hN hz)
  · apply Measure.AbsolutelyContinuous.ae_le
    apply Measure.AbsolutelyContinuous.mk
    intro N hN hz
    exact ((locallyNull_iff_null μ N).mp
      ((testingMeasure_null_iff μ N hN).mp hz)).2

/-- At exponent infinity the norm depends only on the a.e. filter. The
measurability hypothesis here is actual strong measurability, for both measures. -/
lemma infinityNorm_congr {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ ν : Measure X) (h : ae μ = ae ν) (f : X → 𝕜) (hf : StronglyMeasurable f) :
    eLpNorm f ∞ μ = eLpNorm f ∞ ν := by
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable,
    eLpNorm_exponent_top hf.aestronglyMeasurable]
  simp only [eLpNormEssSup, essSup, h]

lemma infinityMemLp_congr {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ ν : Measure X) (h : ae μ = ae ν) (q : Lp 𝕜 ∞ μ) : MemLp q ∞ ν := by
  change eLpNorm q ∞ ν < ∞
  rw [← infinityNorm_congr μ ν h q (Lp.stronglyMeasurable q)]
  exact Lp.memLp q

/-- Change the measure of an L-infinity class using the same strongly
measurable representative. -/
def changeInfinityMeasure {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ ν : Measure X) (h : ae μ = ae ν) (q : Lp 𝕜 ∞ μ) : Lp 𝕜 ∞ ν :=
  (infinityMemLp_congr μ ν h q).toLp q

lemma changeInfinityMeasure_coeFn {X : Type u} [MeasurableSpace X] {𝕜 : Type}
    [RCLike 𝕜] (μ ν : Measure X) (h : ae μ = ae ν) (q : Lp 𝕜 ∞ μ) :
    changeInfinityMeasure μ ν h q =ᵐ[ν] q :=
  (infinityMemLp_congr μ ν h q).coeFn_toLp

def infinityMeasureEquiv {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ ν : Measure X) (h : ae μ = ae ν) : Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] Lp 𝕜 ∞ ν where
  toFun := changeInfinityMeasure μ ν h
  invFun := changeInfinityMeasure ν μ h.symm
  left_inv q := by
    apply Lp.ext
    have hq := changeInfinityMeasure_coeFn μ ν h q
    exact (changeInfinityMeasure_coeFn ν μ h.symm _).trans
      (hq.filter_mono h.le)
  right_inv q := by
    apply Lp.ext
    have hq := changeInfinityMeasure_coeFn ν μ h.symm q
    exact (changeInfinityMeasure_coeFn μ ν h _).trans
      (hq.filter_mono h.ge)
  map_add' q r := by
    apply Lp.ext
    have hadd := Lp.coeFn_add q r
    rw [h] at hadd
    filter_upwards [changeInfinityMeasure_coeFn μ ν h (q + r), hadd,
      Lp.coeFn_add (changeInfinityMeasure μ ν h q) (changeInfinityMeasure μ ν h r),
      changeInfinityMeasure_coeFn μ ν h q,
      changeInfinityMeasure_coeFn μ ν h r] with x hx ha hb hq hr
    exact (hx.trans ha).trans ((congrArg₂ (· + ·) hq hr).symm.trans hb.symm)
  map_smul' c q := by
    apply Lp.ext
    have hsmul := Lp.coeFn_smul c q
    rw [h] at hsmul
    filter_upwards [changeInfinityMeasure_coeFn μ ν h (c • q), hsmul,
      Lp.coeFn_smul c (changeInfinityMeasure μ ν h q),
      changeInfinityMeasure_coeFn μ ν h q] with x hx hs ht hq
    exact (hx.trans hs).trans ((congrArg (c • ·) hq).symm.trans ht.symm)
  norm_map' q := by
    change ‖(infinityMemLp_congr μ ν h q).toLp q‖ = ‖q‖
    rw [Lp.norm_toLp,
      ← infinityNorm_congr μ ν h q (Lp.stronglyMeasurable q), Lp.norm_def]

/-- The canonical bridge keeps the same scalar representative. -/
def sigmaFiniteNativeEquiv {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] : LocalLInfinity 𝕜 μ ≃ₗᵢ[𝕜] Lp 𝕜 ∞ μ :=
  infinityMeasureEquiv (TestingMeasure μ) μ (testingMeasure_ae_eq μ)

lemma sigmaFiniteNativeEquiv_classOf {X : Type u} [MeasurableSpace X]
    {𝕜 : Type} [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (f : BoundedMeasurable X 𝕜) :
    sigmaFiniteNativeEquiv μ (ClassOf μ f) =
      (Specs.D11.Ch20.LocalNullSigmafiniteBridge.ordinaryMemLp μ f).toLp f.val := by
  apply Lp.ext
  have hf := (boundedMemLp μ f).coeFn_toLp
  rw [testingMeasure_ae_eq μ] at hf
  exact ((changeInfinityMeasure_coeFn (TestingMeasure μ) μ
    (testingMeasure_ae_eq μ) (ClassOf μ f)).trans hf).trans
      (Specs.D11.Ch20.LocalNullSigmafiniteBridge.ordinaryMemLp μ f).coeFn_toLp.symm

theorem native_isometry : Specs.D11.Ch20.LocalNullSigmafiniteBridge.native_isometry := by
  intro X _ 𝕜 _ μ _
  exact ⟨sigmaFiniteNativeEquiv μ, sigmaFiniteNativeEquiv_classOf μ⟩

/-- Compose with the accepted Chapter 10 identification to reach the literal
ordinary raw-function quotient, with its original essential norm. -/
theorem quotient_isometry : Specs.D11.Ch20.LocalNullSigmafiniteBridge.quotient_isometry := by
  intro X _ 𝕜 _ μ _
  refine ⟨D11.Ch10.QuotientConstruction.quotientNormedAddCommGroup μ ∞,
    D11.Ch10.QuotientConstruction.quotientNormedSpace μ ∞,
    (sigmaFiniteNativeEquiv μ).trans
      (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ ∞).symm,
    ?_, D11.Ch10.QuotientConstruction.norm_classOf μ ∞⟩
  intro f
  apply (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ ∞).injective
  change (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ ∞)
      ((D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ ∞).symm
        (sigmaFiniteNativeEquiv μ (ClassOf μ f))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf,
    sigmaFiniteNativeEquiv_classOf]
  rfl

end D11.Ch20.LocalNullSigmafiniteBridge
