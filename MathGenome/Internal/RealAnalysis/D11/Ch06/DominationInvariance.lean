import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.DominationInvariance
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch06.LinearityOrder
import MathGenome.Internal.RealAnalysis.D11.Ch05.AlgebraNull
import MathGenome.Internal.RealAnalysis.D11.Ch04.EssentialBounds

/-! Integrable domination, a.e. invariance and restriction, paper.tex:1841–1876.
All uses of native integrability go through the shared scalar bridge, retaining
actual measurability even on incomplete spaces. Quantitative estimates are
stated using the shared nonnegative integral, identified with the lower integral.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch06.DominationInvariance
open ScalarIntegral
open D11.Ch05.NonnegativeIntegral
open D11.Ch04.AeCommonException
open D11.Ch04.EssentialBounds
open D11.Ch01.ExhaustionRestriction

theorem integrable_domination : Specs.D11.Ch06.DominationInvariance.integrable_domination := by
  intro X 𝕜 _ _ _ _ μ f g hfm hg _hg0 hfg
  have hgi := (scalarIntegrable_iff μ g).mp hg
  have hfg' := (almostEverywhere_iff_native μ _).mp hfg
  refine ⟨(scalarIntegrable_iff μ f).mpr
    ⟨hfm, hgi.2.mono' hfm.aestronglyMeasurable hfg'⟩, ?_⟩
  change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖) ≤
    nonnegativeIntegral μ (fun x => ENNReal.ofReal (g x))
  simp only [integral_eq_lintegral]
  exact lintegral_mono_ae (hfg'.mono fun x hx => ENNReal.ofReal_le_ofReal hx)

theorem finite_support_bound : Specs.D11.Ch06.DominationInvariance.finite_support_bound := by
  intro X 𝕜 _ _ _ _ μ f E M hfm hE hEfin hsupp hbound
  have hb := (almostEverywhere_iff_native μ _).mp hbound
  have hle : (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) ≤ ENNReal.ofReal M * μ E := by
    calc
      (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) ≤
          ∫⁻ x, E.indicator (fun _ => ENNReal.ofReal M) x ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hb] with x hx
        by_cases hxE : x ∈ E
        · simpa only [indicator_of_mem hxE] using ENNReal.ofReal_le_ofReal hx
        · simp [hxE, hsupp x hxE]
      _ = ENNReal.ofReal M * μ E := lintegral_indicator_const hE _
  refine ⟨⟨hfm, ?_⟩, ?_⟩
  · change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖) < ∞
    rw [integral_eq_lintegral]
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin)
  · change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖) ≤
      ENNReal.ofReal M * μ E
    simpa only [integral_eq_lintegral] using hle

theorem bounded_multiplier : Specs.D11.Ch06.DominationInvariance.bounded_multiplier := by
  intro X 𝕜 _ _ _ _ μ f h hf hhm hh
  have hfi := (scalarIntegrable_iff μ f).mp hf
  have hhfin : essentialSupNorm μ h < ∞ := hh
  have hb := (almostEverywhere_iff_native μ _).mp
    (essential_bound_attained μ h hhfin)
  refine ⟨(scalarIntegrable_iff μ _).mpr
    ⟨hhm.mul hfi.1, hfi.2.bdd_mul hhm.aestronglyMeasurable hb⟩, ?_⟩
  change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖h x * f x‖) ≤
    essentialSupNorm μ h * nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖)
  simp only [integral_eq_lintegral]
  calc
    (∫⁻ x, ENNReal.ofReal ‖h x * f x‖ ∂μ) ≤
        ∫⁻ x, essentialSupNorm μ h * ENNReal.ofReal ‖f x‖ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hb] with x hx
      rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      apply mul_le_mul' _ le_rfl
      calc
        ENNReal.ofReal ‖h x‖ ≤ ENNReal.ofReal (essentialSupNorm μ h).toReal :=
          ENNReal.ofReal_le_ofReal hx
        _ = essentialSupNorm μ h := ENNReal.ofReal_toReal hhfin.ne
    _ = essentialSupNorm μ h * (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) :=
      lintegral_const_mul' _ _ hhfin.ne

theorem ae_integrable_iff : Specs.D11.Ch06.DominationInvariance.ae_integrable_iff := by
  intro X 𝕜 _ _ _ _ μ f g hfm hgm hfg
  change scalarIntegrable μ f ↔ scalarIntegrable μ g
  rw [native_integrable_iff μ f hfm, native_integrable_iff μ g hgm]
  exact integrable_congr ((aeEq_iff_native μ f g).mp hfg)

theorem ae_integral_eq : Specs.D11.Ch06.DominationInvariance.ae_integral_eq := by
  intro X 𝕜 _ _ _ _ μ f g hf hg hfg
  have h := (aeEq_iff_native μ f g).mp hfg
  constructor
  · exact integral_congr_ae h
  · change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖) =
      nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖g x‖)
    simp only [integral_eq_lintegral]
    exact lintegral_congr_ae (h.mono fun x hx => congrArg (fun z => ENNReal.ofReal ‖z‖) hx)

theorem restriction : Specs.D11.Ch06.DominationInvariance.restriction := by
  intro X 𝕜 _ _ _ _ μ f hf E hE
  have hfi := (scalarIntegrable_iff μ f).mp hf
  have hr : scalarIntegrable (restrictOnSpace μ E) f :=
    (scalarIntegrable_iff _ f).mpr ⟨hfi.1, hfi.2.restrict⟩
  have hi : scalarIntegrable μ (E.indicator f) :=
    (scalarIntegrable_iff μ _).mpr ⟨hfi.1.indicator hE, hfi.2.indicator hE⟩
  refine ⟨hr, hi, (integral_indicator hE).symm, ?_⟩
  change nonnegativeIntegral (restrictOnSpace μ E) (fun x => ENNReal.ofReal ‖f x‖) =
    nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖E.indicator f x‖)
  simp only [integral_eq_lintegral]
  have heq : (fun x => ENNReal.ofReal ‖E.indicator f x‖) =
      E.indicator (fun x => ENNReal.ofReal ‖f x‖) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [heq]
  exact (lintegral_indicator hE _).symm

theorem restriction_subtype : Specs.D11.Ch06.DominationInvariance.restriction_subtype := by
  intro X 𝕜 _ _ _ _ μ f hf E hE
  have hfi := (scalarIntegrable_iff μ f).mp hf
  have hr : scalarIntegrable (restrictOnSpace μ E) f :=
    (scalarIntegrable_iff _ f).mpr ⟨hfi.1, hfi.2.restrict⟩
  have hs : scalarIntegrable (restrictToSubtype μ E) (fun x : E => f x) :=
    (scalarIntegrable_iff _ _).mpr ⟨hfi.1.comp measurable_subtype_coe,
      (integrableOn_iff_comap_subtypeVal hE).mp hfi.2.integrableOn⟩
  refine ⟨hs, hr, integral_subtype_comap hE f, ?_⟩
  change nonnegativeIntegral (restrictToSubtype μ E) (fun x : E => ENNReal.ofReal ‖f x‖) =
    nonnegativeIntegral (restrictOnSpace μ E) (fun x => ENNReal.ofReal ‖f x‖)
  simp only [integral_eq_lintegral]
  simpa only [restrictToSubtype, restrictOnSpace] using
    (lintegral_subtype_comap (μ := μ) hE (fun x => ENNReal.ofReal ‖f x‖))

theorem null_removal : Specs.D11.Ch06.DominationInvariance.null_removal := by
  intro X 𝕜 _ _ _ _ μ f hf N hN hNnull
  obtain ⟨hr, hi, hri, hria⟩ := restriction μ f hf Nᶜ hN.compl
  have hmeasure : restrictOnSpace μ Nᶜ = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact ae_iff.mpr (by simpa using hNnull)
  have heq : scalarIntegral (restrictOnSpace μ Nᶜ) f hr = scalarIntegral μ f hf := by
    change (∫ x, f x ∂restrictOnSpace μ Nᶜ) = ∫ x, f x ∂μ
    rw [hmeasure]
  have heqa : nonnegativeIntegral (restrictOnSpace μ Nᶜ) (fun x => ENNReal.ofReal ‖f x‖) =
      nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖) := by rw [hmeasure]
  exact ⟨hr, hi, heq, hri.symm.trans heq, heqa, hria.symm.trans heqa⟩

end D11.Ch06.DominationInvariance
