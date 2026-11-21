import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.HilbertBilinearBridge
import MathGenome.Internal.RealAnalysis.D11.Ch20.L2HilbertInterface
import MathGenome.Internal.RealAnalysis.D11.Ch20.HilbertRiesz
import MathGenome.Internal.RealAnalysis.D11.Ch20.IntegralPairing

open MeasureTheory
open scoped ENNReal ComplexConjugate
universe u
noncomputable section
namespace D11.Ch20.HilbertBilinearBridge
open Specs.D11.Ch10.QuotientConstruction
open D11.Ch10.QuotientConstruction

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Pointwise conjugation on native L², bundled with its exact scalar law. -/
def nativeConjugation (μ : Measure X) : Lp 𝕜 2 μ ≃ₗᵢ⋆[𝕜] Lp 𝕜 2 μ where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' f g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g,
      Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g]
      with x h1 h2 h3 h4 h5
    simpa only [Pi.star_apply, h2, h3, Pi.add_apply, h4, h5, star_add] using h1
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
      Lp.coeFn_smul (star c) (star f), Lp.coeFn_star f] with x h1 h2 h3 h4
    simpa only [Pi.star_apply, h2, h3, Pi.smul_apply, h4, star_smul, starRingEnd_apply] using h1
  norm_map' f := by
    change ‖star f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

/-- Conjugation on the original quotient, via the representative-preserving isometry. -/
def conjugation (μ : Measure X) :
    QuotientLp (𝕜 := 𝕜) μ 2 ≃ₗᵢ⋆[𝕜] QuotientLp (𝕜 := 𝕜) μ 2 :=
  ((nativeLinearIsometryEquiv μ 2).trans (nativeConjugation μ)).trans
    (nativeLinearIsometryEquiv μ 2).symm

theorem conjugation_classOf (μ : Measure X) (f : Raw (𝕜 := 𝕜) μ 2) :
    ∃ hc : Measurable (fun x => conj (f.val x)) ∧
        MemLp (fun x => conj (f.val x)) 2 μ,
      conjugation μ (classOf f) = classOf ⟨fun x => conj (f.val x), hc⟩ := by
  refine ⟨⟨(RCLike.continuous_conj.measurable.comp f.property.1), f.property.2.star⟩, ?_⟩
  apply (nativeLinearIsometryEquiv μ 2).injective
  simp only [conjugation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, nativeLinearIsometryEquiv_classOf]
  change star (f.property.2.toLp f.val) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f.property.2.toLp f.val),
    MemLp.coeFn_toLp f.property.2,
    MemLp.coeFn_toLp (f.property.2.star)] with x hs hf hc
  exact hs.trans ((congrArg star hf).trans hc.symm)

theorem conjugation_involutive (μ : Measure X) (f : QuotientLp (𝕜 := 𝕜) μ 2) :
    conjugation μ (conjugation μ f) = f := by
  simp [conjugation, nativeConjugation]

/-- The bilinear pairing with the conjugate vector is the Hilbert functional. -/
theorem pairing_conjugation (μ : Measure X) (h f : QuotientLp (𝕜 := 𝕜) μ 2) :
    IntegralPairing.quotientPairing μ 2 2 (conjugation μ h) f = inner 𝕜 h f := by
  rw [IntegralPairing.quotientPairing_apply]
  change Specs.D11.Ch20.IntegralPairing.pairing_value μ 2 2 _ _ = _
  rw [(IntegralPairing.pairing_eq_integral μ 2 2 _ _).2]
  simp only [conjugation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change (∫ x, (nativeLinearIsometryEquiv μ 2 f) x *
      (star (nativeLinearIsometryEquiv μ 2 h)) x ∂μ) =
    ∫ x, inner 𝕜 ((nativeLinearIsometryEquiv μ 2 h) x)
      ((nativeLinearIsometryEquiv μ 2 f) x) ∂μ
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (nativeLinearIsometryEquiv μ 2 h)] with x hx
  simp only [hx, Pi.star_apply, RCLike.inner_apply, starRingEnd_apply]

/-- Hilbert vectors and bilinear densities, with both norms and scalar laws,
on the ordinary a.e. quotient for every positive measure. -/
theorem hilbert_bilinear_bridge :
    Specs.D11.Ch20.HilbertBilinearBridge.hilbert_bilinear_bridge := by
  intro X 𝕜 _ _ _ _ μ
  let Q := QuotientLp (𝕜 := 𝕜) μ 2
  let C := conjugation (𝕜 := 𝕜) μ
  let H := (InnerProductSpace.toDual 𝕜 Q).symm
  let G : (Q →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] Q := H.trans C
  let B := IntegralPairing.quotientPairing (𝕜 := 𝕜) μ 2 2
  have hrep (ℓ : Q →L[𝕜] 𝕜) (f : Q) : ℓ f = inner 𝕜 (H ℓ) f :=
    (InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜)).symm
  have brep (ℓ : Q →L[𝕜] 𝕜) (f : Q) : ℓ f = B (G ℓ) f := by
    rw [hrep]
    exact (pairing_conjugation μ (H ℓ) f).symm
  refine ⟨quotientNormedAddCommGroup μ 2,
    L2HilbertInterface.quotientInnerProductSpace μ,
    nativeLinearIsometryEquiv μ 2, C, H, G, B,
    nativeLinearIsometryEquiv_classOf μ 2, norm_classOf μ 2,
    D11.Ch10.Completeness.quotientCompleteSpace μ 2,
    conjugation_classOf μ, conjugation_involutive μ,
    L2HilbertInterface.inner_classOf μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g
    simpa only [B, IntegralPairing.quotientPairing_apply,
      nativeLinearIsometryEquiv_classOf, IntegralPairing.pairing,
      Specs.D11.Ch20.IntegralPairing.pairing_value] using
      IntegralPairing.pairing_on_raw μ 2 2 f g
  · intro ℓ
    rfl
  · intro ℓ f
    exact ⟨hrep ℓ f, brep ℓ f⟩
  · intro ℓ
    exact ⟨H.norm_map ℓ, G.norm_map ℓ⟩
  · intro ℓ h hh
    apply ext_inner_right 𝕜
    intro f
    exact (hh f).symm.trans (hrep ℓ f)
  · intro ℓ g hg
    obtain ⟨ℓ', rfl⟩ := G.surjective g
    apply congrArg G
    apply ContinuousLinearMap.ext
    intro f
    exact (brep ℓ' f).trans (hg f).symm

end D11.Ch20.HilbertBilinearBridge
