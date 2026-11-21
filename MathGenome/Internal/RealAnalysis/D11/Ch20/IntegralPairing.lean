import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral

/-! The bilinear integral pairing for arbitrary positive measures.
Hölder's inequality gives an L¹ product; integration is a contraction on L¹.
The continuous linear maps supply scalar linearity in both arguments, and the
final theorem transfers this pairing to the original measurable a.e. quotient.
There is no conjugation and no finiteness or completeness assumption on μ.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch20.IntegralPairing
open Specs.D11.Ch10.QuotientConstruction
open Specs.D11.Ch06.ScalarIntegral

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]

/-- g ↦ T_g, with T_g(f) = ∫ f*g. This is scalar linear in both slots. -/
def pairing (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] : Lp 𝕜 q μ →L[𝕜] Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q).flip

theorem product_integrable : Specs.D11.Ch20.IntegralPairing.product_integrable := by
  intro X 𝕜 _ _ _ _ μ p q _ f g
  apply (D11.Ch06.ScalarIntegral.native_integrable_iff μ _
    (f.property.1.mul g.property.1)).mpr
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul 𝕜 𝕜).memLp_of_bilin 1 f.property.2 g.property.2)

theorem pairing_eq_integral : Specs.D11.Ch20.IntegralPairing.pairing_eq_integral := by
  intro X 𝕜 _ _ μ p q _ _ _ g f
  refine ⟨memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul 𝕜 𝕜).memLp_of_bilin 1 (Lp.memLp f) (Lp.memLp g)), ?_⟩
  exact (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing_eq_integral f g

theorem pairing_on_raw : Specs.D11.Ch20.IntegralPairing.pairing_on_raw := by
  intro X 𝕜 _ _ _ _ μ p q _ _ _ f g
  refine ⟨product_integrable μ p q f g, ?_⟩
  change pairing μ p q (g.property.2.toLp g.val) (f.property.2.toLp f.val) =
    ∫ x, f.val x * g.val x ∂μ
  calc
    _ = ∫ x, (f.property.2.toLp f.val) x * (g.property.2.toLp g.val) x ∂μ :=
      (pairing_eq_integral μ p q _ _).2
    _ = ∫ x, f.val x * g.val x ∂μ :=
      integral_congr_ae ((MemLp.coeFn_toLp f.property.2).mul
        (MemLp.coeFn_toLp g.property.2))

/-- Hölder followed by the contraction estimate for integration on L¹. -/
theorem norm_pairing_apply_le (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (g : Lp 𝕜 q μ) (f : Lp 𝕜 p μ) :
    ‖pairing μ p q g f‖ ≤ ‖g‖ * ‖f‖ := by
  have hi := L1.norm_integral_le ((ContinuousLinearMap.mul 𝕜 𝕜).holder 1 f g)
  have hh := (ContinuousLinearMap.mul 𝕜 𝕜).norm_holder_apply_apply_le (r := 1) f g
  have hm : ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  change ‖L1.integralCLM' 𝕜 ((ContinuousLinearMap.mul 𝕜 𝕜).holder 1 f g)‖ ≤ _
  rw [← L1.integral_eq']
  calc
    _ ≤ ‖(ContinuousLinearMap.mul 𝕜 𝕜).holder 1 f g‖ := hi
    _ ≤ ‖ContinuousLinearMap.mul 𝕜 𝕜‖ * ‖f‖ * ‖g‖ := hh
    _ ≤ 1 * ‖f‖ * ‖g‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (norm_nonneg _))
        (norm_nonneg _)
    _ = ‖g‖ * ‖f‖ := by rw [one_mul, mul_comm]

theorem pairing_norm_bound : Specs.D11.Ch20.IntegralPairing.pairing_norm_bound := by
  intro X 𝕜 _ _ μ p q _ _ _ g
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
    (norm_pairing_apply_le μ p q g)

section OrdinaryQuotient
variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]
open D11.Ch10.QuotientConstruction

/-- The same pairing on the literal ordinary measurable a.e. quotient. -/
def quotientPairing (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] :
    QuotientLp (𝕜 := 𝕜) μ q →L[𝕜] QuotientLp (𝕜 := 𝕜) μ p →L[𝕜] 𝕜 :=
  (((pairing μ p q).flip.comp (nativeLinearIsometryEquiv μ p).toLinearIsometry.toContinuousLinearMap).flip).comp
    (nativeLinearIsometryEquiv μ q).toLinearIsometry.toContinuousLinearMap

theorem quotientPairing_apply (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (g : QuotientLp (𝕜 := 𝕜) μ q) (f : QuotientLp (𝕜 := 𝕜) μ p) :
    quotientPairing μ p q g f = pairing μ p q
      (nativeLinearIsometryEquiv μ q g) (nativeLinearIsometryEquiv μ p f) := rfl

theorem quotientPairing_norm_bound (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (g : QuotientLp (𝕜 := 𝕜) μ q) : ‖quotientPairing μ p q g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  rw [quotientPairing_apply]
  simpa only [LinearIsometryEquiv.norm_map] using norm_pairing_apply_le μ p q
    (nativeLinearIsometryEquiv μ q g) (nativeLinearIsometryEquiv μ p f)

theorem pairing_on_ordinary_quotient :
    Specs.D11.Ch20.IntegralPairing.pairing_on_ordinary_quotient := by
  intro X 𝕜 _ _ _ _ μ p q _ _ _
  refine ⟨quotientNormedAddCommGroup μ p, quotientNormedSpace μ p,
    quotientNormedAddCommGroup μ q, quotientNormedSpace μ q,
    nativeLinearIsometryEquiv μ p, nativeLinearIsometryEquiv μ q,
    quotientPairing μ p q, nativeLinearIsometryEquiv_classOf μ p,
    nativeLinearIsometryEquiv_classOf μ q, norm_classOf μ p, norm_classOf μ q, ?_,
    quotientPairing_norm_bound μ p q⟩
  intro f g
  simpa only [quotientPairing_apply, nativeLinearIsometryEquiv_classOf,
    pairing, Specs.D11.Ch20.IntegralPairing.pairing_value] using
    pairing_on_raw μ p q f g

end OrdinaryQuotient
end D11.Ch20.IntegralPairing
