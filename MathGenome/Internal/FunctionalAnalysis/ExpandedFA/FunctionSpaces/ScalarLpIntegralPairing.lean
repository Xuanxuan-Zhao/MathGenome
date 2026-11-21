import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing

/-!
The scalar-linear integral pairing for ordinary native Lp on an arbitrary
positive measure. The construction uses Hölder multiplication into L¹ and the
Bochner integral. It does not use Lp dual representation, sigma-finiteness,
separability of the domain, or a Hilbert inner product.
-/

open MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace ExpandedFA.FunctionSpaces

abbrev ScalarLp : ScalarLpIntegralPairingSpec.ScalarLpType.{u} :=
  fun 𝕜 _ _ p μ => Lp 𝕜 p μ

/-- g ↦ (f ↦ ∫ f*g), with no conjugation even for complex scalars. -/
def lpIntegralPairing : ScalarLpIntegralPairingSpec.IntegralPairingType.{u} :=
  fun μ p q => ((ContinuousLinearMap.mul _ _).lpPairing μ p q).flip

theorem lp_ordinary_ae_identification :
    ScalarLpIntegralPairingSpec.OrdinaryAEIdentification.{u} := by
  intro X 𝕜 _ _ μ p f g hf hg
  rw [MemLp.toLp_eq_toLp_iff]
  exact ae_iff

theorem lp_measurable_representative :
    ScalarLpIntegralPairingSpec.MeasurableRepresentative.{u} := by
  intro X 𝕜 _ _ μ p F
  exact ⟨F, Lp.memLp F, (Lp.stronglyMeasurable F).measurable, Lp.toLp_coeFn F _⟩

theorem lp_source_norm : ScalarLpIntegralPairingSpec.SourceNorm.{u} := by
  intro X 𝕜 _ _ μ p f hf
  exact Lp.norm_toLp f hf

theorem lp_product_integrable : ScalarLpIntegralPairingSpec.ProductIntegrable.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ f g hf hg
  exact hf.integrable_mul hg

theorem lp_pairing_integral : ScalarLpIntegralPairingSpec.PairingIntegral.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ g f
  refine ⟨(Lp.memLp f).integrable_mul (Lp.memLp g), ?_⟩
  exact (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing_eq_integral f g

theorem lp_pairing_on_representatives :
    ScalarLpIntegralPairingSpec.PairingOnRepresentatives.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ f g hf hg
  rw [(lp_pairing_integral μ p q (hg.toLp g) (hf.toLp f)).2]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem lp_pairing_apply_bound : ScalarLpIntegralPairingSpec.PairingApplyBound.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ g f
  let B := ContinuousLinearMap.mul 𝕜 𝕜
  calc
    ‖ScalarLpIntegralPairingSpec.IntegralPairingValue μ p q g f‖ =
        ‖L1.integral (B.holder 1 f g)‖ := by
      simp only [ScalarLpIntegralPairingSpec.IntegralPairingValue,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.postcomp_apply,
        ContinuousLinearMap.holderL_apply_apply, ← L1.integral_eq', B]
    _ ≤ ‖B.holder 1 f g‖ := L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖f‖ * ‖g‖ := B.norm_holder_apply_apply_le f g
    _ ≤ 1 * ‖f‖ * ‖g‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)
          (norm_nonneg f)) (norm_nonneg g)
    _ = ‖g‖ * ‖f‖ := by rw [one_mul, mul_comm]

theorem lp_pairing_norm_bound : ScalarLpIntegralPairingSpec.PairingNormBound.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ g
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
    (lp_pairing_apply_bound μ p q g)

theorem lp_pairing_operator_norm_bound :
    ScalarLpIntegralPairingSpec.PairingOperatorNormBound.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa only [one_mul] using lp_pairing_norm_bound (𝕜 := 𝕜) μ p q g

theorem lp_pairing_scalar_linear : ScalarLpIntegralPairingSpec.PairingScalarLinear.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ c g f
  constructor
  · simp only [map_smul, smul_apply, smul_eq_mul]
  · simp only [map_smul, smul_eq_mul]

end ExpandedFA.FunctionSpaces
