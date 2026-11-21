import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Wiener
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Characters

noncomputable section
open MeasureTheory
namespace ExpandedFA.BanachAlgebra.Wiener
open Specs.ExpandedFA.BanachAlgebra.Wiener

set_option maxHeartbeats 800000

lemma integer_hom_apply (γ : ZGroup →ₜ* Circle) (n : ℤ) :
    γ (Multiplicative.ofAdd n) = γ (Multiplicative.ofAdd (1 : ℤ)) ^ n := by
  rw [← map_zpow]
  congr 1
  simp only [← ofAdd_zsmul, zsmul_eq_mul, mul_one, Int.cast_id]

theorem integer_group_characters : IntegerGroupCharacters := by
  intro γ
  refine ⟨γ (Multiplicative.ofAdd (1 : ℤ)), integer_hom_apply γ, ?_⟩
  intro z hz
  simpa using (hz 1).symm

theorem sequence_identification : SequenceIdentification := by
  constructor
  · intro a
    exact (integrable_count_iff (α := ZGroup)).mp (L1.integrable_coeFn a)
  · intro a ha
    have hi : Integrable (fun x : ZGroup => a x.toAdd) counting :=
      integrable_count_iff.mpr ha
    let h := memLp_one_iff_integrable.mpr hi
    refine ⟨h.toLp _, fun n => ?_⟩
    exact Measure.ae_count_iff.mp h.coeFn_toLp (Multiplicative.ofAdd n)

theorem sequence_norm : SequenceNorm := by
  intro a
  rw [L1.norm_eq_integral_norm, integral_countable (L1.integrable_coeFn a).norm]
  change (∑' x : ZGroup, counting.real {x} • ‖a x‖) = _
  have hcount (x : ZGroup) : counting.real {x} = 1 := by
    simp [counting, measureReal_def]
  simp only [hcount, one_smul]
  exact (Multiplicative.ofAdd.tsum_eq (fun x : ZGroup => ‖a x‖)).symm

theorem convolution_coefficients : ConvolutionCoefficients := by
  intro a b n
  have hp := GroupAlgebraCharacters.convolution_pointwise counting a b
  have heq := Measure.ae_count_iff.mp hp.2 (Multiplicative.ofAdd n)
  have hi := Measure.ae_count_iff.mp hp.1 (Multiplicative.ofAdd n)
  change coefficient (convolution a b) n = _ at heq
  rw [heq]
  dsimp only
  rw [integral_countable hi]
  change (∑' x : ZGroup, counting.real {x} • (a x * b (x⁻¹ * Multiplicative.ofAdd n))) = _
  have hcount (x : ZGroup) : counting.real {x} = 1 := by
    simp [counting, measureReal_def]
  simp only [hcount, one_smul]
  rw [← Multiplicative.ofAdd.tsum_eq (fun x : ZGroup => a x * b (x⁻¹ * Multiplicative.ofAdd n))]
  apply tsum_congr
  intro k
  change a (Multiplicative.ofAdd k) * b (Multiplicative.ofAdd (-k + n)) =
    a (Multiplicative.ofAdd k) * b (Multiplicative.ofAdd (n - k))
  rw [sub_eq_neg_add]

theorem absolute_fourier_convergence : AbsoluteFourierConvergence := by
  intro a ha z
  simpa only [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one] using ha

lemma delta_apply (x : ZGroup) : delta x = if x = 1 then 1 else 0 := by
  have h := Measure.ae_count_iff.mp (indicatorConstLp_coeFn (p := 1)
    (μ := counting) (hs := measurableSet_singleton (1 : ZGroup))
    (hμs := by simp [counting]) (c := (1 : ℂ))) x
  simpa [delta, Set.indicator, Set.mem_singleton_iff] using h

lemma norm_delta : ‖delta‖ = 1 := by
  simp [delta, norm_indicatorConstLp, measureReal_def, counting]

lemma convolution_delta_left (a : L1) : convolution delta a = a := by
  change (∫ x, delta x • ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.translate counting x a ∂counting) = a
  calc
    _ = ∫ x, ({1} : Set ZGroup).indicator (fun _ => a) x ∂counting := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x = 1
        · subst x; simp [delta_apply]
        · simp [delta_apply, hx, Set.indicator_of_notMem]
    _ = a := by
      rw [integral_indicator (measurableSet_singleton _), integral_singleton]
      simp [measureReal_def, counting]

theorem convolution_identity : ConvolutionIdentity := by
  refine ⟨norm_delta, fun a => ⟨convolution_delta_left a, ?_⟩⟩
  exact (ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.convolution_comm counting a delta).trans (convolution_delta_left a)

/-- The circle evaluation with the positive Fourier-series convention.
The upstream group transform uses the conjugate, hence the inverse here. -/
def integerCharacter (z : Circle) : ZGroup →ₜ* Circle where
  toFun x := z⁻¹ ^ x.toAdd
  map_one' := by simp
  map_mul' x y := by simp [zpow_add]
  continuous_toFun := continuous_of_discreteTopology

lemma integerCharacter_apply (z : Circle) (n : ℤ) :
    integerCharacter z (Multiplicative.ofAdd n) = z⁻¹ ^ n := rfl

lemma fourier_eq_group (a : L1) (z : Circle) :
    fourier a z = ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.fourierValue counting (integerCharacter z) a := by
  rw [ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.fourierValue, Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.fourierValue,
    integral_countable (ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.fourier_integrable counting (integerCharacter z) a)]
  change (∑' n : ℤ, a (Multiplicative.ofAdd n) * (z : ℂ) ^ n) = _
  apply tsum_congr
  intro x
  change a (Multiplicative.ofAdd x) * (z : ℂ) ^ x =
    counting.real {(Multiplicative.ofAdd x)} •
      (a (Multiplicative.ofAdd x) * star ((z⁻¹ ^ x : Circle) : ℂ))
  have hc : counting.real {(Multiplicative.ofAdd x)} = 1 := by
    simp [measureReal_def, counting]
  rw [hc, one_smul, Circle.coe_zpow, Circle.coe_inv_eq_conj]
  simp

lemma integerCharacter_injective : Function.Injective integerCharacter := by
  intro z w h
  have h1 := congrArg (fun γ : ZGroup →ₜ* Circle => γ (Multiplicative.ofAdd (1 : ℤ))) h
  simpa [integerCharacter_apply] using h1

lemma integerCharacter_surjective : Function.Surjective integerCharacter := by
  intro γ
  refine ⟨(γ (Multiplicative.ofAdd (1 : ℤ)))⁻¹, ?_⟩
  apply DFunLike.ext
  intro x
  change (γ (Multiplicative.ofAdd (1 : ℤ)))⁻¹⁻¹ ^ x.toAdd = γ x
  rw [inv_inv]
  exact (integer_hom_apply γ x.toAdd).symm

theorem character_classification : CharacterClassification := by
  constructor
  · intro z
    obtain ⟨L, hL, hχ, _⟩ :=
      (GroupAlgebraCharacters.character_classification counting).1 (integerCharacter z)
    exact ⟨L.toLinearMap, hχ, fun a => (hL a).trans (fourier_eq_group a z).symm⟩
  · intro χ hχ
    obtain ⟨⟨γ, hγ, _⟩, _⟩ := (GroupAlgebraCharacters.character_classification counting).2 χ hχ
    obtain ⟨z, rfl⟩ := integerCharacter_surjective γ
    refine ⟨z, fun a => (hγ a).trans (fourier_eq_group a z).symm, ?_⟩
    intro w hw
    apply integerCharacter_injective
    apply GroupAlgebraCharacters.fourier_injective counting
    intro a
    exact (fourier_eq_group a w).symm.trans ((hw a).symm.trans (hγ a))

/-! The convolution ring is unital on this group. The identity chosen by
`IsUnital` is proved equal to the actual point mass before using spectra. -/
local instance : NonUnitalNormedCommRing L1 := GroupAlgebraCharacters.convolutionCommRing counting
local instance : IsUnital L1 :=
  ⟨⟨delta, fun a => ⟨convolution_delta_left a,
    (GroupAlgebraCharacters.convolution_comm counting a delta).trans (convolution_delta_left a)⟩⟩⟩
local instance : NormedCommRing L1 := IsUnital.toNormedCommRing

lemma one_eq_delta : (1 : L1) = delta :=
  (convolution_delta_left 1).symm.trans (mul_one delta)

local instance : Algebra ℂ L1 := Algebra.ofModule
  (GroupAlgebraCharacters.convolution_smul_left counting)
  (GroupAlgebraCharacters.convolution_smul_right counting)
local instance : NormedAlgebra ℂ L1 where
  norm_smul_le := norm_smul_le
local instance : NormOneClass L1 := ⟨by rw [one_eq_delta]; exact norm_delta⟩
local instance : Nontrivial L1 := NormOneClass.nontrivial

lemma unitalSpectrum_eq_native (a : L1) : unitalSpectrum a = spectrum ℂ a := by
  ext w
  change (¬ ∃ b, convolution (w • delta - a) b = delta ∧
    convolution b (w • delta - a) = delta) ↔ _
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, one_eq_delta]
  apply not_congr
  constructor
  · rintro ⟨b, hab, _⟩
    apply isUnit_iff_exists_inv.mpr
    exact ⟨b, hab.trans one_eq_delta.symm⟩
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    exact ⟨b, hb.trans one_eq_delta, (mul_comm _ _).trans (hb.trans one_eq_delta)⟩

theorem spectrum_formula : SpectrumFormula := by
  intro a
  rw [unitalSpectrum_eq_native]
  have hs := Characters.spectrum_characters L1 a
  change spectrum ℂ a = _ at hs
  rw [hs]
  ext w
  constructor
  · rintro ⟨χ, rfl⟩
    obtain ⟨z, hz, _⟩ := character_classification.2 χ.val χ.property
    exact ⟨z, (hz a).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨χ, hχ, hz⟩ := character_classification.1 z
    exact ⟨⟨χ, hχ⟩, hz a⟩

lemma fourier_delta (z : Circle) : fourier delta z = 1 := by
  simp [fourier, coefficient, delta_apply, ofAdd_eq_one]

lemma fourier_convolution (a b : L1) (z : Circle) :
    fourier (convolution a b) z = fourier a z * fourier b z := by
  simpa only [fourier_eq_group] using
    GroupAlgebraCharacters.fourier_convolution counting (integerCharacter z) a b

theorem inverse_criterion : InverseCriterion := by
  intro a
  have h0 : (∀ z : Circle, fourier a z ≠ 0) ↔ 0 ∉ unitalSpectrum a := by
    rw [spectrum_formula a]
    simp only [Set.mem_range, not_exists]
  rw [h0, unitalSpectrum_eq_native, spectrum.zero_notMem_iff]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    exact ⟨b, hb.trans one_eq_delta, (mul_comm _ _).trans (hb.trans one_eq_delta)⟩
  · rintro ⟨b, hb, _⟩
    exact isUnit_iff_exists_inv.mpr ⟨b, hb.trans one_eq_delta.symm⟩

theorem wiener_reciprocal : WienerReciprocal := by
  intro a ha hnonzero
  obtain ⟨f, hf⟩ := sequence_identification.2 a ha
  have hfa (z : Circle) : fourier f z = series a z := by
    unfold fourier series
    exact tsum_congr fun n => by rw [hf n]
  have hn (z : Circle) : fourier f z ≠ 0 := by rw [hfa]; exact hnonzero z
  obtain ⟨b, hb, _⟩ := (inverse_criterion f).mp hn
  refine ⟨coefficient b, sequence_identification.1 b, fun z => ?_⟩
  change fourier b z = (series a z)⁻¹
  have hm : fourier f z * fourier b z = 1 := by
    rw [← fourier_convolution, hb, fourier_delta]
  rw [← hfa]
  exact eq_inv_of_mul_eq_one_right hm

end ExpandedFA.BanachAlgebra.Wiener
