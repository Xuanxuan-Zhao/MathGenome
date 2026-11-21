import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WienerLocalIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.WienerLocal
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination

noncomputable section
open MeasureTheory Filter
open scoped Topology FourierTransform

namespace ExpandedFA.PartIV.WienerLocalIdeal
open ExpandedFA.Fourier
open ExpandedFA.PartIV.WienerLocal (evaluation phase evaluation_apply evaluation_translate
  fourier_eq norm_translate continuous_translate)
variable {d : ℕ}

/-- Fourier evaluation separates genuine L¹ classes. -/
lemma evaluation_injective {f g : L1 d}
    (h : ∀ ξ, evaluation ξ f = evaluation ξ g) : f = g := by
  suffices hz : ∀ u : L1 d, (∀ ξ, evaluation ξ u = 0) → u = 0 by
    apply sub_eq_zero.mp
    apply hz
    intro ξ
    simp [map_sub, h ξ]
  intro u hu
  apply (Lp.eq_zero_iff_ae_eq_zero).mpr
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (L1.integrable_coeFn u).locallyIntegrable
  intro a ha hca
  let φ : Schwartz ℂ d :=
    (hca.comp_left (g := Complex.ofReal) rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp ha)
  let ψ : Schwartz ℂ d := 𝓕⁻ φ
  have hp : ∀ x, 𝓕 (ψ : Euclidean d → ℂ) x = (a x : ℂ) := by
    intro x
    rw [← SchwartzMap.fourier_coe]
    change (𝓕 (𝓕⁻ φ) : Schwartz ℂ d) x = _
    rw [FourierTransform.fourier_fourierInv_eq]
    rfl
  have hi := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure (Euclidean d))) (ν := volume)
    (L := innerₗ (Euclidean d)) Real.continuous_fourierChar continuous_inner
    ψ.integrable (L1.integrable_coeFn u)
  have hflip : (innerₗ (Euclidean d)).flip = innerₗ (Euclidean d) := by
    ext x y
    exact real_inner_comm x y
  rw [hflip] at hi
  change (∫ x, 𝓕 (ψ : Euclidean d → ℂ) x • u x) =
    ∫ x, ψ x • evaluation x u at hi
  simpa [hp, hu, Complex.real_smul] using hi

lemma convolution_integrable (f g : L1 d) :
    Integrable (fun y => f y • translate y g) := by
  have hm : AEStronglyMeasurable (fun y => f y • translate y g) :=
    (Lp.aestronglyMeasurable f).smul (continuous_translate g).aestronglyMeasurable
  apply ((L1.integrable_coeFn f).norm.mul_const ‖g‖).mono' hm
  exact .of_forall fun y => by
    change ‖f y • ExpandedFA.PartIV.WienerLocal.translate y g‖ ≤ _
    simp [norm_smul]

lemma evaluation_convolution (f g : L1 d) (ξ : Euclidean d) :
    evaluation ξ (convolution f g) = evaluation ξ f * evaluation ξ g := by
  rw [convolution, ← (evaluation ξ).integral_comp_comm (convolution_integrable f g)]
  calc
    (∫ y, evaluation ξ (f y • translate y g)) =
        ∫ y, (phase ξ y * f y) * evaluation ξ g := by
      apply integral_congr_ae
      filter_upwards [] with y
      change evaluation ξ (f y • ExpandedFA.PartIV.WienerLocal.translate y g) = _
      rw [map_smul, evaluation_translate, smul_eq_mul]
      ring
    _ = _ := by
      rw [integral_mul_const]
      simp only [evaluation_apply, fourier_eq]

@[simp] lemma convolution_comm (f g : L1 d) : convolution f g = convolution g f := by
  apply evaluation_injective
  intro ξ
  simp only [evaluation_convolution, mul_comm]

lemma convolution_assoc (f g h : L1 d) :
    convolution (convolution f g) h = convolution f (convolution g h) := by
  apply evaluation_injective
  intro ξ
  simp only [evaluation_convolution, mul_assoc]

theorem convolution_bound : Specs.ExpandedFA.PartIV.WienerLocalIdeal.ConvolutionBound := by
  intro d f g
  calc
    ‖convolution f g‖ ≤ ∫ y, ‖f y • translate y g‖ := norm_integral_le_integral_norm _
    _ = ‖f‖ * ‖g‖ := by
      change (∫ y, ‖f y • ExpandedFA.PartIV.WienerLocal.translate y g‖) = _
      simp only [norm_smul, norm_translate]
      rw [integral_mul_const, ← L1.norm_eq_integral_norm]

theorem convolution_formula : Specs.ExpandedFA.PartIV.WienerLocalIdeal.ConvolutionFormula := by
  intro d f g
  let F : Euclidean d → ℂ := MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume
  have hF : Integrable F :=
    (L1.integrable_coeFn f).integrable_convolution _ (L1.integrable_coeFn g)
  let v : L1 d := (memLp_one_iff_integrable.mpr hF).toLp F
  have hv : (v : Euclidean d → ℂ) =ᵐ[volume] F := MemLp.coeFn_toLp _
  have he : convolution f g = v := by
    apply evaluation_injective
    intro ξ
    rw [evaluation_convolution]
    simp only [evaluation_apply]
    rw [Real.fourier_congr_ae hv]
    exact (Real.fourier_mul_convolution_eq
      (L1.integrable_coeFn f) (L1.integrable_coeFn g) ξ).symm
  rw [he]
  exact hv

/-- Closed translation-invariant linear spaces are convolution ideals. -/
theorem convolution_ideal : Specs.ExpandedFA.PartIV.WienerLocalIdeal.ConvolutionIdeal := by
  intro d Y hY htrans f g hf
  let : IsClosed (Y : Set (L1 d)) := hY
  rw [convolution_comm f g]
  apply (Submodule.Quotient.mk_eq_zero Y).mp
  change Y.mkQL (∫ y, g y • translate y f) = 0
  rw [← Y.mkQL.integral_comp_comm (convolution_integrable g f)]
  have hzero : ∀ y, Y.mkQL (g y • translate y f) = 0 := by
    intro y
    exact (Submodule.Quotient.mk_eq_zero Y).mpr (Y.smul_mem (g y) (htrans y f hf))
  simp only [hzero, integral_zero]

/-- Convolution by a fixed L¹ kernel is a bounded linear operator. -/
def convolutionCLM (f : L1 d) : L1 d →L[ℂ] L1 d :=
  LinearMap.mkContinuous
    { toFun := convolution f
      map_add' := by
        intro g h
        apply evaluation_injective
        intro ξ
        simp only [evaluation_convolution, map_add]
        ring
      map_smul' := by
        intro c g
        apply evaluation_injective
        intro ξ
        simp only [evaluation_convolution, map_smul, smul_eq_mul, RingHom.id_apply]
        ring }
    ‖f‖ (convolution_bound d f)

lemma convolutionCLM_norm_le (f : L1 d) : ‖convolutionCLM f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (convolution_bound d f)

/-- The kernel part of the geometric inverse is in L¹. This uses Neumann
inversion in the Banach algebra of bounded operators, then the convolution
identity identifies its kernel and yields the inverse in the unitization. -/
lemma exists_inverse_kernel (h : L1 d) (hh : ‖h‖ < 1) :
    ∃ k : L1 d, k - convolution h k = h := by
  let T := convolutionCLM h
  have hT : ‖T‖ < 1 := lt_of_le_of_lt (convolutionCLM_norm_le h) hh
  let e : (L1 d →L[ℂ] L1 d)ˣ := Units.oneSub T hT
  let k : L1 d := (↑e⁻¹ : L1 d →L[ℂ] L1 d) h
  refine ⟨k, ?_⟩
  have he : (1 - T) ((↑e⁻¹ : L1 d →L[ℂ] L1 d) h) = h := by
    change ((↑e : L1 d →L[ℂ] L1 d) * (↑e⁻¹ : L1 d →L[ℂ] L1 d)) h = h
    rw [Units.mul_inv]
    rfl
  exact he

theorem unitized_inverse : Specs.ExpandedFA.PartIV.WienerLocalIdeal.UnitizedInverse := by
  intro d h hh
  obtain ⟨k, hk⟩ := exists_inverse_kernel h hh
  refine ⟨k, ?_, ?_⟩
  · apply Prod.ext
    · simp [unitizedMul]
    · simp only [unitizedMul, one_smul]
      change k + -h + convolution (-h) k = 0
      apply evaluation_injective
      intro ξ
      have he := congrArg (evaluation ξ) hk
      simp only [map_sub, evaluation_convolution] at he
      simp only [map_add, map_neg, map_zero, evaluation_convolution]
      linear_combination he
  · apply Prod.ext
    · simp [unitizedMul]
    · simp only [unitizedMul, one_smul]
      change -h + k + convolution k (-h) = 0
      apply evaluation_injective
      intro ξ
      have he := congrArg (evaluation ξ) hk
      simp only [map_sub, evaluation_convolution] at he
      simp only [map_add, map_neg, map_zero, evaluation_convolution]
      linear_combination he

/-- The inverse `δ+k` acts on L¹ by `v ↦ v+k*v`. -/
lemma unitized_inverse_action {h k : L1 d}
    (hk : unitizedMul (1, -h) (1, k) = (1, 0)) (v : L1 d) :
    (v - convolution h v) + convolution k (v - convolution h v) = v := by
  apply evaluation_injective
  intro ξ
  have he := congrArg (fun p : ℂ × L1 d => evaluation ξ p.2) hk
  simp only [unitizedMul, one_smul, map_add, map_neg, map_zero,
    evaluation_convolution] at he
  simp only [map_add, map_sub, evaluation_convolution]
  linear_combination (evaluation ξ v) * he

/-- The local inversion stage of Wiener's theorem,
`paper.tex`, proof of `fa2:p4:wiener-tauberian`. -/
theorem local_ideal : Specs.ExpandedFA.PartIV.WienerLocalIdeal.LocalIdeal := by
  intro d Y hY htrans f hf ξ₀ hnonzero
  have hnonzero' : evaluation ξ₀ f ≠ 0 := by
    simpa only [evaluation_apply, integralFourier_eq_native] using hnonzero
  let f₁ : L1 d := (evaluation ξ₀ f)⁻¹ • f
  have hf₁ : f₁ ∈ Y := Y.smul_mem _ hf
  have hnormal : integralFourier (f₁ : Euclidean d → ℂ) ξ₀ = 1 := by
    rw [integralFourier_eq_native]
    change evaluation ξ₀
      ((evaluation ξ₀ f)⁻¹ • f) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hnonzero']
  obtain ⟨h, hh, hsmall, hflat⟩ := ExpandedFA.PartIV.WienerLocal.local_flattening
    d (f₁ : Euclidean d → ℂ) (L1.integrable_coeFn f₁) ξ₀ 1 zero_lt_one
  let H : L1 d := (memLp_one_iff_integrable.mpr hh).toLp h
  have hHcoe : (H : Euclidean d → ℂ) =ᵐ[volume] h := MemLp.coeFn_toLp _
  have hHnorm : ‖H‖ < 1 := by
    rw [L1.norm_eq_integral_norm]
    convert hsmall using 1
    exact integral_congr_ae (hHcoe.fun_comp norm)
  have hHfourier : ∀ ξ, evaluation ξ H = integralFourier h ξ := by
    intro ξ
    rw [evaluation_apply, Real.fourier_congr_ae hHcoe,
      integralFourier_eq_native]
  have hlocal : ∀ᶠ ξ in 𝓝 ξ₀, evaluation ξ H =
      1 - evaluation ξ f₁ := by
    filter_upwards [hflat] with ξ hξ
    rw [hHfourier, hξ, hnormal, integralFourier_eq_native,
      evaluation_apply]
  obtain ⟨U, hU, hopen, hξ₀⟩ := mem_nhds_iff.mp hlocal
  obtain ⟨k, hkinv, _⟩ := unitized_inverse d H hHnorm
  refine ⟨U, hopen, hξ₀, ?_⟩
  intro ψ hsupp
  let v : L1 d := ψ.toLp 1 volume
  have hv : ∀ ξ, evaluation ξ v = schwartzFourier ψ ξ := by
    intro ξ
    rw [evaluation_apply, Real.fourier_congr_ae (ψ.coeFn_toLp 1),
      ← SchwartzMap.fourier_coe]
    rfl
  have hidentity : v - convolution H v = convolution f₁ v := by
    apply evaluation_injective
    intro ξ
    simp only [map_sub, evaluation_convolution]
    by_cases hξ : ξ ∈ U
    · rw [hU hξ]
      ring
    · have hz : evaluation ξ v = 0 := by
        rw [hv]
        apply image_eq_zero_of_notMem_tsupport
        exact fun hm => hξ (hsupp hm)
      simp only [hz, mul_zero, sub_zero]
  have hzY : convolution f₁ v ∈ Y := convolution_ideal d Y hY htrans f₁ v hf₁
  have hkzY : convolution k (convolution f₁ v) ∈ Y := by
    rw [convolution_comm k]
    exact convolution_ideal d Y hY htrans _ k hzY
  have hinv := unitized_inverse_action hkinv v
  rw [hidentity] at hinv
  change v ∈ Y
  rw [← hinv]
  exact Y.add_mem hzY hkzY

end ExpandedFA.PartIV.WienerLocalIdeal
