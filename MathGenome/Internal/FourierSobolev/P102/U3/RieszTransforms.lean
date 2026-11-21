import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RieszTransforms
import MathGenome.Internal.FourierSobolev.P102.U3.RieszL2Multiplier
import MathGenome.Internal.FourierSobolev.P102.U2.CZLp
import MathGenome.Internal.FourierSobolev.P102.U2.PrincipalValues

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal ENNReal

namespace P102.U3.RieszTransforms
open P102.Specs.U3 (Euclidean)
open P102.Specs.U3.Riesz (kernelValue IsMultiplier truncation)
open P102.U2.CZWeak P102.U2.CZLpData P102.U2.MaximalTruncationData

/-- The complex kernel passed to the general singular-integral theorems. -/
def complexKernel {d : ℕ} (j : Fin d) (z : Euclidean d) : ℂ :=
  (kernelValue d j z : ℂ)

lemma complexKernel_smooth {d : ℕ} (hd : 1 ≤ d) (j : Fin d) :
    ContDiffOn ℝ 1 (complexKernel j) ({0}ᶜ : Set (Euclidean d)) := by
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((Riesz.kernel_smooth d hd j).of_le (by simp))

/-- The coordinate-gradient convention of CZLp differs from the real
operator-norm convention upstream. A dimension factor bounds the former. -/
lemma complexKernel_gradient (d : ℕ) (hd : 1 ≤ d) :
    ∃ B : ℝ≥0, ∀ (j : Fin d) (z : Euclidean d), z ≠ 0 →
      gradientNorm (complexKernel j) z ≤ (B : ℝ) / ‖z‖ ^ (d + 1) := by
  obtain ⟨D, hD, hbound⟩ := Riesz.kernel_derivative_bound d hd
  refine ⟨⟨((d : ℝ) + 1) * D, by positivity⟩, ?_⟩
  intro j z hz
  have hdiff : DifferentiableAt ℝ (kernelValue d j) z :=
    ((Riesz.kernel_smooth d hd j).differentiableOn (by simp) z hz).differentiableAt
      (isClosed_singleton.isOpen_compl.mem_nhds hz)
  have hder := Complex.ofRealCLM.hasFDerivAt.comp z hdiff.hasFDerivAt
  have hcoord (i : Fin d) :
      ‖fderiv ℝ (complexKernel j) z (ExpandedFA.Fourier.basisVector i)‖ ≤
        D / ‖z‖ ^ (d + 1) := by
    rw [show fderiv ℝ (complexKernel j) z =
      Complex.ofRealCLM.comp (fderiv ℝ (kernelValue d j) z) from hder.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
    calc
      _ ≤ ‖fderiv ℝ (kernelValue d j) z‖ * ‖ExpandedFA.Fourier.basisVector i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ D / ‖z‖ ^ (d + 1) := by
        simpa [ExpandedFA.Fourier.basisVector] using hbound j z hz
  have hA : 0 ≤ D / ‖z‖ ^ (d + 1) := div_nonneg hD (by positivity)
  change gradientNorm (complexKernel j) z ≤ (((d : ℝ) + 1) * D) / ‖z‖ ^ (d + 1)
  unfold gradientNorm ExpandedFA.SingularIntegrals.StandardConvolution.kernelGradientNorm
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _i : Fin d, (D / ‖z‖ ^ (d + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
    _ = (d : ℝ) * (D / ‖z‖ ^ (d + 1)) ^ 2 := by simp
    _ ≤ (((d : ℝ) + 1) * (D / ‖z‖ ^ (d + 1))) ^ 2 := by
      nlinarith [sq_nonneg (d : ℝ), sq_nonneg (D / ‖z‖ ^ (d + 1))]
    _ = _ := by ring

/-- Translation followed by reflection preserves Euclidean volume. This is
exactly the change of variables z = x - y in the ordinary truncation. -/
lemma truncation_eq {d : ℕ} (j : Fin d) (ε : ℝ)
    (f : Euclidean d → ℂ) (x : Euclidean d) :
    truncation j ε f x = truncated (complexKernel j) f ε x := by
  have h := (volume : Measure (Euclidean d)).measurePreserving_sub_left x
  have he := h.setIntegral_preimage_emb
    (MeasurableEquiv.subLeft x).measurableEmbedding
    (fun z => complexKernel j z * f (x - z)) {z | ε < ‖z‖}
  simpa [truncation, truncated, complexKernel] using he.symm

lemma truncation_integrable_iff {d : ℕ} (j : Fin d) (ε : ℝ)
    (f : Euclidean d → ℂ) (x : Euclidean d) :
    IntegrableOn (fun z => (kernelValue d j z : ℂ) * f (x - z))
      {z : Euclidean d | ε < ‖z‖} volume ↔
    IntegrableOn (fun y => complexKernel j (x - y) * f y)
      {y : Euclidean d | ε < ‖x - y‖} volume := by
  have h := (volume : Measure (Euclidean d)).measurePreserving_sub_left x
  simpa [Function.comp_def, complexKernel] using
    (h.integrableOn_comp_preimage (MeasurableEquiv.subLeft x).measurableEmbedding
      (f := fun z => complexKernel j z * f (x - z)) (s := {z | ε < ‖z‖})).symm

/-- Every kernel hypothesis is verified for the exact normalized kernel. -/
lemma complexKernel_regularity (d : ℕ) (hd : 1 ≤ d) :
    ∃ B : ℝ≥0, ∀ j : Fin d, KernelRegularity (complexKernel j) B := by
  obtain ⟨B, hB⟩ := complexKernel_gradient d hd
  refine ⟨B, fun j => ⟨complexKernel_smooth hd j, ?_, ?_, hB j⟩⟩
  · intro r hr z _hz
    simpa [complexKernel, zpow_neg, zpow_natCast, RCLike.real_smul_eq_coe_mul] using
      congrArg (fun t : ℝ => (t : ℂ)) (Riesz.kernel_homogeneous d hd j r hr z)
  · change (∫ θ : Metric.sphere (0 : Euclidean d) 1,
      (kernelValue d j θ.val : ℂ) ∂(volume : Measure (Euclidean d)).toSphere) = 0
    rw [integral_complex_ofReal, (Riesz.kernel_sphere_mean d hd j).2]
    rfl

/-- Smooth-input identification uses the upstream physical principal-value
proof, with the same multiplier and the same ordinary truncations. -/
lemma smoothL2Action {d : ℕ} (hd : 1 ≤ d) (j : Fin d) (a : ℂ)
    (T : Operator d) (hT : IsMultiplier j a T) :
    SmoothL2Action T (complexKernel j) := by
  intro φ
  obtain ⟨_hi, g, hf, hg, hlim, heq⟩ :=
    Riesz.principal_value_identification d hd j a T hT φ φ.contDiff φ.hasCompactSupport
  have htest : hf.toLp (φ : Euclidean d → ℂ) =
      ExpandedFA.SingularIntegrals.StandardConvolution.testL2 φ := rfl
  have hpv (x : Euclidean d) : principalValue (complexKernel j) φ x = g x := by
    apply Tendsto.limUnder_eq
    simpa only [truncation_eq] using hlim x
  rw [← htest, ← heq]
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, hpv]

lemma canonical_multiplier {d : ℕ} (hd : 1 ≤ d) (j : Fin d) (a : ℂ) :
    IsMultiplier j a (Riesz.rieszL2 j) := by
  obtain ⟨U, _hU, hmul⟩ := Riesz.multiplier_exists d hd j a
  have hc : IsMultiplier j 0 (Riesz.rieszL2 j) := by
    intro f
    rw [Riesz.rieszL2_frequency]
    filter_upwards [Riesz.frequencyMul_ae j (P102.Specs.U3.Riesz.F2 d f),
      Riesz.symbol_origin_ae j 0] with ξ hξ ha
    rw [hξ, ha]
  have heq := Riesz.multiplier_unique d hd j a 0 U (Riesz.rieszL2 j) hmul hc
  rwa [heq] at hmul

/-- Transfer the general convergence theorem to the source's z-truncations. -/
lemma convergence {d : ℕ} (hd : 1 ≤ d) (j : Fin d) (B : ℝ≥0)
    (hK : KernelRegularity (complexKernel j) B) (T : Operator d)
    (hT : SmoothL2Action T (complexKernel j))
    (p : Exponent) (R : StrongOperator d p) (hR : Agrees T p R) :
    P102.Specs.U3.RieszTransforms.Convergence j p R := by
  intro f hf
  have hc := P102.U2.PrincipalValues.convergence d hd (complexKernel j) B T hK hT p R hR f hf
  have hi := P102.U2.MaximalTruncation.truncation_realization d hd
    (complexKernel j) B hK p f hf
  refine ⟨?_, ?_⟩
  · intro ε hε x
    exact (truncation_integrable_iff j ε f x).mpr (hi.1 ε hε x)
  · have he (ε : ℝ) : truncation j ε f = truncated (complexKernel j) f ε :=
      funext (truncation_eq j ε f)
    simpa only [he] using hc

/-- Full Hilbert/Riesz theorem, including the weak endpoint and both modes
of principal-value convergence for every finite exponent above one. -/
theorem full_theorem : P102.Specs.U3.RieszTransforms.full_theorem := by
  intro d hd j
  obtain ⟨B, hB⟩ := complexKernel_regularity d hd
  have hK := hB j
  let T : Operator d := Riesz.rieszL2 j
  have hT : SmoothL2Action T (complexKernel j) :=
    smoothL2Action hd j 0 T (canonical_multiplier hd j 0)
  obtain ⟨D, hD⟩ := P102.U2.MaximalTruncation.kernel_representation
  have hKhyp := (hD d hd (complexKernel j) B T hK hT).1
  obtain ⟨C₁, C, hC⟩ := P102.U2.CZLp.full_extension
  obtain ⟨_hcore, S, R, hcompat, hweak, _hcont, _happrox, huniq, _hsum,
    hnorm, hagree, hpair, hend⟩ := hC d hd T (complexKernel j) (D d * B) hKhyp
  refine ⟨T, S, R, C₁ d (D d * B) ‖T‖₊,
    (fun p => C d p (D d * B) ‖T‖₊),
    canonical_multiplier hd j, Riesz.rieszL2_norm_le j, hcompat, hweak, huniq,
    hnorm, hagree, hpair, hend, ?_, ?_⟩
  · intro p
    exact convergence hd j B hK T hT p (R p) (hagree p)
  · intro a U hU
    exact Riesz.multiplier_unique d hd j a 0 U T hU (canonical_multiplier hd j 0)

/-- Dimension one gives the kernel 1/(πx), the multiplier −i sgn ξ,
and all extensions and convergence assertions of the general theorem. -/
theorem hilbert_theorem : P102.Specs.U3.RieszTransforms.hilbert_theorem :=
  ⟨Riesz.one_dimensional, full_theorem 1 le_rfl 0⟩

end P102.U3.RieszTransforms
