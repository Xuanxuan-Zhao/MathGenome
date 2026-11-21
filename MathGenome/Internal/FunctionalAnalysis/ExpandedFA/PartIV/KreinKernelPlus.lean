import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinKernelPlus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinSpectralKernel
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal InnerProductSpace Topology Convolution

namespace ExpandedFA.PartIV.KreinKernelPlus
open KreinSpectralKernel

/-- The kernel representation applies to every continuous compactly supported
scalar test, including tests without a prescribed parity. -/
theorem compact_test_transform
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S}
    (K : KernelData G M) (A : AmplitudeData K)
    (f : ℝ → ℂ) (hfcont : Continuous f) (hfc : HasCompactSupport f) :
    (M.U (∫ t, f t • G.vectors t) : ℝ → FiberSpace) =ᵐ[M.μ]
      fun ξ => (∫ t, f t * (solution p ξ t : ℂ)) • A.c ξ := by
  obtain ⟨R, hR, hb⟩ := hfc.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hs : tsupport f ⊆ Icc (-R) R := by
    simpa only [Real.closedBall_eq_Icc, zero_sub, zero_add] using hb
  have hfzero : ∀ t, t ∉ Icc (-R) R → f t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (fun h => ht (hs h))
  have hf : MemLp f 2 (intervalMeasure R) := hfcont.memLp_of_hasCompactSupport hfc
  let ff : Lp ℂ 2 (intervalMeasure R) := hf.toLp f
  have hinput : (∫ t, ff t • G.vectors t ∂intervalMeasure R) =
      ∫ t, f t • G.vectors t := by
    calc
      (∫ t, ff t • G.vectors t ∂intervalMeasure R) =
          ∫ t, f t • G.vectors t ∂intervalMeasure R :=
        integral_congr_ae (hf.coeFn_toLp.mono fun t ht =>
          congrArg (fun z : ℂ => z • G.vectors t) ht)
      _ = ∫ t, f t • G.vectors t :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hfzero t ht, zero_smul])
  have hrep := K.represents R hR ff
  rw [hinput] at hrep
  filter_upwards [hrep, A.factorization] with ξ hrep hfact
  calc
    M.U (∫ t, f t • G.vectors t) ξ =
        ∫ t, ff t • K.h ξ t ∂intervalMeasure R := hrep
    _ = ∫ t, (f t * (solution p ξ t : ℂ)) • A.c ξ ∂intervalMeasure R := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, ae_restrict_of_ae hfact] with t hft ht
      rw [hft, ht, smul_smul]
    _ = (∫ t, f t * (solution p ξ t : ℂ) ∂intervalMeasure R) • A.c ξ :=
      integral_smul_const _ _
    _ = (∫ t, f t * (solution p ξ t : ℂ)) • A.c ξ := by
      congr 1
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => by rw [hfzero t ht, zero_mul])

/-- A concrete smooth approximate identity; the radii tend to zero. -/
def shrinkingBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (2 * ((n : ℝ) + 1))⁻¹
  rOut := ((n : ℝ) + 1)⁻¹
  rIn_pos := inv_pos.mpr (by positivity)
  rIn_lt_rOut := by
    apply inv_lt_inv₀ (by positivity) (by positivity) |>.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem shrinkingBump_radius :
    Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa [shrinkingBump, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Approximate point masses recover actual spectral representatives of each
continuous Gram vector. Subsequence convergence in L² justifies the passage
from an integral kernel to point evaluation; no finiteness of ν is assumed. -/
theorem pointwise_transform
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S}
    (K : KernelData G M) (A : AmplitudeData K) (s : ℝ) :
    (M.U (G.vectors s) : ℝ → FiberSpace) =ᵐ[M.μ]
      fun ξ => (solution p ξ s : ℂ) • A.c ξ := by
  let b (n : ℕ) : ℝ → ℝ := (shrinkingBump n).normed volume
  let v (n : ℕ) : H := (b n ⋆[lsmul ℝ ℝ, volume] G.vectors) s
  let a (n : ℕ) (ξ : ℝ) : ℝ :=
    (b n ⋆[lsmul ℝ ℝ, volume] (solution p ξ)) s
  have hv : Tendsto v atTop (𝓝 (G.vectors s)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      shrinkingBump_radius G.continuous_vectors s
  have ha (ξ : ℝ) : Tendsto (fun n => a n ξ) atTop (𝓝 (solution p ξ s)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      shrinkingBump_radius
      ((KreinFiberAmplitudes.continuous_solution p).comp
        (continuous_const.prodMk continuous_id)) s
  have hrep (n : ℕ) : (M.U (v n) : ℝ → FiberSpace) =ᵐ[M.μ]
      fun ξ => (a n ξ : ℂ) • A.c ξ := by
    let f : ℝ → ℂ := fun t => (b n (s - t) : ℂ)
    have hf : Continuous f := Complex.continuous_ofReal.comp
      ((shrinkingBump n).continuous_normed.comp (continuous_const.sub continuous_id))
    have hfc : HasCompactSupport f := by
      have h := (shrinkingBump n).hasCompactSupport_normed (μ := volume)
      have h' := h.comp_homeomorph ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft s))
      exact (show HasCompactSupport (fun t => b n (s - t)) by
        simpa [Function.comp_def, b, sub_eq_add_neg] using h').comp_left (g := Complex.ofReal) (by simp)
    have hi : (∫ t, f t • G.vectors t) = v n := by
      rw [show v n = (b n ⋆[lsmul ℝ ℝ, volume] G.vectors) s from rfl,
        convolution_lsmul_swap]
      simp only [f, Complex.coe_smul]
    have hj (ξ : ℝ) : (∫ t, f t * (solution p ξ t : ℂ)) = (a n ξ : ℂ) := by
      rw [show a n ξ = (b n ⋆[lsmul ℝ ℝ, volume] (solution p ξ)) s from rfl,
        convolution_lsmul_swap]
      simp only [f, smul_eq_mul, ← Complex.ofReal_mul]
      exact integral_ofReal
    simpa only [hi, hj] using compact_test_transform K A f hf hfc
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (M.U.continuous.tendsto _ |>.comp hv)).exists_seq_tendsto_ae
  have hall : ∀ᵐ ξ ∂M.μ, ∀ n, M.U (v n) ξ = (a n ξ : ℂ) • A.c ξ :=
    ae_all_iff.mpr hrep
  filter_upwards [hlim, hall] with ξ hξ heq
  apply tendsto_nhds_unique hξ
  have h := ((Complex.continuous_ofReal.tendsto _).comp (ha ξ)).smul_const (A.c ξ)
  exact (h.comp hns.tendsto_atTop).congr (fun n => (heq (ns n)).symm)

/-- Finite mass and the representation follow from the two actual Gram
vectors, after pointwise spectral recovery. In particular the zero-space
case requires no division by a positive norm or spectral mass. -/
theorem kernel_plus : Spec.Main := by
  intro F hF he hpos
  have hp : KreinSolutions.Specs.PositiveDefiniteValue
      (KreinSymmetricOperator.Spec.kernel true F) := by
    simpa [KreinSymmetricOperator.Spec.kernel] using hpos
  obtain ⟨H, hnorm, hinner, hcomplete, hsep, G, S₀, S,
    hdom, haction, hsym, hreal, hclose, hext, hself, M, K, ⟨A⟩⟩ :=
    KreinSpectralKernel.spectral_kernel true F hF he hp
  let := hnorm
  let := hinner
  let := hcomplete
  let := hsep
  let ν : Measure ℝ := amplitudeMeasure M.μ A.c
  have hzero (ξ : ℝ) : KreinSolutions.Specs.CValue ξ 0 = 1 := by
    simp [KreinSolutions.Specs.CValue]
  have hpair (s : ℝ) := KreinFiberAmplitudes.weighted_gram_pairing M.μ M.U A.c
    A.measurable (G.vectors 0) (G.vectors s)
    (fun ξ => (solution true ξ 0 : ℂ)) (fun ξ => (solution true ξ s : ℂ))
    (pointwise_transform K A 0) (pointwise_transform K A s)
  have hint (s : ℝ) : Integrable (fun ξ => (KreinSolutions.Specs.CValue ξ s : ℂ)) ν := by
    simpa [solution, hzero] using (hpair s).1
  have hgram (s : ℝ) : ⟪G.vectors 0, G.vectors s⟫_ℂ = (F s : ℂ) := by
    rw [G.gram]
    simp [KreinSymmetricOperator.Spec.kernel, KreinSolutions.Specs.KernelPlusValue, he s]
  have hrepr (s : ℝ) : F s = ∫ ξ, KreinSolutions.Specs.CValue ξ s ∂ν := by
    have hc : (F s : ℂ) = ∫ ξ, (KreinSolutions.Specs.CValue ξ s : ℂ) ∂ν := by
      simpa [hgram, solution, hzero] using (hpair s).2
    exact Complex.ofReal_injective (hc.trans integral_ofReal)
  have hfinite : IsFiniteMeasure ν :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℂ) ≠ 0)).mp
      (by simpa only [hzero, Complex.ofReal_one] using hint 0)
  have hrint (s : ℝ) : Integrable (fun ξ => KreinSolutions.Specs.CValue ξ s) ν := by
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using (hint s).re
  refine ⟨ν, hfinite, ?_, fun s => ⟨hrint s, hrepr s⟩, ?_⟩
  · simpa only [hzero, integral_const, smul_eq_mul, mul_one] using (hrepr 0).symm
  · intro R hR
    apply (hrint R).restrict.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have hξpos : 0 < ξ := hξ
    simp [KreinSolutions.Specs.CValue, not_lt_of_gt hξpos, ne_of_gt hξpos, mul_comm]

end ExpandedFA.PartIV.KreinKernelPlus
