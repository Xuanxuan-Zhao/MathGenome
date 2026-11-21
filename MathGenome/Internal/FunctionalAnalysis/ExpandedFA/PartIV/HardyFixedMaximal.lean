import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyFixedMaximal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyPeetre
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyGrandAtomic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyGrandForward
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyRadialTransfer
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarL1DunfordPettis
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Topology BoundedContinuousFunction LineDeriv

namespace SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma translation_seminorm_bound (f : 𝓢(E,F)) (k n : ℕ) (a : E) (ha : ‖a‖ ≤ 1) :
    SchwartzMap.seminorm ℝ k n (compSubConstCLM ℝ a f - f) ≤
      (2 ^ k * (Finset.Iic (k,n+1)).sup (schwartzSeminormFamily ℝ E F) f) * ‖a‖ := by
  let C := 2 ^ k * (Finset.Iic (k,n+1)).sup (schwartzSeminormFamily ℝ E F) f
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine seminorm_le_bound ℝ k n _ (mul_nonneg hC (norm_nonneg _)) ?_
  intro x
  have hdiff : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) :=
    (f.smooth ⊤).iteratedFDeriv_right (by simp)
  let g := fun y : E => ‖x‖ ^ k • iteratedFDeriv ℝ n f y
  have hg : Differentiable ℝ g := by
    dsimp [g]
    exact (hdiff.differentiable (by simp)).const_smul (‖x‖ ^ k)
  have hbound : ∀ y ∈ Metric.closedBall x 1, ‖fderiv ℝ g y‖ ≤ C := by
    intro y hy
    have hxy : ‖x‖ ≤ 1 + ‖y‖ := by
      calc
        ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add _ _
        _ ≤ 1 + ‖y‖ := add_le_add_left (by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy) _
    calc
      ‖fderiv ℝ g y‖ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n+1) f y‖ := by
        change ‖fderiv ℝ ((‖x‖ ^ k) • iteratedFDeriv ℝ n f) y‖ ≤ _
        rw [fderiv_const_smul (hdiff.differentiable (by simp) y)]
        simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _), norm_fderiv_iteratedFDeriv] using
          (ContinuousLinearMap.opNorm_smul_le (‖x‖ ^ k) (fderiv ℝ (iteratedFDeriv ℝ n f) y))
      _ ≤ (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n+1) f y‖ := by gcongr
      _ ≤ C := by
        change _ ≤ 2 ^ k * ((Finset.Iic (k,n+1)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f
        exact (one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k,n+1)) le_rfl le_rfl f y)
  have hm := (convex_closedBall x (1:ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hg y) hbound (Metric.mem_closedBall_self (by norm_num))
    (show x-a ∈ Metric.closedBall x 1 by simpa [Metric.mem_closedBall, dist_eq_norm] using ha)
  have hsub : iteratedFDeriv ℝ n (⇑(compSubConstCLM ℝ a f - f)) x =
      iteratedFDeriv ℝ n f (x-a) - iteratedFDeriv ℝ n f x := by
    change iteratedFDeriv ℝ n ((fun z => f (z-a)) - (f : E → F)) x = _
    have hs : ContDiff ℝ n (fun z => f (z-a)) := (f.smooth n).comp (contDiff_id.sub contDiff_const)
    rw [iteratedFDeriv_sub hs (f.smooth n)]
    change iteratedFDeriv ℝ n (fun z => f (z-a)) x - iteratedFDeriv ℝ n f x = _
    rw [iteratedFDeriv_comp_sub]
  rw [hsub]
  simpa [g, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg x) k)] using hm

lemma continuous_compSubConst (f : 𝓢(E,F)) : Continuous (fun a : E => compSubConstCLM ℝ a f) := by
  have hzero : Tendsto (fun a : E => compSubConstCLM ℝ a f) (𝓝 0) (𝓝 f) := by
    apply ((schwartz_withSeminorms ℝ E F).tendsto_nhds _ _).mpr
    rintro ⟨k,n⟩ ε hε
    let C := 2 ^ k * (Finset.Iic (k,n+1)).sup (schwartzSeminormFamily ℝ E F) f
    have hlim : Tendsto (fun a : E => C * ‖a‖) (𝓝 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_norm_zero (E := E))
    filter_upwards [(tendsto_norm_zero (E := E)).eventually_lt_const (by norm_num : (0:ℝ)<1),
      hlim.eventually_lt_const hε] with a ha hεa
    exact lt_of_le_of_lt (translation_seminorm_bound f k n a ha.le) hεa
  apply continuous_iff_continuousAt.mpr
  intro a
  have hsub : Tendsto (fun b : E => b-a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun b : E => b-a) := by fun_prop
    simpa using hc.tendsto a
  have hh := ((compSubConstCLM ℝ a).continuous.tendsto f).comp (hzero.comp hsub)
  change Tendsto _ _ _
  simpa only [Function.comp_def, compSubConstCLM_comp, sub_add_cancel] using hh

lemma translation_seminorm_growth (f : 𝓢(E,F)) (k n : ℕ) (a : E) :
    SchwartzMap.seminorm ℝ k n (compSubConstCLM ℝ a f) ≤
      (2 ^ k * (Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ E F) f) * (1+‖a‖)^k := by
  have hC : 0 ≤ 2 ^ k * (Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ E F) f := by positivity
  refine seminorm_le_bound ℝ k n _ (mul_nonneg hC (by positivity)) ?_
  intro x
  have hxa : ‖x‖ ≤ (1+‖a‖) * (1+‖x-a‖) := by
    have ht := norm_le_norm_sub_add x a
    nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg (x-a))]
  change ‖x‖^k * ‖iteratedFDeriv ℝ n (fun z => f (z-a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  calc
    ‖x‖^k * ‖iteratedFDeriv ℝ n f (x-a)‖ ≤
        ((1+‖a‖)*(1+‖x-a‖))^k * ‖iteratedFDeriv ℝ n f (x-a)‖ := by gcongr
    _ = ((1+‖x-a‖)^k * ‖iteratedFDeriv ℝ n f (x-a)‖) * (1+‖a‖)^k := by rw [mul_pow]; ring
    _ ≤ (2 ^ k * (Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ E F) f) * (1+‖a‖)^k := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      change _ ≤ 2 ^ k * ((Finset.Iic (k,n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f
      exact one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k,n)) le_rfl le_rfl f (x-a)

end SchwartzMap

lemma SchwartzMap.continuous_compSubConst_rclike {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    (f : SchwartzMap E F) : Continuous (fun a : E => SchwartzMap.compSubConstCLM 𝕜 a f) := by
  have heq (a:E) : SchwartzMap.compSubConstCLM 𝕜 a f = SchwartzMap.compSubConstCLM ℝ a f := by ext; rfl
  simp only [heq]
  exact SchwartzMap.continuous_compSubConst f


namespace ExpandedFA.PartIV.HardyFixedMaximal
open ExpandedFA.Fourier HardyMaximalSpec HardyFixedMaximalSpec LineDeriv
open ExpandedFA.Hardy.AtomicHardySpaceSpec
open ExpandedFA.FunctionSpaces WeakL1UniformIntegrabilitySpec ScalarL1DunfordPettisSpec
open private l1_compact_subsequence from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarL1DunfordPettis

lemma radial_congr_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) {f g : Euclidean d → 𝕜} (hfg : f =ᵐ[volume] g) :
    radial Φ f = radial Φ g := by
  unfold radial
  funext x
  congr 1
  funext t
  congr 2
  exact congrFun (convolution_congr (ContinuousLinearMap.mul 𝕜 𝕜)
    (EventuallyEq.rfl) hfg) x

theorem forward : Forward := by
  intro 𝕜 _ d hd Φ hΦ
  obtain ⟨N, hN⟩ := (HardyMaximal.parameters d).2.2.2.2
  obtain ⟨A, hA, hAG⟩ := HardyRadialTransfer.radial_grand hd N hN Φ hΦ
  obtain ⟨B, hB⟩ := HardyGrandForward.forward d N hd hN
  refine ⟨A * (B + 1), by positivity, ?_⟩
  intro h
  calc
    (∫⁻ x, radial Φ (EmbeddingValue volume h : Euclidean d → 𝕜) x) ≤
        ∫⁻ x, ENNReal.ofReal A * grand N (EmbeddingValue volume h : Euclidean d → 𝕜) x :=
      lintegral_mono (hAG _ (MeasureTheory.L1.integrable_coeFn _) )
    _ = ENNReal.ofReal A * ∫⁻ x, grand N (EmbeddingValue volume h : Euclidean d → 𝕜) x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * ((B : ℝ≥0∞) * ENNReal.ofReal ‖h‖) :=
      by gcongr; exact hB h
    _ ≤ ENNReal.ofReal (A * (B + 1)) * ENNReal.ofReal ‖h‖ := by
      rw [ENNReal.ofReal_mul hA.le, ← mul_assoc]
      gcongr
      simpa only [ENNReal.ofReal_coe_nnreal] using
        (ENNReal.ofReal_le_ofReal (show (B : ℝ) ≤ (B : ℝ) + 1 by linarith))

theorem converse : Converse := by
  intro 𝕜 _ d hd Φ hΦ
  obtain ⟨N, hN⟩ := (HardyMaximal.parameters d).2.2.2.2
  obtain ⟨A, hA, hAG⟩ := HardyPeetre.grand_L1_bound hd N hN Φ hΦ
  obtain ⟨B, hB, hBH⟩ := HardyGrandAtomic.grand_atomic 𝕜 d N hd hN
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro f hf hF
  have hG := hAG f hf hF
  have hGfin : (∫⁻ x, grand N f x) < ⊤ :=
    hG.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF)
  obtain ⟨h, he, hn, _⟩ := hBH f hf hGfin
  refine ⟨h, he, ?_⟩
  calc
    ‖h‖ ≤ B * (∫⁻ x, grand N f x).toReal := hn
    _ ≤ B * (A * (∫⁻ x, radial Φ f x).toReal) := by
      apply mul_le_mul_of_nonneg_left _ hB.le
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le] using
        ENNReal.toReal_mono (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF)) hG
    _ = _ := by ring

theorem characterization : Characterization := by
  intro 𝕜 _ d hd Φ hΦ
  obtain ⟨A, hA, hAf⟩ := forward hd Φ hΦ
  obtain ⟨B, hB, hBf⟩ := converse hd Φ hΦ
  let C := max A B
  have hC : 0 < C := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro f hf
  have forward' (h : Hardy 𝕜 d) (he : EmbeddingValue volume h = hf.toL1 f) :
      (∫⁻ x, radial Φ f x) ≤ ENNReal.ofReal A * ENNReal.ofReal ‖h‖ := by
    have hae : (EmbeddingValue volume h : Euclidean d → 𝕜) =ᵐ[volume] f := by
      rw [he]
      exact hf.coeFn_toL1
    rw [← radial_congr_ae Φ hae]
    exact hAf h
  have hfinite (h : Hardy 𝕜 d) (he : EmbeddingValue volume h = hf.toL1 f) :
      (∫⁻ x, radial Φ f x) < ⊤ :=
    (forward' h he).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h, he⟩
    exact hfinite h he
  · intro hF
    obtain ⟨h, he, _⟩ := hBf f hf hF
    exact ⟨h, he⟩
  · intro h he
    have hF := hfinite h he
    obtain ⟨h', he', hn⟩ := hBf f hf hF
    have hh : h' = h := (ExpandedFA.Hardy.AtomicHardySpace.embedding_properties volume).1
      (he'.trans he.symm)
    rw [hh] at hn
    constructor
    · have hn' : ‖h‖ ≤ C * (∫⁻ x, radial Φ f x).toReal :=
        hn.trans (mul_le_mul_of_nonneg_right (le_max_right A B) ENNReal.toReal_nonneg)
      calc
        C⁻¹ * ‖h‖ ≤ C⁻¹ * (C * (∫⁻ x, radial Φ f x).toReal) :=
          mul_le_mul_of_nonneg_left hn' (inv_nonneg.mpr hC.le)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
    · calc
        (∫⁻ x, radial Φ f x).toReal ≤ A * ‖h‖ := by
          simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le,
            ENNReal.toReal_ofReal (norm_nonneg h)] using
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
              (forward' h he)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left A B) (norm_nonneg h)

theorem schwartz_kernels : SchwartzKernels := by
  intro 𝕜 _ d Φ hI
  refine ⟨Φ.smooth _, hI, ?_⟩
  intro k a
  let C : ℝ := 2 ^ (d + 1 + k) *
    (Finset.Iic (d + 1 + k, k)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x
  have hpartial : ‖coordinatePartial a (Φ : Euclidean d → 𝕜) x‖ ≤
      ‖iteratedFDeriv ℝ k Φ x‖ := by
    have h := (iteratedFDeriv ℝ k Φ x).le_opNorm (fun i => basisVector (a i))
    simpa [coordinatePartial, basisVector] using h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖x‖) ^ (d + 1 + k))).mpr
  calc
    _ ≤ ‖iteratedFDeriv ℝ k Φ x‖ * (1 + ‖x‖) ^ (d + 1 + k) :=
      mul_le_mul_of_nonneg_right hpartial (by positivity)
    _ ≤ C := by
      simpa only [C, mul_comm] using
        (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
          (m := (d + 1 + k, k)) le_rfl le_rfl Φ x)

/-- Nonzero-integral Schwartz kernels inherit the full quantitative theorem. -/
theorem schwartz_characterization : SchwartzCharacterization := by
  intro 𝕜 _ d hd Φ hI
  exact characterization hd Φ (schwartz_kernels Φ hI)

lemma iteratedFDeriv_id_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (x : E) : ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ 1 + ‖x‖ := by
  cases n with
  | zero => simp
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    rw [show fderiv ℝ (id : E → E) = (fun _ => ContinuousLinearMap.id ℝ E) from funext (fun _ => fderiv_id)]
    cases n with
    | zero =>
      simp only [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity

lemma neg_norm_sq_deriv_bound {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y : Euclidean d => -‖y‖ ^ 2) x‖ ≤
      (2 * (1 + ‖x‖) ^ 2) ^ n := by
  have hsq : (fun y : Euclidean d => ‖y‖ ^ 2) =
      (fun y => innerSL ℝ (id y) (id y)) := by funext y; simp
  change ‖iteratedFDeriv ℝ n (-(fun y : Euclidean d => ‖y‖ ^ 2)) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg, hsq]
  have hb := (innerSL ℝ (E := Euclidean d)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (N := (⊤ : ℕ∞ω)) contDiff_id contDiff_id x (by simp : (n : ℕ∞ω) ≤ ⊤)
    (norm_innerSL_le (𝕜 := ℝ))
  refine hb.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (1 + ‖x‖) * (1 + ‖x‖) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr <;> exact iteratedFDeriv_id_bound _ x
    _ = (2 : ℝ) ^ n * (1 + ‖x‖) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ ≤ (2 : ℝ) ^ n * ((1 + ‖x‖) ^ 2) ^ n := by
      gcongr
      exact le_self_pow₀ (by nlinarith [norm_nonneg x] : 1 ≤ (1 + ‖x‖) ^ 2) (by omega)
    _ = _ := (mul_pow _ _ _).symm

lemma gaussian_deriv_bound {d : ℕ} (n : ℕ) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y : Euclidean d => Real.exp (-‖y‖ ^ 2)) x‖ ≤
      n.factorial * Real.exp (-‖x‖ ^ 2) * (2 * (1 + ‖x‖) ^ 2) ^ n := by
  apply norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (N := ⊤) Real.contDiff_exp
    (contDiff_norm_sq ℝ).neg (by simp) x
  · intro i hi
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact le_rfl
  · intro i hi hin
    exact neg_norm_sq_deriv_bound i hi x

lemma polynomial_gaussian_bound (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1+r)^m * Real.exp (-r^2) ≤ 2^m * (m.factorial : ℝ) := by
  by_cases h : r ≤ 1
  · calc
      _ ≤ (2 : ℝ)^m * 1 := by
        gcongr
        · linarith
        · exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ ≤ _ := by gcongr; exact_mod_cast Nat.factorial_pos m
  · have hr1 : 1 ≤ r := le_of_lt (lt_of_not_ge h)
    have hseries := Real.pow_div_factorial_le_exp (r^2) (sq_nonneg r) m
    have hfact : (0 : ℝ) < m.factorial := by positivity
    have hp : r ^ (2*m) * Real.exp (-r^2) ≤ (m.factorial : ℝ) := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      have hh := (div_le_iff₀ hfact).mp hseries
      simpa only [pow_mul, mul_comm (Real.exp _) (m.factorial : ℝ)] using hh
    calc
      _ ≤ (2*r)^m * Real.exp (-r^2) := by gcongr; linarith
      _ = 2^m * (r^m * Real.exp (-r^2)) := by rw [mul_pow]; ring
      _ ≤ 2^m * (r^(2*m) * Real.exp (-r^2)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact pow_le_pow_right₀ hr1 (show m ≤ 2*m by omega)
      _ ≤ _ := by gcongr

lemma gaussian_schwartz_exists (d : ℕ) :
    ∃ G : Schwartz ℝ d, ∀ x, G x = Real.exp (-‖x‖ ^ 2) := by
  refine ⟨⟨(fun x => Real.exp (-‖x‖ ^ 2)), Real.contDiff_exp.comp (contDiff_norm_sq ℝ).neg, ?_⟩, fun _ => rfl⟩
  intro k n
  refine ⟨(n.factorial : ℝ) * 2^n * (2^(k+2*n) * ((k+2*n).factorial : ℝ)), ?_⟩
  intro x
  calc
    _ ≤ ‖x‖ ^ k * (n.factorial * Real.exp (-‖x‖ ^ 2) * (2 * (1 + ‖x‖) ^ 2) ^ n) := by
      gcongr; exact gaussian_deriv_bound n x
    _ ≤ (n.factorial : ℝ) * 2^n * ((1 + ‖x‖)^(k+2*n) * Real.exp (-‖x‖ ^ 2)) := by
      calc
        _ ≤ (1 + ‖x‖) ^ k * (n.factorial * Real.exp (-‖x‖ ^ 2) *
              (2 * (1 + ‖x‖) ^ 2) ^ n) := by
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg x) (show ‖x‖ ≤ 1 + ‖x‖ by linarith) k
        _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_gaussian_bound _ (norm_nonneg x)) (by positivity)

lemma exists_scaled_gaussian_schwartz {𝕜 : Type} [RCLike 𝕜] (d : ℕ)
    (b : ℝ) (hb : 0 < b) :
    ∃ G : Schwartz 𝕜 d, ∀ x, G x =
      ExpandedFA.PartIV.HardyFixedMaximalSpec.gaussian b x := by
  obtain ⟨G, hG⟩ := gaussian_schwartz_exists d
  let e : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (Real.sqrt b) (Real.sqrt_pos.mpr hb).ne')
  let H : Schwartz ℝ d := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e G
  refine ⟨SchwartzMap.postcompCLM (RCLike.ofRealCLM (K := 𝕜)) H, ?_⟩
  intro x
  change (H x : 𝕜) = _
  have he : H x = Real.exp (-b * ‖x‖ ^ 2) := by
    simp only [H, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hG,
      e, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0,
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hb), mul_pow,
      Real.sq_sqrt hb.le, neg_mul]
  rw [he]
  rfl

lemma gaussian_integral {𝕜 : Type} [RCLike 𝕜] (d : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫ x : Euclidean d, ExpandedFA.PartIV.HardyFixedMaximalSpec.gaussian (𝕜 := 𝕜) b x) =
      (((Real.pi / b) ^ ((d : ℝ) / 2) : ℝ) : 𝕜) := by
  change (∫ x : Euclidean d, (RCLike.ofRealCLM (K := 𝕜)) (Real.exp (-b * ‖x‖ ^ 2))) = _
  rw [ContinuousLinearMap.integral_comp_comm]
  · change ((∫ x : Euclidean d, Real.exp (-b * ‖x‖ ^ 2) : ℝ) : 𝕜) = _
    congr 1
    simpa using (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Euclidean d) hb)
  · obtain ⟨G, hG⟩ := exists_scaled_gaussian_schwartz (𝕜 := ℝ) d b hb
    exact G.integrable.congr (Filter.Eventually.of_forall hG)



theorem gaussian_kernels : GaussianKernels := by
  intro 𝕜 _ d b hb
  obtain ⟨G, hG⟩ := exists_scaled_gaussian_schwartz (𝕜 := 𝕜) d b hb
  have hI : (∫ x, G x) ≠ 0 := by
    simp_rw [hG]
    rw [gaussian_integral d b hb]
    exact_mod_cast (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) ((d : ℝ)/2)).ne'
  have h := schwartz_kernels G hI
  have he : (G : Euclidean d → 𝕜) = gaussian b := funext hG
  rwa [he] at h

theorem gaussian_characterization : GaussianCharacterization := by
  intro 𝕜 _ d hd b hb
  exact characterization hd _ (gaussian_kernels b hb)

lemma heat_schwartz {𝕜 : Type} [RCLike 𝕜] (d : ℕ) :
    ∃ G : Schwartz 𝕜 d, ∀ x, G x = heatKernel 𝕜 d x := by
  obtain ⟨G, hG⟩ := exists_scaled_gaussian_schwartz (𝕜 := 𝕜) d (1/4) (by norm_num)
  exact ⟨((4 * Real.pi) ^ (-(d : ℝ)/2) : ℝ) • G, fun x => by simp [heatKernel, hG]⟩

lemma heat_integral {𝕜 : Type} [RCLike 𝕜] (d : ℕ) :
    (∫ x, heatKernel 𝕜 d x) = 1 := by
  simp_rw [heatKernel]
  rw [integral_smul, gaussian_integral d (1/4) (by norm_num)]
  rw [RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul]
  have hpos : 0 < 4 * Real.pi := by positivity
  have he : -(d : ℝ) / 2 = -((d : ℝ)/2) := by ring
  have he' : Real.pi / (1/4) = 4 * Real.pi := by ring
  rw [he, he', ← Real.rpow_add hpos]
  simp

theorem heat_kernel_example : HeatKernelExample := by
  intro 𝕜 _ d hd
  obtain ⟨G, hG⟩ := heat_schwartz (𝕜 := 𝕜) d
  have he : (G : Euclidean d → 𝕜) = heatKernel 𝕜 d := funext hG
  have hI : (∫ x, G x) ≠ 0 := by rw [he, heat_integral]; exact one_ne_zero
  have hK := schwartz_kernels G hI
  rw [he] at hK
  exact ⟨heat_integral d, hK, characterization hd _ hK⟩


@[simp] lemma kernelTest_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) (t : Scale) (x y : Euclidean d) :
    kernelTest Φ t x y = dilate t.val (Φ : Euclidean d → 𝕜) (x - y) := by
  simp only [kernelTest, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, SchwartzMap.compSubConstCLM_apply,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def,
    Units.val_mk0, dilate]
  congr 2
  module

lemma temperedConvolve_eq {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) {u : Tempered 𝕜 d} {f : Euclidean d → 𝕜}
    (hu : Represents u f) (t : Scale) (x : Euclidean d) :
    temperedConvolve Φ u t x = convolve (dilate t.val Φ) f x := by
  rw [temperedConvolve, hu]
  simp only [kernelTest_apply, convolve, convolution_eq_swap, ContinuousLinearMap.mul_apply']

lemma temperedRadial_eq {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) {u : Tempered 𝕜 d} {f : Euclidean d → 𝕜}
    (hu : Represents u f) : temperedRadial Φ u = radial Φ f := by
  funext x
  unfold temperedRadial radial
  congr 1
  funext t
  rw [temperedConvolve_eq Φ hu]

lemma represents_congr_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {u : Tempered 𝕜 d} {f g : Euclidean d → 𝕜} (hfg : f =ᵐ[volume] g)
    (hu : Represents u f) : Represents u g := by
  intro ψ
  rw [hu ψ]
  exact integral_congr_ae (hfg.mono (fun x hx => by simp only [hx]))

lemma represents_unique_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {u : Tempered 𝕜 d} {f g : Euclidean d → 𝕜}
    (hf : Integrable f) (hg : Integrable g) (huf : Represents u f) (hug : Represents u g) :
    f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
  intro ψ hψ hc
  let ψS : Schwartz ℝ d := hc.toSchwartzMap hψ
  let ψK : Schwartz 𝕜 d := SchwartzMap.postcompCLM (RCLike.ofRealCLM (K := 𝕜)) ψS
  have he := (huf ψK).symm.trans (hug ψK)
  change (∫ x, (ψ x : 𝕜) * f x) = ∫ x, (ψ x : 𝕜) * g x at he
  simpa only [RCLike.real_smul_eq_coe_mul] using he

lemma represents_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    Represents (0 : Tempered 𝕜 d) (0 : Euclidean d → 𝕜) := by
  intro ψ
  simp

lemma temperedRadial_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) : temperedRadial Φ (0 : Tempered 𝕜 d) = 0 := by
  funext x
  simp [temperedRadial, temperedConvolve]

/-- Distributional uniqueness identifies the L¹ class needed by the atomic theorem. -/
lemma embedding_eq_of_represents {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {u : Tempered 𝕜 d} {f : Euclidean d → 𝕜} (hf : Integrable f)
    (huf : Represents u f) (h : Hardy 𝕜 d)
    (huh : Represents u (EmbeddingValue volume h : Euclidean d → 𝕜)) :
    EmbeddingValue volume h = hf.toL1 f := by
  apply Lp.ext
  exact (represents_unique_ae (MeasureTheory.L1.integrable_coeFn _) hf huh huf).trans
    hf.coeFn_toL1.symm

/-- Once the analytic recovery assertion is established, the already proved
L¹ characterization gives the full distributional statement. -/
theorem tempered_characterization_of_recovery (hrec : TemperedRecovery) :
    TemperedCharacterization := by
  intro 𝕜 _ d hd Φ hI
  obtain ⟨C, hC, hCf⟩ := schwartz_characterization hd Φ hI
  refine ⟨C, hC, ?_⟩
  intro u
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h, huh⟩
    rw [temperedRadial_eq Φ huh]
    have hf := MeasureTheory.L1.integrable_coeFn (EmbeddingValue volume h)
    apply ((hCf _ hf).1.mp ⟨h, ?_⟩)
    apply Lp.ext
    exact hf.coeFn_toL1.symm
  · intro hF
    obtain ⟨f, hf, huf⟩ := hrec hd Φ hI u hF
    rw [temperedRadial_eq Φ huf] at hF
    obtain ⟨h, he⟩ := (hCf f hf).1.mpr hF
    refine ⟨h, represents_congr_ae ?_ huf⟩
    exact hf.coeFn_toL1.symm.trans (by rw [← he])
  · intro h huh
    have hf := MeasureTheory.L1.integrable_coeFn (EmbeddingValue volume h)
    rw [temperedRadial_eq Φ huh]
    apply (hCf _ hf).2 h
    apply Lp.ext
    exact hf.coeFn_toL1.symm


lemma poisson_profile_integrable (d : ℕ) : Integrable (poissonProfile d) := by
  exact integrable_rpow_neg_one_add_norm_sq (by simp :
    (Module.finrank ℝ (Euclidean d) : ℝ) < (d : ℝ) + 1)

lemma poisson_profile_pos {d : ℕ} (x : Euclidean d) : 0 < poissonProfile d x :=
  Real.rpow_pos_of_pos (by positivity) _

lemma poisson_constant_pos (d : ℕ) : 0 < poissonConstant d := by
  apply inv_pos.mpr
  apply (integral_pos_iff_support_of_nonneg (fun x => (poisson_profile_pos x).le)
    (poisson_profile_integrable d)).mpr
  have hs : Function.support (poissonProfile d) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (poisson_profile_pos x).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr (by infer_instance : NeZero (volume : Measure (Euclidean d))).out

lemma poisson_integral {𝕜 : Type} [RCLike 𝕜] (d : ℕ) :
    (∫ x, poissonKernel 𝕜 d x) = 1 := by
  change (∫ x : Euclidean d, (RCLike.ofRealCLM (K := 𝕜))
    (poissonConstant d * poissonProfile d x)) = 1
  rw [(RCLike.ofRealCLM (K := 𝕜)).integral_comp_comm ((poisson_profile_integrable d).const_mul _)]
  change ((∫ x : Euclidean d, poissonConstant d * poissonProfile d x : ℝ) : 𝕜) = 1
  rw [integral_const_mul, poissonConstant, inv_mul_cancel₀]
  · simp
  · exact (inv_pos.mp (poisson_constant_pos d)).ne'

lemma poisson_profile_smooth (d : ℕ) : ContDiff ℝ ∞ (poissonProfile d) := by
  apply (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
  intro x
  positivity

lemma norm_iteratedFDeriv_id_high {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (hn : 2 ≤ n) (x : E) : ‖iteratedFDeriv ℝ n (id : E → E) x‖ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + m = (m+1)+1 by omega, ← norm_iteratedFDeriv_fderiv]
  rw [show fderiv ℝ (id : E → E) = (fun _ => ContinuousLinearMap.id ℝ E) from funext (fun _ => fderiv_id)]
  simp [iteratedFDeriv_succ_const]

lemma norm_sq_deriv_high {d : ℕ} (n : ℕ) (hn : 3 ≤ n) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y : Euclidean d => ‖y‖ ^ 2) x‖ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m = (m+2)+1 by omega, ← norm_iteratedFDeriv_fderiv, fderiv_norm_sq]
  have hb := ((2 : ℝ) • innerSL ℝ (E := Euclidean d)).norm_iteratedFDeriv_comp_left
    (f := id) (N := (⊤ : ℕ∞ω)) (by fun_prop) (by simp : ((m+2 : ℕ) : ℕ∞ω) ≤ ⊤) (x := x)
  simp only [Function.comp_id, FunLike.coe_smul, two_smul] at hb ⊢
  apply le_antisymm (hb.trans _) (norm_nonneg _)
  simp [norm_iteratedFDeriv_id_high (m+2) (by omega) x]

lemma norm_sq_deriv_two {d : ℕ} (x : Euclidean d) :
    ‖iteratedFDeriv ℝ 2 (fun y : Euclidean d => ‖y‖ ^ 2) x‖ ≤ 2 := by
  rw [show 2 = 1+1 from rfl, ← norm_iteratedFDeriv_fderiv, fderiv_norm_sq]
  have hb := ((2 : ℝ) • innerSL ℝ (E := Euclidean d)).norm_iteratedFDeriv_comp_left
    (f := id) (N := (⊤ : ℕ∞ω)) (by fun_prop) (by simp : (1 : ℕ∞ω) ≤ ⊤) (x := x)
  simp only [Function.comp_id, FunLike.coe_smul, two_smul] at hb ⊢
  apply hb.trans
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), norm_iteratedFDeriv_one, fderiv_id]
  calc
    2 * ‖innerSL ℝ (E := Euclidean d)‖ * ‖ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤ 2 * 1 * 1 := by
      gcongr
      · exact norm_innerSL_le ℝ
      · exact ContinuousLinearMap.norm_id_le
    _ = 2 := by ring


lemma quadratic_deriv_bound {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y : Euclidean d => 1 + ‖y‖ ^ 2) x‖ ≤
      (2 / Real.sqrt (1 + ‖x‖ ^ 2)) ^ n * (1 + ‖x‖ ^ 2) := by
  have hq : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hR : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr hq
  have hR2 := Real.sq_sqrt hq.le
  have hrR : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
    nlinarith [norm_nonneg x]
  change ‖iteratedFDeriv ℝ n ((fun _ : Euclidean d => (1 : ℝ)) + (fun y => ‖y‖ ^ 2)) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_const.contDiffAt) ((contDiff_norm_sq ℝ).contDiffAt),
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
  · subst n
    have hder : fderiv ℝ (fun y : Euclidean d => ‖y‖ ^ 2) x = (2 : ℝ) • innerSL ℝ x := by
      simpa only [two_smul] using fderiv_norm_sq_apply x
    simp only [norm_iteratedFDeriv_one, hder, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), innerSL_apply_norm, pow_one]
    apply (mul_le_mul_of_nonneg_left hrR (by norm_num : (0 : ℝ) ≤ 2)).trans
    apply le_of_eq
    field_simp
    nlinarith
  · subst n
    apply (norm_sq_deriv_two x).trans
    have he : (2 / Real.sqrt (1 + ‖x‖ ^ 2)) ^ 2 * (1 + ‖x‖ ^ 2) = 4 := by
      rw [div_pow, hR2]
      field_simp
      norm_num
    rw [he]
    norm_num
  · rw [norm_sq_deriv_high _ h x]
    positivity

lemma normalized_quadratic_deriv_bound {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n
      (fun y : Euclidean d => (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)) x‖ ≤
      (2 / Real.sqrt (1 + ‖x‖ ^ 2)) ^ n := by
  have hq : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have he : (fun y : Euclidean d => (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)) =
      (1 + ‖x‖ ^ 2)⁻¹ • (fun y : Euclidean d => 1 + ‖y‖ ^ 2) := rfl
  have hs : ContDiff ℝ n (fun y : Euclidean d => 1 + ‖y‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℝ)
  rw [he, iteratedFDeriv_const_smul_apply hs.contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
  calc
    _ ≤ (1 + ‖x‖ ^ 2)⁻¹ *
      ((2 / Real.sqrt (1 + ‖x‖ ^ 2)) ^ n * (1 + ‖x‖ ^ 2)) := by
        gcongr; exact quadratic_deriv_bound n hn x
    _ = _ := by field_simp


lemma normalized_rpow_deriv_bound {d : ℕ} (p : ℝ) (n : ℕ) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y : Euclidean d =>
      ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)) ^ p) x‖ ≤
      n.factorial * (∑ i ∈ Finset.range (n+1), ‖(descPochhammer ℝ i).eval p‖) *
        (2 / Real.sqrt (1 + ‖x‖ ^ 2)) ^ n := by
  let f : Euclidean d → ℝ := fun y => (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)
  have hq : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hfx : f x = 1 := by dsimp [f]; field_simp
  have hf : ContDiff ℝ (⊤ : ℕ∞ω) f :=
    contDiff_const.mul (contDiff_const.add (contDiff_norm_sq ℝ))
  have hg : ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => z ^ p) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (fun z hz => ne_of_gt hz)
  apply norm_iteratedFDeriv_comp_le' (t := Set.Ioi 0) (𝕜 := ℝ)
    (fun y hy => by obtain ⟨z, rfl⟩ := hy; change 0 < f z; dsimp [f]; positivity)
    (isOpen_Ioi.uniqueDiffOn : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ))) hg hf (by simp) x
  · intro i hi
    rw [hfx, iteratedFDerivWithin_eq_iteratedFDeriv
      (isOpen_Ioi.uniqueDiffOn : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ))) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)
      (by norm_num : (1 : ℝ) ∈ Set.Ioi 0),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_rpow_const, Real.one_rpow, mul_one]
    exact Finset.single_le_sum (f := fun j => ‖(descPochhammer ℝ j).eval p‖) (fun j _ => norm_nonneg _)
      (show i ∈ Finset.range (n+1) from Finset.mem_range.mpr (by omega))
  · intro i hi hin
    exact normalized_quadratic_deriv_bound i hi x


lemma rpow_quadratic_deriv_bound {d : ℕ} (p : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d,
      ‖iteratedFDeriv ℝ n (fun y : Euclidean d => (1 + ‖y‖ ^ 2) ^ p) x‖ ≤
        C * (1 + ‖x‖ ^ 2) ^ (p - (n : ℝ) / 2) := by
  let M : ℝ := ∑ i ∈ Finset.range (n+1), ‖(descPochhammer ℝ i).eval p‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨(n.factorial : ℝ) * M * 2^n, by positivity, ?_⟩
  intro x
  let q : ℝ := 1 + ‖x‖ ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  let f : Euclidean d → ℝ := fun y => (q⁻¹ * (1 + ‖y‖ ^ 2)) ^ p
  have hf : ContDiff ℝ n f :=
    (contDiff_const.mul (contDiff_const.add (contDiff_norm_sq ℝ))).rpow_const_of_ne
      (fun y => by dsimp [q]; positivity)
  have he : (fun y : Euclidean d => (1 + ‖y‖ ^ 2) ^ p) = q ^ p • f := by
    funext y
    change (1 + ‖y‖ ^ 2) ^ p = q ^ p * (q⁻¹ * (1 + ‖y‖ ^ 2)) ^ p
    rw [← Real.mul_rpow hq.le (by positivity)]
    congr 1
    field_simp
  rw [he, iteratedFDeriv_const_smul_apply hf.contDiffAt, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hq _)]
  have hR : Real.sqrt q ^ n = q ^ ((n : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    ring
  have hs : q ^ p * (2 / Real.sqrt q) ^ n = 2^n * q ^ (p - (n : ℝ)/2) := by
    rw [div_pow, hR, Real.rpow_sub hq]
    ring
  calc
    _ ≤ q ^ p * ((n.factorial : ℝ) * M * (2 / Real.sqrt q) ^ n) := by
      apply mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos hq _).le
      exact normalized_rpow_deriv_bound p n x
    _ = (n.factorial : ℝ) * M * (q ^ p * (2 / Real.sqrt q) ^ n) := by ring
    _ = _ := by rw [hs]; ring

lemma poisson_profile_deriv_bound (d n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d,
      ‖iteratedFDeriv ℝ n (poissonProfile d) x‖ ≤ C / (1 + ‖x‖) ^ (d+1+n) := by
  obtain ⟨C, hC, hb⟩ := rpow_quadratic_deriv_bound (d := d) (-((d : ℝ)+1)/2) n
  let r : ℝ := (d : ℝ)+1+n
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨C * 2 ^ (r / 2), by positivity, ?_⟩
  intro x
  have he : -((d : ℝ)+1)/2 - (n : ℝ)/2 = -r/2 := by dsimp [r]; ring
  calc
    _ ≤ C * (1 + ‖x‖ ^ 2) ^ (-r/2) := by
      change ‖iteratedFDeriv ℝ n (fun y : Euclidean d => (1 + ‖y‖ ^ 2) ^ (-((d : ℝ)+1)/2)) x‖ ≤ _
      simpa only [he] using hb x
    _ ≤ C * (2^(r/2) * (1 + ‖x‖)^(-r)) :=
      mul_le_mul_of_nonneg_left (rpow_neg_one_add_norm_sq_le x hr) hC
    _ = _ := by
      rw [Real.rpow_neg (by positivity)]
      have hex : r = ((d+1+n : ℕ) : ℝ) := by dsimp [r]; push_cast; ring
      rw [hex, Real.rpow_natCast]
      ring


lemma poisson_kernel_deriv_bound {𝕜 : Type} [RCLike 𝕜] (d n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d,
      ‖iteratedFDeriv ℝ n (poissonKernel 𝕜 d) x‖ ≤ C / (1 + ‖x‖) ^ (d+1+n) := by
  obtain ⟨C, hC, hb⟩ := poisson_profile_deriv_bound d n
  let f : Euclidean d → ℝ := poissonConstant d • poissonProfile d
  have hp : ContDiff ℝ n (poissonProfile d) := (poisson_profile_smooth d).of_le (by simp)
  have hf : ContDiff ℝ n f := contDiff_const.smul hp
  have he : poissonKernel 𝕜 d = (RCLike.ofRealCLM (K := 𝕜)) ∘ f := rfl
  refine ⟨poissonConstant d * C, mul_nonneg (poisson_constant_pos d).le hC, ?_⟩
  intro x
  rw [he]
  calc
    _ ≤ ‖(RCLike.ofRealCLM (K := 𝕜))‖ * ‖iteratedFDeriv ℝ n f x‖ :=
      (RCLike.ofRealCLM (K := 𝕜)).norm_iteratedFDeriv_comp_left hf.contDiffAt le_rfl
    _ = poissonConstant d * ‖iteratedFDeriv ℝ n (poissonProfile d) x‖ := by
      rw [RCLike.ofRealCLM_norm, one_mul]
      dsimp only [f]
      rw [iteratedFDeriv_const_smul_apply hp.contDiffAt,
        norm_smul, Real.norm_eq_abs, abs_of_pos (poisson_constant_pos d)]
    _ ≤ poissonConstant d * (C / (1 + ‖x‖) ^ (d+1+n)) :=
      mul_le_mul_of_nonneg_left (hb x) (poisson_constant_pos d).le
    _ = _ := by ring

theorem poisson_kernel_example : PoissonKernelExample := by
  intro 𝕜 _ d hd
  have hI := poisson_integral (𝕜 := 𝕜) d
  have hK : IsFixedKernel (poissonKernel 𝕜 d) := by
    refine ⟨?_, by rw [hI]; exact one_ne_zero, ?_⟩
    · exact (RCLike.ofRealCLM (K := 𝕜)).contDiff.comp
        (contDiff_const.mul (poisson_profile_smooth d))
    · intro n a
      obtain ⟨C, hC, hb⟩ := poisson_kernel_deriv_bound (𝕜 := 𝕜) d n
      refine ⟨C, hC, fun x => ?_⟩
      apply le_trans _ (hb x)
      have h := (iteratedFDeriv ℝ n (poissonKernel 𝕜 d) x).le_opNorm (fun i => basisVector (a i))
      simpa [coordinatePartial, basisVector] using h
  exact ⟨poisson_constant_pos d, hI, hK, characterization hd _ hK⟩


lemma dominated_integral_controls {X ι 𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    {μ : Measure X} (H : X → ℝ) (hH : Integrable H μ) (f : ι → Lp 𝕜 1 μ)
    (hdom : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ H x) :
    Controls μ (fun i => (f i : X → 𝕜)) := by
  have hc := weak_l1_finite_family_controls μ (fun _ : Unit => H) (fun _ => hH)
  have hmono (s : Set X) (i : ι) :
      (∫ x in s, ‖f i x‖ ∂μ) ≤ ∫ x in s, ‖H x‖ ∂μ := by
    apply integral_mono_ae (MeasureTheory.L1.integrable_coeFn (f i)).norm.integrableOn
      hH.norm.integrableOn
    exact (ae_restrict_of_ae (hdom i)).mono fun x hx => hx.trans (le_abs_self _)
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hs⟩ := hc.1 ε hε
    exact ⟨δ, hδ, fun s hsm hμ i => (hmono s i).trans_lt (hs s hsm hμ ())⟩
  · intro ε hε
    obtain ⟨s, hs, hμ, ht⟩ := hc.2 ε hε
    exact ⟨s, hs, hμ, fun i => (hmono sᶜ i).trans_lt (ht ())⟩

lemma dominated_weak_subsequence {X 𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    {μ : Measure X} [SigmaFinite μ] (H : X → ℝ) (hH : Integrable H μ)
    (f : ℕ → Lp 𝕜 1 μ) (hdom : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ H x) :
    ∃ g r, StrictMono r ∧ WeaklyConverges μ (f ∘ r) g := by
  let A : Set (Lp 𝕜 1 μ) := Set.range f
  have hdomA (g : A) : ∀ᵐ x ∂μ, ‖g.val x‖ ≤ H x := by
    obtain ⟨n, hn⟩ := g.property
    rw [← hn]
    exact hdom n
  have hb : Bornology.IsBounded A := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨∫ x, ‖H x‖ ∂μ, ?_⟩
    intro g hg
    rw [MeasureTheory.L1.norm_eq_integral_norm]
    apply integral_mono_ae (MeasureTheory.L1.integrable_coeFn g).norm hH.norm
    exact (hdomA ⟨g, hg⟩).mono fun x hx => hx.trans (le_abs_self _)
  have hc : UniformIntegralControls μ A := dominated_integral_controls H hH
    (fun g : A => g.val) hdomA
  have hcompact := scalar_l1_dunford_pettis_sufficiency μ A ⟨hb, hc⟩
  exact l1_compact_subsequence hcompact f (fun n => Set.mem_range_self n)

lemma tempered_recovery_of_regularization (hreg : TemperedRegularization) : TemperedRecovery := by
  intro 𝕜 _ d hd Φ hI u hF
  have h := hreg hd Φ u
  have hFm : Measurable (temperedRadial Φ u) := by
    apply LowerSemicontinuous.measurable
    apply lowerSemicontinuous_iSup
    intro t
    exact (ENNReal.continuous_ofReal.comp (h.1 t).norm).lowerSemicontinuous
  let F : Euclidean d → ℝ := fun x => (temperedRadial Φ u x).toReal
  have hFi : Integrable F := integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hF.ne
  have hfinite : ∀ᵐ x ∂volume, temperedRadial Φ u x ≠ (∞ : ℝ≥0∞) :=
    (ae_lt_top hFm hF.ne).mono (fun _ hx => hx.ne)
  let v : ℕ → Euclidean d → 𝕜 := fun n =>
    temperedConvolve Φ u ⟨((n : ℝ)+1)⁻¹, by positivity⟩
  have hvm (n : ℕ) : AEStronglyMeasurable (v n) volume := (h.1 _).aestronglyMeasurable
  have hvdom (n : ℕ) : ∀ᵐ x ∂volume, ‖v n x‖ ≤ F x := by
    filter_upwards [hfinite] with x hx
    apply (ENNReal.ofReal_le_iff_le_toReal hx).mp
    exact le_iSup (fun t : Scale => ENNReal.ofReal ‖temperedConvolve Φ u t x‖)
      ⟨((n : ℝ)+1)⁻¹, by positivity⟩
  have hvi (n : ℕ) : Integrable (v n) := hFi.mono' (hvm n) (hvdom n)
  let w : ℕ → Lp 𝕜 1 volume := fun n => (hvi n).toL1 (v n)
  have hwdom (n : ℕ) : ∀ᵐ x ∂volume, ‖w n x‖ ≤ F x := by
    filter_upwards [(hvi n).coeFn_toL1, hvdom n] with x hx hb
    exact hx ▸ hb
  obtain ⟨g, r, hr, hweak⟩ := dominated_weak_subsequence F hFi w hwdom
  have hg : Integrable (g : Euclidean d → 𝕜) := MeasureTheory.L1.integrable_coeFn g
  let c : 𝕜 := ∫ x, Φ x
  refine ⟨fun x => c⁻¹ * g x, hg.const_mul _, ?_⟩
  intro ψ
  have hseq := (h.2 ψ).comp hr.tendsto_atTop
  let L : Lp 𝕜 1 volume →L[𝕜] 𝕜 :=
    ScalarLpIntegralPairingSpec.IntegralPairingValue volume 1 ∞ (ψ.toLp ∞ volume)
  have hweak' := hweak L
  have hpair (a : Lp 𝕜 1 volume) : L a = ∫ x, ψ x * a x := by
    change ScalarLpIntegralPairingSpec.IntegralPairingValue volume 1 ∞ (ψ.toLp ∞ volume) a = _
    rw [(lp_pairing_integral volume 1 ∞ (ψ.toLp ∞ volume) a).2]
    apply integral_congr_ae
    exact (ψ.coeFn_toLp ∞ volume).mono (fun x hx => by simp only [hx, mul_comm])
  have he (n : ℕ) : L (w n) = ∫ x, ψ x * v n x := by
    rw [hpair]
    apply integral_congr_ae
    exact ((hvi n).coeFn_toL1).mono (fun x hx => congrArg (fun z => ψ x * z) hx)
  simp_rw [Function.comp_apply, he, hpair g] at hweak'
  have hlim : (∫ x, ψ x * g x) = c * u ψ := tendsto_nhds_unique hweak' hseq
  calc
    u ψ = c⁻¹ * (∫ x, ψ x * g x) := by rw [hlim]; field_simp [c, hI]
    _ = ∫ x, ψ x * (c⁻¹ * g x) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring


variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

abbrev SchwartzJet (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (s : Finset (SchwartzIndex d)) :=
  s → (Euclidean d →ᵇ 𝕜)

def schwartzJetMap (s : Finset (SchwartzIndex d)) :
    Schwartz 𝕜 d →L[𝕜] SchwartzJet 𝕜 s :=
  ContinuousLinearMap.pi fun a =>
    (SchwartzMap.toBoundedContinuousFunctionCLM 𝕜 (Euclidean d) 𝕜).comp
      (weightedPartial 𝕜 a.val)

@[simp] theorem schwartzJetMap_apply (s : Finset (SchwartzIndex d))
    (f : Schwartz 𝕜 d) (a : s) (x : Euclidean d) :
    schwartzJetMap s f a x =
      (monomial a.val.weight x : 𝕜) *
        iteratedFDeriv ℝ a.val.order f x (fun j => basisVector (a.val.directions j)) := by
  simp [schwartzJetMap]

theorem norm_schwartzJetMap (s : Finset (SchwartzIndex d)) (f : Schwartz 𝕜 d) :
    ‖schwartzJetMap s f‖ = s.sup (coordinateSchwartzSeminorm 𝕜) f := by
  classical
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
    intro a
    apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
    intro x
    have h := (seminorm_formula 𝕜 d a.val f _ (apply_nonneg _ _)).mp
      (Finset.le_sup (f := coordinateSchwartzSeminorm 𝕜) a.property f) x
    simpa using h
  · apply Seminorm.finset_sup_apply_le (norm_nonneg _)
    intro a ha
    apply (seminorm_formula 𝕜 d a f _ (norm_nonneg _)).mpr
    intro x
    rw [← schwartzJetMap_apply s f ⟨a, ha⟩]
    exact (BoundedContinuousFunction.norm_coe_le_norm _ x).trans
      (norm_le_pi_norm (schwartzJetMap s f) ⟨a, ha⟩)

def schwartzZeroIndex (d : ℕ) : SchwartzIndex d := ⟨0, 0, Fin.elim0, Fin.elim0⟩

theorem schwartzJetMap_injective (s : Finset (SchwartzIndex d))
    (hs : schwartzZeroIndex d ∈ s) :
    Function.Injective (schwartzJetMap (𝕜 := 𝕜) s) := by
  intro f g h
  ext x
  have hx := congrArg (fun z : SchwartzJet 𝕜 s => z ⟨schwartzZeroIndex d, hs⟩ x) h
  simpa [schwartzZeroIndex, monomial] using hx

theorem tempered_schwartzJet_factorization (u : Tempered 𝕜 d) :
    ∃ s : Finset (SchwartzIndex d), ∃ L : SchwartzJet 𝕜 s →L[𝕜] 𝕜,
      ∀ f : Schwartz 𝕜 d, L (schwartzJetMap s f) = u f := by
  classical
  let p := coordinateSchwartzSeminorm 𝕜 (d := d)
  let q := (normSeminorm 𝕜 𝕜).comp u.toLinearMap
  have hq : Continuous q := continuous_norm.comp u.continuous
  obtain ⟨s₀, C, _, hC⟩ := Seminorm.bound_of_continuous (seminorm_topology 𝕜 d) q hq
  let s := insert (schwartzZeroIndex d) s₀
  let J := schwartzJetMap (𝕜 := 𝕜) s
  let e := LinearEquiv.ofInjective J.toLinearMap
    (schwartzJetMap_injective s (Finset.mem_insert_self _ _))
  let v : J.range →ₗ[𝕜] 𝕜 := u.toLinearMap.comp e.symm.toLinearMap
  have hv : ∀ z : J.range, ‖v z‖ ≤ C * ‖z‖ := by
    intro z
    have hj : J (e.symm z) = z.val := congrArg Subtype.val (e.apply_symm_apply z)
    change ‖u (e.symm z)‖ ≤ C * ‖z‖
    calc
      _ ≤ C * s₀.sup p (e.symm z) := hC (e.symm z)
      _ ≤ C * s.sup p (e.symm z) := by
        gcongr
        apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
        intro a ha
        exact Finset.le_sup (f := p) (Finset.mem_insert_of_mem ha) (e.symm z)
      _ = C * ‖z‖ := by
        rw [← norm_schwartzJetMap]
        change C * ‖J (e.symm z)‖ = C * ‖z‖
        rw [hj]
        rfl
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq J.range (v.mkContinuous C hv)
  refine ⟨s, L, fun f => ?_⟩
  have he := hL (e f)
  simpa [v, e] using he

/-- A Banach-valued realization of the transpose convolution reduces interchange
with an arbitrary tempered distribution to the ordinary Bochner integral API. -/
lemma temperedConvolve_transpose_of_jet_integral
    {𝕜 B : Type} [RCLike 𝕜] [NormedAddCommGroup B] [CompleteSpace B] [NormedSpace 𝕜 B] [NormedSpace ℝ B] [IsScalarTower ℝ 𝕜 B]
    {d : ℕ} (Φ ψ θ : Schwartz 𝕜 d) (u : Tempered 𝕜 d) (t : Scale)
    (J : Schwartz 𝕜 d →ₗ[𝕜] B) (L : B →L[𝕜] 𝕜)
    (hL : ∀ η, L (J η) = u η)
    (hi : Integrable (fun x => ψ x • J (kernelTest Φ t x)))
    (heq : (∫ x, ψ x • J (kernelTest Φ t x)) = J θ) :
    (∫ x, ψ x * temperedConvolve Φ u t x) = u θ := by
  calc
    _ = ∫ x, L (ψ x • J (kernelTest Φ t x)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [map_smul, hL]
      rfl
    _ = L (∫ x, ψ x • J (kernelTest Φ t x)) :=
      L.integral_comp_comm hi
    _ = u θ := by rw [heq, hL]

/-- The preceding identity plus convergence of finite jets proves the required
weak regularization limit. The convergence lives in an ordinary normed space. -/
lemma temperedConvolve_tendsto_of_jet_integrals
    {𝕜 B : Type} [RCLike 𝕜] [NormedAddCommGroup B] [CompleteSpace B] [NormedSpace 𝕜 B] [NormedSpace ℝ B] [IsScalarTower ℝ 𝕜 B]
    {d : ℕ} (Φ ψ : Schwartz 𝕜 d) (u : Tempered 𝕜 d)
    (J : Schwartz 𝕜 d →ₗ[𝕜] B) (L : B →L[𝕜] 𝕜)
    (hL : ∀ η, L (J η) = u η)
    (hi : ∀ n : ℕ, Integrable (fun x => ψ x •
      J (kernelTest Φ ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x)))
    (hlim : Tendsto (fun n : ℕ => ∫ x, ψ x •
      J (kernelTest Φ ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x)) atTop
      (𝓝 ((∫ x, Φ x) • J ψ))) :
    Tendsto (fun n : ℕ => ∫ x, ψ x *
      temperedConvolve Φ u ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x) atTop
      (𝓝 ((∫ x, Φ x) * u ψ)) := by
  have h := L.continuous.tendsto ((∫ x, Φ x) • J ψ) |>.comp hlim
  have hfun : (fun n : ℕ => ∫ x, ψ x *
      temperedConvolve Φ u ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x) =
      L ∘ (fun n : ℕ => ∫ x, ψ x •
        J (kernelTest Φ ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x)) := by
    funext n
    calc
      _ = ∫ x, L (ψ x • J (kernelTest Φ ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [map_smul, hL]
        rfl
      _ = _ := L.integral_comp_comm (hi n)
  rw [hfun]
  simpa only [map_smul, hL, smul_eq_mul] using h

lemma schwartz_lineDeriv_comm (f : Schwartz 𝕜 d) (v w : Euclidean d) :
    ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) := by
  ext x
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f y v) x w
  have hd := ((f.smooth ⊤).fderiv_right (m := ∞) (by simp)).differentiable
    (by simp) x
  simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_fun_const,
    Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact (f.smooth ⊤).contDiffAt.isSymmSndFDerivAt (by simp) v w

lemma schwartz_iteratedLineDeriv_lineDeriv {n : ℕ} (v : Fin n → Euclidean d)
    (w : Euclidean d) (f : Schwartz 𝕜 d) :
    ∂^{v} (∂_{w} f) = ∂_{w} (∂^{v} f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, ih]
    exact schwartz_lineDeriv_comm _ _ _

lemma integral_schwartz_mul_iteratedLineDeriv {n : ℕ}
    (f g : Schwartz 𝕜 d) (v : Fin n → Euclidean d) :
    (∫ x, f x * ∂^{v} g x) =
      (-1 : 𝕜) ^ n * (∫ x, ∂^{v} f x * g x) := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left,
      SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left,
      ih, schwartz_iteratedLineDeriv_lineDeriv]
    rw [iteratedLineDerivOp_succ_left, pow_succ]
    ring

lemma integral_schwartz_iteratedFDeriv_mul {n : ℕ}
    (f g : Schwartz 𝕜 d) (v : Fin n → Euclidean d) :
    (∫ x, iteratedFDeriv ℝ n f x v * g x) =
      (-1 : 𝕜) ^ n * (∫ x, f x * iteratedFDeriv ℝ n g x v) := by
  have hi := integral_schwartz_mul_iteratedLineDeriv g f v
  simpa only [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, mul_comm] using hi

lemma integral_schwartz_iteratedFDeriv_neg_mul {n : ℕ}
    (f g : Schwartz 𝕜 d) (v : Fin n → Euclidean d) :
    (∫ x, iteratedFDeriv ℝ n f x (fun j => -v j) * g x) =
      ∫ x, f x * iteratedFDeriv ℝ n g x v := by
  have hneg (x : Euclidean d) :
      iteratedFDeriv ℝ n f x (fun j => -v j) =
        (-1 : 𝕜)^n * iteratedFDeriv ℝ n f x v := by
    have h := (iteratedFDeriv ℝ n f x).map_smul_univ (fun _ => (-1 : ℝ)) v
    simpa [RCLike.real_smul_eq_coe_mul] using h
  simp_rw [hneg, mul_assoc]
  rw [integral_const_mul, integral_schwartz_iteratedFDeriv_mul,
    ← mul_assoc, ← mul_pow]
  simp


lemma schwartz_integrable_norm_mul_one_add_norm_pow (Φ : Schwartz 𝕜 d) (k : ℕ) :
    Integrable (fun x => ‖Φ x‖ * (1 + ‖x‖) ^ k) := by
  have hi : Integrable (fun x =>
      2 ^ (k-1) * (‖Φ x‖ + ‖x‖ ^ k * ‖Φ x‖)) :=
    (Φ.integrable.norm.add (Φ.integrable_pow_mul volume k)).const_mul _
  apply hi.mono' (by fun_prop)
  filter_upwards with x
  have hb := add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (norm_nonneg x) k
  simp only [one_pow] at hb
  calc
    ‖‖Φ x‖ * (1 + ‖x‖) ^ k‖ = ‖Φ x‖ * (1 + ‖x‖) ^ k := Real.norm_of_nonneg (by positivity)
    _ ≤ ‖Φ x‖ * (2 ^ (k-1) * (1 + ‖x‖ ^ k)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

lemma schwartz_translated_integral_tendsto
    {B : Type} [NormedAddCommGroup B] [CompleteSpace B]
    [NormedSpace 𝕜 B] [NormedSpace ℝ B] [IsScalarTower ℝ 𝕜 B]
    (Φ ψ : Schwartz 𝕜 d) (J : Schwartz 𝕜 d →L[𝕜] B)
    (htrans : Continuous (fun a : Euclidean d => SchwartzMap.compSubConstCLM 𝕜 a ψ))
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a : Euclidean d,
      ‖J (SchwartzMap.compSubConstCLM 𝕜 a ψ)‖ ≤ C * (1 + ‖a‖) ^ k) :
    Tendsto (fun n : ℕ => ∫ z, Φ z •
      J (SchwartzMap.compSubConstCLM 𝕜 (-(((n : ℝ) + 1)⁻¹ • z)) ψ)) atTop
      (𝓝 ((∫ z, Φ z) • J ψ)) := by
  have hzero : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (z : Euclidean d) => Φ z •
      J (SchwartzMap.compSubConstCLM 𝕜 (-(((n : ℝ) + 1)⁻¹ • z)) ψ))
    (f := fun z : Euclidean d => Φ z • J ψ)
    (fun z : Euclidean d => C * (‖Φ z‖ * (1 + ‖z‖) ^ k))
    (fun n => by
      apply Continuous.aestronglyMeasurable
      exact Φ.continuous.smul (J.continuous.comp (htrans.comp (by fun_prop))))
    ((schwartz_integrable_norm_mul_one_add_norm_pow Φ k).const_mul C)
    (fun n => Filter.Eventually.of_forall fun z => by
      rw [norm_smul]
      apply (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)).trans
      have ht : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      have hnn : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      have ha : ‖-(((n : ℝ) + 1)⁻¹ • z)‖ ≤ ‖z‖ := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
        exact mul_le_of_le_one_left (norm_nonneg z) ht
      calc
        ‖Φ z‖ * (C * (1 + ‖-(((n : ℝ) + 1)⁻¹ • z)‖) ^ k) ≤
          ‖Φ z‖ * (C * (1 + ‖z‖) ^ k) := by gcongr
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun z => by
      have hz : Tendsto (fun n : ℕ => -(((n : ℝ) + 1)⁻¹ • z)) atTop (𝓝 0) := by
        simpa using (hzero.smul_const z).neg
      have hp := (J.continuous.tendsto _).comp ((htrans.tendsto 0).comp hz)
      simpa only [Function.comp_apply, SchwartzMap.compSubConstCLM_zero, ContinuousLinearMap.id_apply]
        using tendsto_const_nhds.smul hp)
  simpa only [integral_smul_const] using hlim
lemma tempered_convolve_continuous {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) (u : Tempered 𝕜 d) (t : Scale) : Continuous (temperedConvolve Φ u t) := by
  have ht : Continuous (fun x : Euclidean d =>
      SchwartzMap.compSubConstCLM 𝕜 (-(t.val⁻¹ • x)) Φ) :=
    (SchwartzMap.continuous_compSubConst_rclike Φ).comp (by fun_prop)
  let A : Schwartz 𝕜 d →L[𝕜] Schwartz 𝕜 d := SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean d)
        (Units.mk0 (-t.val⁻¹) (neg_ne_zero.mpr (inv_ne_zero t.property.ne'))))
  exact u.continuous.comp ((A.continuous.comp ht).const_smul ((t.val ^ d)⁻¹))

lemma kernelTest_iteratedFDeriv_eq {n : ℕ}
    (Φ : Schwartz 𝕜 d) (t : Scale) (x y : Euclidean d) (v : Fin n → Euclidean d) :
    iteratedFDeriv ℝ n (kernelTest Φ t x) y v =
      iteratedFDeriv ℝ n (HardyLowpass.dilateSchwartz t.val t.property Φ) (x-y)
        (fun j => -v j) := by
  let H := HardyLowpass.dilateSchwartz t.val t.property Φ
  let N : Euclidean d →L[ℝ] Euclidean d := -ContinuousLinearMap.id ℝ _
  have heq : (kernelTest Φ t x : Euclidean d → 𝕜) = (fun z => H (x+z)) ∘ N := by
    funext z
    simp only [kernelTest, smul_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      SchwartzMap.compSubConstCLM_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_def, Units.val_mk0, H, HardyLowpass.dilateSchwartz_apply, dilate, N,
      neg_apply, ContinuousLinearMap.id_apply]
    congr 2
    module
  rw [heq, N.iteratedFDeriv_comp_right (f := fun z => H (x+z))
    ((H.smooth ⊤).comp (contDiff_const.add contDiff_id)) y (i := n) (by simp)]
  simp only [N, neg_apply, ContinuousLinearMap.id_apply, iteratedFDeriv_comp_add_left, sub_eq_add_neg]
  rfl

lemma kernelTest_iteratedFDeriv_transpose {n : ℕ}
    (Φ ψ : Schwartz 𝕜 d) (t : Scale) (y : Euclidean d) (v : Fin n → Euclidean d) :
    (∫ x, ψ x * iteratedFDeriv ℝ n (kernelTest Φ t x) y v) =
      ∫ z, Φ z * iteratedFDeriv ℝ n ψ (y+t.val • z) v := by
  let H := HardyLowpass.dilateSchwartz t.val t.property Φ
  let G := SchwartzMap.compSubConstCLM 𝕜 (-y) ψ
  have hG (z : Euclidean d) : G z = ψ (z+y) := by simp [G]
  have hderG (z : Euclidean d) : iteratedFDeriv ℝ n G z v =
      iteratedFDeriv ℝ n ψ (z+y) v := by
    change iteratedFDeriv ℝ n (fun z => ψ (z-(-y))) z v = _
    rw [iteratedFDeriv_comp_sub]
    simp
  calc
    _ = ∫ x, iteratedFDeriv ℝ n H (x-y) (fun j => -v j) * ψ x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [kernelTest_iteratedFDeriv_eq]
      exact mul_comm _ _
    _ = ∫ z, iteratedFDeriv ℝ n H z (fun j => -v j) * G z := by
      have ht := integral_sub_right_eq_self (μ := (volume : Measure (Euclidean d)))
        (fun z => iteratedFDeriv ℝ n H z (fun j => -v j) * ψ (z+y)) y
      simpa only [sub_add_cancel, hG] using ht
    _ = ∫ z, H z * iteratedFDeriv ℝ n G z v :=
      integral_schwartz_iteratedFDeriv_neg_mul H G v
    _ = ∫ z, Φ z * iteratedFDeriv ℝ n ψ (y+t.val • z) v := by
      let F : Euclidean d → 𝕜 := fun z => Φ z * iteratedFDeriv ℝ n ψ (y+t.val • z) v
      have hpoint (z : Euclidean d) : H z * iteratedFDeriv ℝ n G z v =
          (t.val ^ d)⁻¹ • F (t.val⁻¹ • z) := by
        simp only [H, HardyLowpass.dilateSchwartz_apply, dilate, hderG, F,
          smul_smul, mul_inv_cancel₀ t.property.ne', one_smul]
        rw [add_comm y z, smul_mul_assoc]
      simp_rw [hpoint]
      rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg volume F t.property.le]
      simp [finrank_euclideanSpace, t.property.ne', F]


lemma schwartzJetMap_kernel_integral_transpose
    (s : Finset (SchwartzIndex d)) (Φ ψ : Schwartz 𝕜 d) (t : Scale)
    (hi : Integrable (fun x => ψ x • schwartzJetMap s (kernelTest Φ t x)))
    (hj : Integrable (fun z => Φ z • schwartzJetMap s
      (SchwartzMap.compSubConstCLM 𝕜 (-(t.val • z)) ψ))) :
    (∫ x, ψ x • schwartzJetMap s (kernelTest Φ t x)) =
      ∫ z, Φ z • schwartzJetMap s (SchwartzMap.compSubConstCLM 𝕜 (-(t.val • z)) ψ) := by
  ext a y
  let ev : SchwartzJet 𝕜 s →L[𝕜] 𝕜 :=
    (BoundedContinuousFunction.evalCLM 𝕜 y).comp (ContinuousLinearMap.proj a)
  have hl := ev.integral_comp_comm hi
  have hr := ev.integral_comp_comm hj
  have hp (z : Euclidean d) :
      schwartzJetMap s (SchwartzMap.compSubConstCLM 𝕜 (-(t.val • z)) ψ) a y =
        (monomial a.val.weight y : 𝕜) *
          iteratedFDeriv ℝ a.val.order ψ (y+t.val • z)
            (fun j => basisVector (a.val.directions j)) := by
    rw [schwartzJetMap_apply]
    congr 1
    change iteratedFDeriv ℝ a.val.order
      (fun w => ψ (w-(-(t.val • z)))) y _ = _
    rw [iteratedFDeriv_comp_sub]
    simp
  change ev (∫ x, ψ x • schwartzJetMap s (kernelTest Φ t x)) =
    ev (∫ z, Φ z • schwartzJetMap s (SchwartzMap.compSubConstCLM 𝕜 (-(t.val • z)) ψ))
  rw [← hl, ← hr]
  change (∫ x, ψ x * schwartzJetMap s (kernelTest Φ t x) a y) =
    ∫ z, Φ z * schwartzJetMap s (SchwartzMap.compSubConstCLM 𝕜 (-(t.val • z)) ψ) a y
  simp_rw [schwartzJetMap_apply s (kernelTest Φ t _), hp]
  have hleft (x : Euclidean d) : ψ x * ((monomial a.val.weight y : 𝕜) *
      iteratedFDeriv ℝ a.val.order (kernelTest Φ t x) y
        (fun j => basisVector (a.val.directions j))) =
      (monomial a.val.weight y : 𝕜) * (ψ x *
        iteratedFDeriv ℝ a.val.order (kernelTest Φ t x) y
          (fun j => basisVector (a.val.directions j))) := by ring
  have hright (z : Euclidean d) : Φ z * ((monomial a.val.weight y : 𝕜) *
      iteratedFDeriv ℝ a.val.order ψ (y+t.val • z)
        (fun j => basisVector (a.val.directions j))) =
      (monomial a.val.weight y : 𝕜) * (Φ z *
        iteratedFDeriv ℝ a.val.order ψ (y+t.val • z)
          (fun j => basisVector (a.val.directions j))) := by ring
  simp_rw [hleft, hright]
  rw [integral_const_mul, integral_const_mul, kernelTest_iteratedFDeriv_transpose]


lemma schwartz_clm_translation_growth
    {B : Type} [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    (J : Schwartz 𝕜 d →L[𝕜] B) (ψ : Schwartz 𝕜 d) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Euclidean d,
      ‖J (SchwartzMap.compSubConstCLM 𝕜 a ψ)‖ ≤ C * (1+‖a‖)^k := by
  classical
  let p := schwartzSeminormFamily 𝕜 (Euclidean d) 𝕜
  let q := (normSeminorm 𝕜 B).comp J.toLinearMap
  have hq : Continuous q := continuous_norm.comp J.continuous
  obtain ⟨s, C₀, _, hC₀⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms 𝕜 (Euclidean d) 𝕜) q hq
  let k := s.sup Prod.fst
  let c : ℕ × ℕ → ℝ := fun m => 2 ^ m.1 *
    (Finset.Iic m).sup (schwartzSeminormFamily ℝ (Euclidean d) 𝕜) ψ
  have hc : ∀ m, 0 ≤ c m := by intro m; dsimp [c]; positivity
  refine ⟨k, C₀ * ∑ m ∈ s, c m, by positivity, ?_⟩
  intro a
  have heq : SchwartzMap.compSubConstCLM 𝕜 a ψ = SchwartzMap.compSubConstCLM ℝ a ψ := by
    ext x
    rfl
  calc
    ‖J (SchwartzMap.compSubConstCLM 𝕜 a ψ)‖ ≤
        C₀ * s.sup p (SchwartzMap.compSubConstCLM 𝕜 a ψ) := hC₀ _
    _ ≤ C₀ * ((∑ m ∈ s, c m) * (1+‖a‖)^k) := by
      gcongr
      apply Seminorm.finset_sup_apply_le (by positivity)
      intro m hm
      calc
        p m (SchwartzMap.compSubConstCLM 𝕜 a ψ) ≤ c m * (1+‖a‖)^m.1 := by
          rw [heq]
          exact SchwartzMap.translation_seminorm_growth ψ m.1 m.2 a
        _ ≤ _ := by
          gcongr
          · exact Finset.single_le_sum (fun b _ => hc b) hm
          · exact le_add_of_nonneg_right (norm_nonneg a)
          · exact Finset.le_sup (f := Prod.fst) hm
    _ = _ := by ring


lemma schwartz_clm_translated_integrable
    {B : Type} [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    (Φ ψ : Schwartz 𝕜 d) (J : Schwartz 𝕜 d →L[𝕜] B) (r : ℝ) :
    Integrable (fun z => Φ z • J (SchwartzMap.compSubConstCLM 𝕜 (-(r • z)) ψ)) := by
  obtain ⟨k,C,hC,hbound⟩ := schwartz_clm_translation_growth J ψ
  have htrans : Continuous (fun a : Euclidean d => SchwartzMap.compSubConstCLM 𝕜 a ψ) := by
    convert SchwartzMap.continuous_compSubConst ψ using 1
    funext a
    ext x
    rfl
  have hcont : Continuous (fun z : Euclidean d =>
      Φ z • J (SchwartzMap.compSubConstCLM 𝕜 (-(r • z)) ψ)) :=
    Φ.continuous.smul (J.continuous.comp (htrans.comp (by fun_prop)))
  have hi := (schwartz_integrable_norm_mul_one_add_norm_pow Φ k).const_mul
    (C * (1+‖r‖)^k)
  apply hi.mono' hcont.aestronglyMeasurable
  filter_upwards with z
  rw [norm_smul]
  apply (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)).trans
  have ha : 1 + ‖-(r • z)‖ ≤ (1+‖r‖) * (1+‖z‖) := by
    rw [norm_neg, norm_smul]
    nlinarith [norm_nonneg r, norm_nonneg z]
  calc
    ‖Φ z‖ * (C * (1+‖-(r • z)‖)^k) ≤
        ‖Φ z‖ * (C * ((1+‖r‖) * (1+‖z‖))^k) := by gcongr
    _ = _ := by rw [mul_pow]; ring


lemma kernelTest_schwartzJet_integrable
    {B : Type} [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    (Φ ψ : Schwartz 𝕜 d) (J : Schwartz 𝕜 d →L[𝕜] B) (t : Scale) :
    Integrable (fun x => ψ x • J (kernelTest Φ t x)) := by
  let A : Schwartz 𝕜 d →L[𝕜] Schwartz 𝕜 d := (t.val ^ d)⁻¹ •
    (SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean d)
        (Units.mk0 (-t.val⁻¹) (neg_ne_zero.mpr (inv_ne_zero t.property.ne')))))
  have hi := schwartz_clm_translated_integrable ψ Φ (J.comp A) t.val⁻¹
  exact hi


lemma schwartz_clm_translated_integral_tendsto
    {B : Type} [NormedAddCommGroup B] [CompleteSpace B]
    [NormedSpace 𝕜 B] [NormedSpace ℝ B] [IsScalarTower ℝ 𝕜 B]
    (Φ ψ : Schwartz 𝕜 d) (J : Schwartz 𝕜 d →L[𝕜] B) :
    Tendsto (fun n : ℕ => ∫ z, Φ z •
      J (SchwartzMap.compSubConstCLM 𝕜 (-(((n : ℝ) + 1)⁻¹ • z)) ψ)) atTop
      (𝓝 ((∫ z, Φ z) • J ψ)) := by
  obtain ⟨k,C,hC,hbound⟩ := schwartz_clm_translation_growth J ψ
  apply schwartz_translated_integral_tendsto Φ ψ J _ k C hC hbound
  convert SchwartzMap.continuous_compSubConst ψ using 1
  funext a
  ext x
  rfl


theorem tempered_regularization : TemperedRegularization := by
  intro 𝕜 _ d _ Φ u
  refine ⟨tempered_convolve_continuous Φ u, ?_⟩
  intro ψ
  obtain ⟨s, L, hL⟩ := tempered_schwartzJet_factorization u
  apply temperedConvolve_tendsto_of_jet_integrals Φ ψ u
    (schwartzJetMap s).toLinearMap L hL
  · intro n
    exact kernelTest_schwartzJet_integrable Φ ψ (schwartzJetMap s) _
  · have heq : (fun n : ℕ => ∫ x, ψ x • schwartzJetMap s
        (kernelTest Φ ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x)) =
        (fun n : ℕ => ∫ z, Φ z • schwartzJetMap s
          (SchwartzMap.compSubConstCLM 𝕜 (-(((n : ℝ)+1)⁻¹ • z)) ψ)) := by
      funext n
      exact schwartzJetMap_kernel_integral_transpose s Φ ψ _
        (kernelTest_schwartzJet_integrable Φ ψ (schwartzJetMap s) _)
        (schwartz_clm_translated_integrable Φ ψ (schwartzJetMap s) _)
    change Tendsto (fun n : ℕ => ∫ x, ψ x • schwartzJetMap s
      (kernelTest Φ ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x)) atTop
      (𝓝 ((∫ x, Φ x) • schwartzJetMap s ψ))
    rw [heq]
    exact schwartz_clm_translated_integral_tendsto Φ ψ (schwartzJetMap s)

theorem tempered_recovery : TemperedRecovery :=
  tempered_recovery_of_regularization tempered_regularization

theorem tempered_characterization : TemperedCharacterization :=
  tempered_characterization_of_recovery tempered_recovery


end ExpandedFA.PartIV.HardyFixedMaximal
