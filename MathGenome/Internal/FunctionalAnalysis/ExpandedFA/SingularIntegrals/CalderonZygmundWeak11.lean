import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.StandardConvolutionOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundDecomposition
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace ExpandedFA.SingularIntegrals.CZWeak
open StandardConvolution

/-- An elementary bound sufficient for either real or complex scalar outputs.
The factor d is harmless for the dimension-dependent endpoint constant. -/
theorem linear_norm_le_sum_basis {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (L : Space d →L[ℝ] 𝕜) :
    ‖L‖ ≤ ∑ i : Fin d, ‖L (ExpandedFA.Fourier.basisVector i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : x = ∑ i : Fin d, (x i) • ExpandedFA.Fourier.basisVector i := by
    simpa [ExpandedFA.Fourier.basisVector, EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x).symm
  calc
    ‖L x‖ = ‖∑ i : Fin d, (x i) • L (ExpandedFA.Fourier.basisVector i)‖ := by
      conv_lhs => rw [hx, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin d, ‖(x i) • L (ExpandedFA.Fourier.basisVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, ‖x‖ * ‖L (ExpandedFA.Fourier.basisVector i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i : Fin d, ‖L (ExpandedFA.Fourier.basisVector i)‖) * ‖x‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- Each coordinate component is bounded by the Euclidean gradient length. -/
theorem component_le_gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : Space d → 𝕜) (x : Space d) (i : Fin d) :
    ‖fderiv ℝ k x (ExpandedFA.Fourier.basisVector i)‖ ≤ kernelGradientNorm k x := by
  unfold kernelGradientNorm
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun j _ => sq_nonneg (‖fderiv ℝ k x (ExpandedFA.Fourier.basisVector j)‖)) (Finset.mem_univ i)

theorem fderiv_norm_le_gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : Space d → 𝕜) (x : Space d) :
    ‖fderiv ℝ k x‖ ≤ (d : ℝ) * kernelGradientNorm k x := by
  apply (linear_norm_le_sum_basis _).trans
  calc
    (∑ i : Fin d, ‖fderiv ℝ k x (ExpandedFA.Fourier.basisVector i)‖) ≤
      ∑ _i : Fin d, kernelGradientNorm k x :=
        Finset.sum_le_sum fun i _ => component_le_gradient k x i
    _ = (d : ℝ) * kernelGradientNorm k x := by simp

/-- The segment lies in a ball separated from the singularity. -/
theorem kernel_difference :
    Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11.KernelDifference := by
  intro 𝕜 _ d k a h ha hh
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let B := Metric.closedBall a (‖a‖ / 2)
  have hnorm (z : Space d) (hz : z ∈ B) : ‖a‖ / 2 ≤ ‖z‖ := by
    have hz' : ‖z - a‖ ≤ ‖a‖ / 2 := by simpa [B, dist_eq_norm] using hz
    have hn := norm_sub_le a z
    rw [norm_sub_rev a z] at hn
    have ht : ‖a‖ ≤ ‖z - a‖ + ‖z‖ := by
      calc
        ‖a‖ = ‖(a - z) + z‖ := by congr 1; abel
        _ ≤ ‖a - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z - a‖ + ‖z‖ := by rw [norm_sub_rev a z]
    linarith
  have hne (z : Space d) (hz : z ∈ B) : z ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by linarith) (hnorm z hz))
  have hd (z : Space d) (hz : z ∈ B) : DifferentiableAt ℝ k.function z := by
    exact (k.contDiff.differentiableOn (by norm_num) z (hne z hz)).differentiableAt
      (isClosed_singleton.isOpen_compl.mem_nhds (hne z hz))
  have hb (z : Space d) (hz : z ∈ B) :
      ‖fderiv ℝ k.function z‖ ≤
        (d : ℝ) * k.constant / (‖a‖ / 2) ^ (d + 1) := by
    calc
      ‖fderiv ℝ k.function z‖ ≤ (d : ℝ) * kernelGradientNorm k.function z :=
        fderiv_norm_le_gradient _ _
      _ ≤ (d : ℝ) * (k.constant / ‖z‖ ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left (k.gradient z (hne z hz)) (Nat.cast_nonneg _)
      _ ≤ (d : ℝ) * (k.constant / (‖a‖ / 2) ^ (d + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
        exact div_le_div_of_nonneg_left k.constant_nonneg (by positivity)
          (pow_le_pow_left₀ (by positivity) (hnorm z hz) _)
      _ = _ := by ring
  have hma : a ∈ B := Metric.mem_closedBall_self (by positivity)
  have hmh : a - h ∈ B := by simpa [B, dist_eq_norm] using hh
  have hv := Convex.norm_image_sub_le_of_norm_fderiv_le hd hb (convex_closedBall a _) hma hmh
  have heq : ‖a - h - a‖ = ‖h‖ := by rw [sub_right_comm, sub_self, zero_sub, norm_neg]
  rw [heq] at hv
  calc
    ‖k.function (a - h) - k.function a‖ ≤
        (d : ℝ) * k.constant / (‖a‖ / 2) ^ (d + 1) * ‖h‖ := hv
    _ = ((d : ℝ) * k.constant * 2 ^ (d + 1)) * ‖h‖ / ‖a‖ ^ (d + 1) := by
      rw [div_pow]
      field_simp

/-- Radial tail calculation; the strict exterior avoids any boundary convention. -/
theorem radial_tail {d : ℕ} (hd : 0 < d) (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : Space d =>
      (Set.Ioi R).indicator (fun r : ℝ => 1 / r ^ (d + 1)) ‖x‖) volume ∧
    (∫ x : Space d, (Set.Ioi R).indicator (fun r : ℝ => 1 / r ^ (d + 1)) ‖x‖) =
      (d : ℝ) * volume.real (Metric.ball (0 : Space d) 1) / R := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have heq (r : ℝ) (hr : 0 < r) :
      r ^ (d - 1) * (Set.Ioi R).indicator (fun r : ℝ => 1 / r ^ (d + 1)) r =
        (Set.Ioi R).indicator (fun r : ℝ => r ^ (-2 : ℝ)) r := by
    by_cases h : R < r
    · simp only [Set.indicator_of_mem (show r ∈ Ioi R from h)]
      rw [show d + 1 = (d - 1) + 2 by omega, pow_add]
      rw [Real.rpow_neg hr.le, Real.rpow_two]
      field_simp
    · simp [h]
  have hi : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hR
  have his : IntegrableOn ((Ioi R).indicator (fun r : ℝ => r ^ (-2 : ℝ))) (Ioi 0) :=
    (hi.integrable_indicator measurableSet_Ioi).integrableOn
  have hrad : IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      (Ioi R).indicator (fun r : ℝ => 1 / r ^ (d + 1)) r) (Ioi 0) :=
    his.congr_fun (fun r hr => (heq r hr).symm) measurableSet_Ioi
  have hdim : Module.finrank ℝ (Space d) = d := by simp [Space, ExpandedFA.Fourier.Euclidean]
  constructor
  · rw [integrable_fun_norm_addHaar volume]
    simpa [hdim, smul_eq_mul] using hrad
  · rw [integral_fun_norm_addHaar volume]
    simp only [hdim, smul_eq_mul, nsmul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi heq]
    have hsub : Ioi R ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hR.le
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr hsub, integral_Ioi_rpow_of_lt (by norm_num) hR]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv, mul_assoc]



theorem cubeRadius_pos {d : ℕ} (q : CZ.DyadicCube d) : 0 < cubeRadius q := by
  unfold cubeRadius CZ.side
  positivity

/-- The half-open coordinate cube is contained in the selected compact ball. -/
theorem cube_subset_closedBall {d : ℕ} (q : CZ.DyadicCube d) :
    CZ.cube q ⊆ Metric.closedBall (cubeCenter q) (cubeRadius q) := by
  intro y hy
  have hs : 0 < CZ.side q := by unfold CZ.side; positivity
  have hc (i : Fin d) : ‖(y - cubeCenter q) i‖ ≤ CZ.side q := by
    change |y i - CZ.side q * ((q.2 i : ℝ) + 1 / 2)| ≤ CZ.side q
    have hi := hy i
    apply abs_le.mpr
    constructor <;> dsimp [CZ.cube] at hi <;> linarith
  have hsq : ‖y - cubeCenter q‖ ^ 2 ≤ (d : ℝ) * CZ.side q ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      (∑ i : Fin d, ‖(y - cubeCenter q) i‖ ^ 2) ≤ ∑ _i : Fin d, CZ.side q ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (hc i) _
      _ = _ := by simp
  have hr : cubeRadius q ^ 2 = (d + 1 : ℝ) * CZ.side q ^ 2 := by
    rw [cubeRadius, mul_pow, Real.sq_sqrt (by positivity)]
  have hrad := (cubeRadius_pos q).le
  rw [Metric.mem_closedBall, dist_eq_norm]
  nlinarith [sq_nonneg (CZ.side q), norm_nonneg (y - cubeCenter q)]

/-- The ball used for cancellation is contained in the fixed cube dilation. -/
theorem closedBall_subset_enlargedCube {d : ℕ} (q : CZ.DyadicCube d) :
    Metric.closedBall (cubeCenter q) (2 * cubeRadius q) ⊆ enlargedCube q := by
  intro x hx i
  have hx' : ‖x - cubeCenter q‖ ≤ 2 * cubeRadius q := by simpa [dist_eq_norm] using hx
  exact (PiLp.norm_apply_le (x - cubeCenter q) i).trans hx'


/-- A deliberately loose volume bound keeps the original half-open grid and
allows the dilation to be closed without any boundary-measure lemma. -/
theorem enlargedCube_volume_le {d : ℕ} (q : CZ.DyadicCube d) :
    volume (enlargedCube q) ≤
      ENNReal.ofReal ((6 * Real.sqrt (d + 1 : ℝ)) ^ d) * volume (CZ.cube q) := by
  let S : Set (Fin d → ℝ) := Set.pi Set.univ
    (fun i => Ico (cubeCenter q i - 3 * cubeRadius q) (cubeCenter q i + 3 * cubeRadius q))
  have hS : MeasurableSet S := MeasurableSet.pi (Set.to_countable _) (fun i _ => measurableSet_Ico)
  have hsub : enlargedCube q ⊆ WithLp.ofLp ⁻¹' S := by
    intro x hx
    change ∀ i ∈ (Set.univ : Set (Fin d)), _
    intro i _
    have hi := abs_le.mp (hx i)
    have hr := cubeRadius_pos q
    constructor <;> dsimp <;> linarith
  apply (measure_mono hsub).trans_eq
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hS.nullMeasurableSet]
  dsimp only [S]
  rw [Real.volume_pi_Ico]
  simp only [show ∀ i : Fin d,
      cubeCenter q i + 3 * cubeRadius q - (cubeCenter q i - 3 * cubeRadius q) =
        6 * cubeRadius q by intro i; ring]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, CZ.cube_volume]
  have hr := (cubeRadius_pos q).le
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 6 * cubeRadius q),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← mul_pow]
  congr 1
  unfold cubeRadius
  ring

/-- Fatou's lemma passes a uniform restricted L¹ bound through any L² series.
This avoids asserting pointwise convergence of a general L² series. -/
theorem eLpNorm_one_le_of_hasSum_L2 {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {ι : Type} [Countable ι] (u : ι → L2 𝕜 d) (v : L2 𝕜 d)
    (hu : HasSum u v) (E : Set (Space d)) (C : ℝ≥0∞)
    (hC : ∀ s : Finset ι,
      eLpNorm (∑ i ∈ s, (u i : Space d → 𝕜)) 1 (volume.restrict E) ≤ C) :
    eLpNorm (v : Space d → 𝕜) 1 (volume.restrict E) ≤ C := by
  classical
  let U : Finset ι → L2 𝕜 d := fun s => ∑ i ∈ s, u i
  have hc : TendstoInMeasure volume (fun s => (U s : Space d → 𝕜)) atTop v :=
    tendstoInMeasure_of_tendsto_Lp hu
  have hr : TendstoInMeasure (volume.restrict E)
      (fun s => (U s : Space d → 𝕜)) atTop v := by
    intro ε hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hc ε hε)
      (fun _ => bot_le) (fun _ => Measure.restrict_le_self _)
  apply eLpNorm_le_of_tendstoInMeasure (Filter.Eventually.of_forall (fun s => ?_)) hr
    (fun s => (Lp.aestronglyMeasurable (U s)).restrict)
  rw [eLpNorm_congr_ae (ae_restrict_of_ae (Lp.coeFn_finsetSum s u))]
  exact hC s

/-- The exact good-part energy estimate from the decomposition bounds. -/
theorem good_energy_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Space d → 𝕜) (hf : Integrable f) (t : ℝ) (ht : 0 < t)
    (Q : Set (CZ.DyadicCube d)) (g : Space d → 𝕜) (hD : CZ.Decomposition f t Q g) :
    Integrable (fun x => ‖g x‖ ^ 2) ∧
      (∫ x, ‖g x‖ ^ 2) ≤ (2 : ℝ) ^ d * t * ∫ x, ‖f x‖ := by
  have hG : ∀ᵐ x ∂volume, ‖g x‖ ≤ (2 : ℝ) ^ d * t := by
    have h := ae_le_eLpNormEssSup (f := g) (μ := volume)
    have h' : eLpNormEssSup g volume ≤ ENNReal.ofReal ((2 : ℝ) ^ d * t) := by
      rw [← eLpNorm_exponent_top hD.good_integrable.aestronglyMeasurable]
      exact hD.good_infinity
    filter_upwards [h] with x hx
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      ((show ENNReal.ofReal ‖g x‖ ≤ eLpNormEssSup g volume from by simpa using hx).trans h')
  have hpoint : ∀ᵐ x ∂volume, ‖‖g x‖ ^ 2‖ ≤ ((2 : ℝ) ^ d * t) * ‖g x‖ := by
    filter_upwards [hG] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (g x)]
  have hi : Integrable (fun x => ‖g x‖ ^ 2) :=
    (hD.good_integrable.norm.const_mul _).mono'
      (hD.good_integrable.aestronglyMeasurable.norm.pow 2) hpoint
  refine ⟨hi, ?_⟩
  have hone : (∫ x, ‖g x‖) ≤ ∫ x, ‖f x‖ := by
    apply ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => norm_nonneg _) |>.mp
    rw [ofReal_integral_norm_eq_lintegral_enorm hD.good_integrable,
      ofReal_integral_norm_eq_lintegral_enorm hf,
      ← eLpNorm_one_eq_lintegral_enorm hD.good_integrable.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact hD.good_one
  calc
    (∫ x, ‖g x‖ ^ 2) ≤ ∫ x, ((2 : ℝ) ^ d * t) * ‖g x‖ :=
      integral_mono_ae hi (hD.good_integrable.norm.const_mul _)
        (hpoint.mono fun x hx => by simpa [Real.norm_of_nonneg (sq_nonneg _)] using hx)
    _ = ((2 : ℝ) ^ d * t) * ∫ x, ‖g x‖ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hone (by positivity)

/-- Uniform L¹ control outside twice a supporting ball. This uses the actual
nonsmooth distribution-kernel identity from the upstream result. -/
theorem cancellation_outside_ball {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    (T : StandardConvolutionOperator 𝕜 d) (c : Space d) (R : ℝ) (hR : 0 < R)
    (b : Space d → 𝕜) (hb : Integrable b) (h2 : MemLp b 2)
    (hs : SupportedAE b (Metric.closedBall c R)) (hm : (∫ x, b x) = 0) :
    IntegrableOn (fun x => ‖T.operator (h2.toLp b) x‖) (Metric.closedBall c (2 * R))ᶜ ∧
    (∫ x in (Metric.closedBall c (2 * R))ᶜ, ‖T.operator (h2.toLp b) x‖) ≤
      (((d : ℝ) * T.kernel.constant * 2 ^ (d + 1)) *
        ((d : ℝ) * volume.real (Metric.ball (0 : Space d) 1)) / 2) * ∫ x, ‖b x‖ := by
  let A : ℝ := (d : ℝ) * T.kernel.constant * 2 ^ (d + 1)
  let M : ℝ := ∫ x, ‖b x‖
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) T.kernel.constant_nonneg) (by positivity)
  have hM : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  let w : Space d → ℝ := fun x =>
    (Ioi (2 * R)).indicator (fun r : ℝ => 1 / r ^ (d + 1)) ‖x - c‖
  obtain ⟨hwi, hwe⟩ := radial_tail hd (2 * R) (by positivity)
  have hwi' : Integrable w := hwi.comp_sub_right c
  have hwe' : (∫ x, w x) = (d : ℝ) * volume.real (Metric.ball (0 : Space d) 1) / (2 * R) := by
    dsimp [w]
    exact (integral_sub_right_eq_self (fun z : Space d =>
      (Ioi (2 * R)).indicator (fun r : ℝ => 1 / r ^ (d + 1)) ‖z‖) c).trans hwe
  have hrep := cancellation_representation 𝕜 d T b (Metric.closedBall c R)
    (isCompact_closedBall c R) hb h2 hs hm c
  have hp : ∀ᵐ x ∂volume, x ∉ Metric.closedBall c (2 * R) →
      ‖T.operator (h2.toLp b) x‖ ≤ A * R * M * w x := by
    filter_upwards [hrep] with x hx hxe
    have hxd : 2 * R < ‖x - c‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hxe
    have hxn : x - c ≠ 0 := norm_pos_iff.mp (by linarith)
    have hxS : x ∉ Metric.closedBall c R := by
      simp only [Metric.mem_closedBall, dist_eq_norm, not_le]
      linarith
    obtain ⟨hki, hke⟩ := hx hxS
    have hbound : ∀ᵐ y ∂volume,
        ‖(T.kernel.function (x - y) - T.kernel.function (x - c)) * b y‖ ≤
          (A * R / ‖x - c‖ ^ (d + 1)) * ‖b y‖ := by
      filter_upwards [hs] with y hy
      by_cases hyS : y ∈ Metric.closedBall c R
      · have hyd : ‖y - c‖ ≤ R := by simpa [dist_eq_norm] using hyS
        have hh : ‖y - c‖ ≤ ‖x - c‖ / 2 := by linarith
        have hk := kernel_difference 𝕜 d T.kernel (x - c) (y - c) hxn hh
        have halg : x - c - (y - c) = x - y := by abel
        rw [halg] at hk
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply hk.trans
        change A * ‖y - c‖ / ‖x - c‖ ^ (d + 1) ≤ A * R / ‖x - c‖ ^ (d + 1)
        gcongr
      · simp [hy hyS]
    rw [hke]
    calc
      ‖∫ y, (T.kernel.function (x - y) - T.kernel.function (x - c)) * b y‖ ≤
          ∫ y, ‖(T.kernel.function (x - y) - T.kernel.function (x - c)) * b y‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y, (A * R / ‖x - c‖ ^ (d + 1)) * ‖b y‖ :=
        integral_mono_ae hki.norm (hb.norm.const_mul _) hbound
      _ = A * R * M * w x := by
        rw [integral_const_mul]
        simp only [w, Set.indicator_of_mem (show ‖x - c‖ ∈ Ioi (2 * R) from hxd)]
        dsimp [M]
        ring
  have hg : Integrable (fun x => A * R * M * w x) := hwi'.const_mul _
  have hbound : ∀ᵐ x ∂volume.restrict (Metric.closedBall c (2 * R))ᶜ,
      ‖T.operator (h2.toLp b) x‖ ≤ A * R * M * w x := by
    filter_upwards [ae_restrict_of_ae hp,
      ae_restrict_mem (Metric.isClosed_closedBall.isOpen_compl.measurableSet)] with x hx hxs
    exact hx hxs
  have hint : IntegrableOn (fun x => ‖T.operator (h2.toLp b) x‖)
      (Metric.closedBall c (2 * R))ᶜ := by
    apply hg.integrableOn.mono' (Lp.aestronglyMeasurable (T.operator (h2.toLp b))).norm.restrict
    simpa only [Real.norm_eq_abs, abs_norm] using hbound
  refine ⟨hint, ?_⟩
  calc
    (∫ x in (Metric.closedBall c (2 * R))ᶜ, ‖T.operator (h2.toLp b) x‖) ≤
        ∫ x in (Metric.closedBall c (2 * R))ᶜ, A * R * M * w x :=
      integral_mono_ae hint hg.integrableOn hbound
    _ ≤ ∫ x, A * R * M * w x := setIntegral_le_integral hg (ae_of_all _ fun x => by
      apply mul_nonneg (by positivity)
      dsimp [w]
      exact Set.indicator_nonneg (fun r hr => by
        have : 0 < r := lt_trans (by positivity : 0 < 2 * R) hr
        positivity) _)
    _ = (A * ((d : ℝ) * volume.real (Metric.ball (0 : Space d) 1)) / 2) * M := by
      rw [integral_const_mul, hwe']
      field_simp [ne_of_gt hR]


/-- The explicitly required off-enlarged-cube cancellation estimate. -/
theorem integrated_cancellation :
    Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11.IntegratedCancellation := by
  intro 𝕜 _ d T
  by_cases hd : 0 < d
  · let C : ℝ := (((d : ℝ) * T.kernel.constant * 2 ^ (d + 1)) *
        ((d : ℝ) * volume.real (Metric.ball (0 : Space d) 1)) / 2)
    have hC : 0 ≤ C := by
      dsimp [C]
      exact div_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) T.kernel.constant_nonneg) (by positivity))
        (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)) (by norm_num)
    refine ⟨C, hC, ?_⟩
    intro q b hb h2 hs hm
    have hs' : SupportedAE b (Metric.closedBall (cubeCenter q) (cubeRadius q)) := by
      filter_upwards [hs] with y hy hys
      exact hy (fun hyq => hys (cube_subset_closedBall q hyq))
    obtain ⟨hi, he⟩ := cancellation_outside_ball hd T (cubeCenter q) (cubeRadius q)
      (cubeRadius_pos q) b hb h2 hs' hm
    have hsub : (enlargedCube q)ᶜ ⊆ (Metric.closedBall (cubeCenter q) (2 * cubeRadius q))ᶜ :=
      Set.compl_subset_compl.mpr (closedBall_subset_enlargedCube q)
    refine ⟨hi.mono_set hsub, le_trans ?_ he⟩
    exact integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (ae_of_all _ fun _ => norm_nonneg _) hi
  · have hd0 : d = 0 := by omega
    subst d
    refine ⟨0, le_rfl, ?_⟩
    intro q b hb h2 hs hm
    have he : enlargedCube q = Set.univ := by ext x; simp [enlargedCube]
    simp [he]


/-- L¹ seminorm/integral conversion used for the bad pieces. -/
theorem eLpNorm_one_eq_integral_norm {X 𝕜 : Type} [MeasurableSpace X]
    [RCLike 𝕜] {μ : Measure X} {f : X → 𝕜} (hf : Integrable f μ) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ofReal_integral_norm_eq_lintegral_enorm hf]

theorem norm_L2_sq {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (v : L2 𝕜 d) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- A real-threshold Markov bound, independent of any finiteness of μ. -/
theorem measure_norm_gt_le_one {X 𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f : X → 𝕜) (t : ℝ) (ht : 0 < t) :
    μ {x | t < ‖f x‖} ≤ (ENNReal.ofReal t)⁻¹ * eLpNorm f 1 μ := by
  have hs : {x | t < ‖f x‖} ⊆ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} := by
    intro x hx
    change ENNReal.ofReal t ≤ _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx.le
  apply (measure_mono hs).trans
  simpa using meas_ge_le_mul_pow_eLpNorm_enorm (p := 1) μ (by norm_num) (by norm_num)
    (ENNReal.ofReal_ne_zero_iff.mpr ht) (by simp)

theorem measure_norm_gt_le_L2 {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (v : L2 𝕜 d) (t : ℝ) (ht : 0 < t) :
    volume {x | t < ‖v x‖} ≤ ENNReal.ofReal (‖v‖ ^ 2 / t ^ 2) := by
  have hs : {x | t < ‖v x‖} ⊆ {x | ENNReal.ofReal t ≤ ‖v x‖ₑ} := by
    intro x hx
    change ENNReal.ofReal t ≤ _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx.le
  apply (measure_mono hs).trans
  have hm := meas_ge_le_mul_pow_eLpNorm_enorm (p := 2) (f := (v : Space d → 𝕜))
    volume (by norm_num) (by norm_num) (ENNReal.ofReal_ne_zero_iff.mpr ht) (by simp)
  have hv : eLpNorm (v : Space d → 𝕜) 2 volume = ENNReal.ofReal ‖v‖ := by
    rw [← Lp.enorm_def, ofReal_norm]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hv,
    ← ENNReal.ofReal_pow (norm_nonneg v), ← ENNReal.inv_pow,
    ← ENNReal.ofReal_pow ht.le, ← ENNReal.div_eq_inv_mul,
    ← ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht)] using hm

/-- Summing cancellation first for finite partial sums, then taking the L² limit,
gives the uniform exterior estimate for the entire bad part. -/
theorem bad_sum_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (f : Space d → 𝕜)
    (t : ℝ) (Q : Set (CZ.DyadicCube d)) (g : Space d → 𝕜)
    (hD : CZ.Decomposition f t Q g) (h2 : MemLp f 2 volume)
    (C : ℝ) (hC : 0 ≤ C)
    (hcancel : ∀ (q : CZ.DyadicCube d) (b : Space d → 𝕜),
      Integrable b volume → ∀ h2 : MemLp b 2 volume, SupportedAE b (CZ.cube q) → (∫ x, b x) = 0 →
        IntegrableOn (fun x => ‖T.operator (h2.toLp b) x‖) (enlargedCube q)ᶜ ∧
        (∫ x in (enlargedCube q)ᶜ, ‖T.operator (h2.toLp b) x‖) ≤ C * ∫ x, ‖b x‖) :
    ∃ hg2 : MemLp g 2 volume,
      eLpNorm (T.operator (h2.toLp f - hg2.toLp g) : Space d → 𝕜) 1
        (volume.restrict (⋃ q : Q, enlargedCube q.1)ᶜ) ≤
          ENNReal.ofReal (2 * C) * eLpNorm f 1 volume := by
  classical
  obtain ⟨hg2, hb2, hs2, hsum⟩ := hD.series_two h2
  let E := (⋃ q : Q, enlargedCube q.1)ᶜ
  let u : Q → L2 𝕜 d := fun q => T.operator ((hb2 q).toLp (CZ.badPiece f q.1))
  have heq : hs2.toLp (f - g) = h2.toLp f - hg2.toLp g := by
    apply Lp.ext
    filter_upwards [hs2.coeFn_toLp, Lp.coeFn_sub (h2.toLp f) (hg2.toLp g),
      h2.coeFn_toLp, hg2.coeFn_toLp] with x hx hsub hf hg
    simp only [hx, hsub, Pi.sub_apply, hf, hg]
  have hu : HasSum u (T.operator (h2.toLp f - hg2.toLp g)) := by
    simpa only [heq] using T.operator.hasSum hsum
  refine ⟨hg2, eLpNorm_one_le_of_hasSum_L2 u _ hu E _ (fun s => ?_)⟩
  have hpiece (q : Q) : eLpNorm (u q : Space d → 𝕜) 1 (volume.restrict E) ≤
      ENNReal.ofReal C * eLpNorm (CZ.badPiece f q.1) 1 volume := by
    have hs : SupportedAE (CZ.badPiece f q.1) (CZ.cube q.1) := ae_of_all _ fun x hx => by
      by_contra hn
      exact hx (hD.bad_support q hn)
    obtain ⟨hi, hb⟩ := hcancel q.1 (CZ.badPiece f q.1) (hD.bad_integrable q)
      (hb2 q) hs (hD.bad_mean q)
    have hsub : E ⊆ (enlargedCube q.1)ᶜ := by
      intro x hx hxs
      exact hx (mem_iUnion.mpr ⟨q, hxs⟩)
    have hpart : IntegrableOn (fun x => ‖u q x‖) E := hi.mono_set hsub
    have hi' : Integrable (fun x => u q x) (volume.restrict E) :=
      (integrable_norm_iff (Lp.aestronglyMeasurable (u q)).restrict).mp hpart
    rw [eLpNorm_one_eq_integral_norm hi', eLpNorm_one_eq_integral_norm (hD.bad_integrable q),
      ← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    exact (integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (ae_of_all _ fun _ => norm_nonneg _) hi).trans hb
  calc
    eLpNorm (∑ i ∈ s, (u i : Space d → 𝕜)) 1 (volume.restrict E) ≤
        ∑ q ∈ s, eLpNorm (u q : Space d → 𝕜) 1 (volume.restrict E) := eLpNorm_sum_le le_rfl
    _ ≤ ∑ q ∈ s, ENNReal.ofReal C * eLpNorm (CZ.badPiece f q.1) 1 volume :=
      Finset.sum_le_sum fun q _ => hpiece q
    _ = ENNReal.ofReal C * ∑ q ∈ s, eLpNorm (CZ.badPiece f q.1) 1 volume :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal C * (2 * eLpNorm f 1 volume) :=
      mul_le_mul le_rfl ((ENNReal.sum_le_tsum s).trans hD.bad_one_bound) bot_le bot_le
    _ = ENNReal.ofReal (2 * C) * eLpNorm f 1 volume := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      ring

/-- All nonzero-exponent seminorms coincide on the mass-one singleton. -/
theorem eLpNorm_zero_dim {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (hp : p ≠ 0) (f : Space 0 → 𝕜) :
    eLpNorm f p volume = ‖f 0‖ₑ := by
  rw [volume_euclideanSpace_eq_dirac (Fin 0), eLpNorm_dirac _ _ hp]

/-- The d=0 Lp norms are precisely the scalar norm at the unique point. -/
theorem norm_Lp_zero_dim {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ 0) (f : Lp 𝕜 p (volume : Measure (Space 0))) :
    ‖f‖ = ‖f 0‖ := by
  rw [Lp.norm_def, eLpNorm_zero_dim hp]
  simp

/-- No positive-dimensional decomposition is used for the singleton case. -/
theorem weak_core_zero_dim {𝕜 : Type} [RCLike 𝕜]
    (T : StandardConvolutionOperator 𝕜 0) : WeakOneOnCore T ‖T.operator‖ := by
  intro f hf h2 t ht
  have hn : ‖T.operator (h2.toLp f) 0‖ ≤ ‖T.operator‖ * ‖f 0‖ := by
    have hb := T.operator.le_opNorm (h2.toLp f)
    rw [norm_Lp_zero_dim (by norm_num : (2 : ℝ≥0∞) ≠ 0), Lp.norm_toLp,
      eLpNorm_zero_dim (by norm_num : (2 : ℝ≥0∞) ≠ 0)] at hb
    simpa using hb
  have hv (s : Set (Space 0)) : volume s = (Measure.dirac (0 : Space 0)) s := by
    rw [volume_euclideanSpace_eq_dirac (Fin 0)]
  rw [hv, eLpNorm_zero_dim (by norm_num : (1 : ℝ≥0∞) ≠ 0)]
  by_cases h : t < ‖T.operator (h2.toLp f) 0‖
  · rw [Measure.dirac_apply_of_mem (show (0 : Space 0) ∈ {x | t < ‖T.operator (h2.toLp f) x‖} from h), ← ofReal_norm,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.one_le_ofReal.mpr
    rw [div_mul_eq_mul_div, le_div_iff₀ ht]
    linarith
  · simp [Measure.dirac_apply, h]

/-- Distribution-function triangle inequality, respecting arbitrary L² representatives. -/
theorem level_triangle {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : L2 𝕜 d) (t : ℝ) :
    volume {x | t < ‖(u + v) x‖} ≤
      volume {x | t / 2 < ‖u x‖} + volume {x | t / 2 < ‖v x‖} := by
  apply (measure_mono_ae (t := {x | t / 2 < ‖u x‖} ∪ {x | t / 2 < ‖v x‖}) ?_).trans
    (measure_union_le _ _)
  filter_upwards [Lp.coeFn_add u v] with x hx hxt
  change t < ‖(u + v) x‖ at hxt
  rw [hx] at hxt
  by_cases hu : t / 2 < ‖u x‖
  · exact Or.inl hu
  · apply Or.inr
    by_contra hv
    have hn := norm_add_le (u x) (v x)
    simp only [Pi.add_apply] at hxt
    have hu' := le_of_not_gt hu
    have hv' := le_of_not_gt (show ¬ t / 2 < ‖v x‖ from hv)
    linarith

/-- Splitting any measurable level set into a region and its exterior. -/
theorem measure_level_le_region {X 𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f : X → 𝕜) (hf : StronglyMeasurable f) (t : ℝ) (F : Set X) :
    μ {x | t < ‖f x‖} ≤ μ F + (μ.restrict Fᶜ) {x | t < ‖f x‖} := by
  have hA : MeasurableSet {x | t < ‖f x‖} := measurableSet_lt measurable_const hf.measurable.norm
  rw [Measure.restrict_apply hA]
  apply (measure_mono (t := F ∪ ({x | t < ‖f x‖} ∩ Fᶜ)) ?_).trans
    (measure_union_le _ _)
  intro x hx
  by_cases hF : x ∈ F
  · exact Or.inl hF
  · exact Or.inr ⟨hx, hF⟩

/-- Weak (1,1) on the entire original L¹ ∩ L² domain. -/
theorem weak_core : Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11.WeakCore := by
  intro 𝕜 _ d T
  classical
  by_cases hd : 0 < d
  · obtain ⟨C, hC, hcancel⟩ := integrated_cancellation 𝕜 d T
    let D : ℝ := (6 * Real.sqrt (d + 1 : ℝ)) ^ d
    let A : ℝ := 4 * ‖T.operator‖ ^ 2 * 2 ^ d
    have hDpos : 0 ≤ D := by dsimp [D]; positivity
    have hApos : 0 ≤ A := by dsimp [A]; positivity
    refine ⟨A + D + 4 * C, by positivity, ?_⟩
    intro f hf h2 t ht
    obtain ⟨Q, g, hdec⟩ := calderonZygmund_decomposition d hd f hf t ht
    obtain ⟨hg2, hbad⟩ := bad_sum_bound T f t Q g hdec h2 C hC hcancel
    let G : L2 𝕜 d := T.operator (hg2.toLp g)
    let B : L2 𝕜 d := T.operator (h2.toLp f - hg2.toLp g)
    let F : Set (Space d) := ⋃ q : Q, enlargedCube q.1
    have henergy : ‖hg2.toLp g‖ ^ 2 ≤ (2 : ℝ) ^ d * t * ∫ x, ‖f x‖ := by
      rw [norm_L2_sq]
      have he : (fun x => ‖hg2.toLp g x‖ ^ 2) =ᵐ[volume] (fun x => ‖g x‖ ^ 2) :=
        hg2.coeFn_toLp.mono fun x hx => by simp only [hx]
      rw [integral_congr_ae he]
      exact (good_energy_bound f hf t ht Q g hdec).2
    have hTG : ‖G‖ ^ 2 ≤ ‖T.operator‖ ^ 2 * ((2 : ℝ) ^ d * t * ∫ x, ‖f x‖) := by
      calc
        ‖G‖ ^ 2 ≤ (‖T.operator‖ * ‖hg2.toLp g‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (T.operator.le_opNorm _) _
        _ = ‖T.operator‖ ^ 2 * ‖hg2.toLp g‖ ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
    have hgood : volume {x | t / 2 < ‖G x‖} ≤ ENNReal.ofReal (A / t) * eLpNorm f 1 volume := by
      apply (measure_norm_gt_le_L2 G (t / 2) (by positivity)).trans
      rw [eLpNorm_one_eq_integral_norm hf, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_div_of_nonneg_right hTG (sq_nonneg _)).trans_eq
      dsimp [A]
      field_simp
      ring
    have hregion : volume F ≤ ENNReal.ofReal (D / t) * eLpNorm f 1 volume := by
      calc
        volume F ≤ ∑' q : Q, volume (enlargedCube q.1) := measure_iUnion_le _
        _ ≤ ∑' q : Q, ENNReal.ofReal D * volume (CZ.cube q.1) :=
          ENNReal.tsum_le_tsum fun q => enlargedCube_volume_le q.1
        _ = ENNReal.ofReal D * ∑' q : Q, volume (CZ.cube q.1) := by rw [ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal D * (eLpNorm f 1 volume / ENNReal.ofReal t) :=
          mul_le_mul le_rfl hdec.measure_bound bot_le bot_le
        _ = ENNReal.ofReal (D / t) * eLpNorm f 1 volume := by
          rw [ENNReal.ofReal_div_of_pos ht]
          simp only [div_eq_mul_inv]
          ring
    have hbadlevel : (volume.restrict Fᶜ) {x | t / 2 < ‖B x‖} ≤
        ENNReal.ofReal (4 * C / t) * eLpNorm f 1 volume := by
      apply (measure_norm_gt_le_one (volume.restrict Fᶜ) B (t / 2) (by positivity)).trans
      apply (mul_le_mul le_rfl hbad bot_le bot_le).trans_eq
      rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < t / 2),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
      ring
    have he : T.operator (h2.toLp f) = G + B := by
      dsimp [G, B]
      rw [← map_add]
      congr 1
      abel
    rw [he]
    apply (level_triangle G B t).trans
    apply (add_le_add hgood
      ((measure_level_le_region volume B (Lp.stronglyMeasurable B) (t / 2) F).trans
        (add_le_add hregion hbadlevel))).trans_eq
    rw [← add_assoc, ← add_mul, ← add_mul,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2
    ring
  · have hd0 : d = 0 := by omega
    subst d
    exact ⟨‖T.operator‖, norm_nonneg _, weak_core_zero_dim T⟩

/-- A compatible weak extension is continuous from L¹ into convergence in
measure on the whole Euclidean space, including its infinite-measure case. -/
theorem extension_tendstoInMeasure {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d)
    (S : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d) (hS : IsCompatibleExtension T S)
    (u : ℕ → L1 𝕜 d) (f : L1 𝕜 d) (hu : Tendsto u atTop (𝓝 f)) :
    TendstoInMeasure volume (fun n => (S (u n) : Space d → 𝕜)) atTop (S f) := by
  obtain ⟨C, hC, hweak⟩ := hS.2
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  have hn : Tendsto (fun n => ‖u n - f‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hb : Tendsto (fun n => ENNReal.ofReal (C / (ε / 2)) * ENNReal.ofReal ‖u n - f‖)
      atTop (𝓝 0) := by
    simp_rw [← ENNReal.ofReal_mul (div_nonneg hC he.le)]
    simpa using ENNReal.tendsto_ofReal (hn.const_mul (C / (ε / 2)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
  intro n
  apply (measure_mono_ae (t := {x | ε / 2 < ‖S (u n - f) x‖}) ?_).trans
    (hweak (u n - f) (ε / 2) he)
  have heq : (S (u n - f) : Space d → 𝕜) =ᵐ[volume]
      (fun x => S (u n) x - S f x) := by
    rw [map_sub]
    exact AEEqFun.coeFn_sub _ _
  filter_upwards [heq] with x hx hh
  rw [hx]
  change ε ≤ ‖S (u n) x - S f x‖ at hh
  linarith

/-- Density of smooth compactly supported data plus the weak estimate proves
uniqueness, independently of how a measurable extension is constructed. -/
theorem extension_unique :
    Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11.ExtensionUniqueness := by
  intro 𝕜 _ d T S S' hS hS'
  apply LinearMap.ext
  intro f
  have hd := Lp.dense_hasCompactSupport_contDiff (F := 𝕜)
    (μ := (volume : Measure (Space d))) (p := 1) (by norm_num)
  obtain ⟨u, hu, hul⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose g hg hgcompact hgsmooth using hu
  have h1 (n : ℕ) : MemLp (g n) 1 volume := (memLp_congr_ae (hg n)).mp (Lp.memLp (u n))
  have h2 (n : ℕ) : MemLp (g n) 2 volume :=
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgcompact n)
  have hu_eq (n : ℕ) : (h1 n).toLp (g n) = u n := by
    apply Lp.ext
    exact (h1 n).coeFn_toLp.trans (hg n).symm
  have hsame (n : ℕ) : (S (u n) : Space d → 𝕜) =ᵐ[volume] (S' (u n) : Space d → 𝕜) := by
    rw [← hu_eq n]
    exact (hS.1 (g n) (h1 n) (h2 n)).trans (hS'.1 (g n) (h1 n) (h2 n)).symm
  have hc := (extension_tendstoInMeasure T S hS u f hul).congr_left hsame
  exact AEEqFun.ext (tendstoInMeasure_ae_unique hc
    (extension_tendstoInMeasure T S' hS' u f hul))

/-- Combine existence of a compatible weak extension with its uniqueness. -/
theorem unique_extension_of_exists {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d)
    (h : ∃ S : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d, IsCompatibleExtension T S) :
    ∃! S : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d, IsCompatibleExtension T S := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, hS, fun S' hS' => extension_unique 𝕜 d T S' S hS' hS⟩



private theorem bound_level_of_ae_tendsto
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {v : ℕ → X → E} {g f : X → E}
    (hv : ∀ᵐ x ∂μ, Tendsto (fun k => v k x) atTop (𝓝 (g x)))
    {ε δ : ℝ} (hε : 0 < ε)
    (hb : ∀ᶠ k in atTop, μ {x | ε / 2 ≤ ‖f x - v k x‖} ≤ ENNReal.ofReal δ) :
    μ {x | ε ≤ ‖f x - g x‖} ≤ ENNReal.ofReal δ := by
  let A : ℕ → Set X := fun k => {x | ε / 2 ≤ ‖f x - v k x‖}
  let B : ℕ → Set X := fun N => ⋂ k ≥ N, A k
  have hB : Monotone B := by
    intro i j hij x hx
    simp only [B, mem_iInter] at hx ⊢
    exact fun k hk => hx k (hij.trans hk)
  have hsub : {x | ε ≤ ‖f x - g x‖} ≤ᵐ[μ] ⋃ N, B N := by
    filter_upwards [hv] with x hx hxε
    have ht : Tendsto (fun k => ‖f x - v k x‖) atTop (𝓝 ‖f x - g x‖) :=
      (tendsto_const_nhds.sub hx).norm
    have hev : ∀ᶠ k in atTop, ε / 2 < ‖f x - v k x‖ :=
      ht.eventually (eventually_gt_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact mem_iUnion.2 ⟨N, by simpa [B, A] using fun k hk => (hN k hk).le⟩
  refine (measure_mono_ae hsub).trans ?_
  rw [hB.measure_iUnion]
  refine iSup_le fun N => ?_
  obtain ⟨K, hK⟩ := eventually_atTop.1 hb
  exact (measure_mono (show B N ⊆ A (max N K) from
    fun x hx => by simpa [B] using (mem_iInter₂.1 hx) (max N K) (le_max_left _ _))).trans
      (hK _ (le_max_right _ _))

theorem exists_tendstoInMeasure_of_cauchy
    {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (u : ℕ → X → 𝕜)
    (hu : ∀ n, AEStronglyMeasurable (u n) μ)
    (hc : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ m n : ℕ, N ≤ m → N ≤ n →
        μ {x | ε ≤ ‖u m x - u n x‖} ≤ ENNReal.ofReal δ) :
    ∃ g : X → 𝕜, AEStronglyMeasurable g μ ∧ TendstoInMeasure μ u atTop g := by
  have hdy (n : ℕ) : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  choose N hN using fun n => hc ((2 : ℝ)⁻¹ ^ n) (hdy n) ((2 : ℝ)⁻¹ ^ n) (hdy n)
  let s : ℕ → ℕ := Nat.rec (N 0) (fun n a => max (N (n + 1)) (a + 1))
  have hsN (n : ℕ) : N n ≤ s n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  have hs : StrictMono s := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let A : ℕ → Set X := fun n =>
    {x | (2 : ℝ)⁻¹ ^ n ≤ ‖u (s (n + 1)) x - u (s n) x‖}
  have hof (n : ℕ) : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hA (n : ℕ) : μ (A n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    have h := hN n (s (n + 1)) (s n) ((hsN n).trans (hs.monotone (Nat.le_succ n))) (hsN n)
    simpa only [A, hof] using h
  have hsum : (∑' n, μ (A n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
    simp only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, ne_eq]
    exact ENNReal.ofNat_ne_top
  have hae : ∀ᵐ x ∂μ, ∃ a : 𝕜, Tendsto (fun n => u (s n) x) atTop (𝓝 a) := by
    filter_upwards [ae_eventually_notMem hsum] with x hx
    have hd : Summable (fun n => dist (u (s n) x) (u (s (n + 1)) x)) := by
      apply (summable_geometric_of_norm_lt_one (x := (2 : ℝ)⁻¹) (by norm_num)).of_norm_bounded_eventually_nat
      filter_upwards [hx] with n hn
      simp only [A, mem_ofPred_eq, not_le] at hn
      simpa only [Real.norm_eq_abs, dist_eq_norm_sub, abs_of_nonneg (norm_nonneg _), norm_sub_rev] using hn.le
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hd)
  obtain ⟨g, hg, hvg⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae (fun n => hu (s n)) hae
  refine ⟨g, hg.aestronglyMeasurable, tendstoInMeasure_iff_norm.2 ?_⟩
  intro ε hε
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_two_pow_lt hη.ne'
  obtain ⟨M, hM⟩ := hc (ε / 2) (by positivity) ((2 : ℝ)⁻¹ ^ j) (hdy j)
  filter_upwards [eventually_ge_atTop M] with n hn
  refine (bound_level_of_ae_tendsto (f := u n) (δ := (2 : ℝ)⁻¹ ^ j) hvg hε ?_).trans ?_
  · filter_upwards [hs.tendsto_atTop.eventually (eventually_ge_atTop M)] with k hk
    exact hM n (s k) hn hk
  · rw [hof]
    exact hj.le



lemma tendstoInMeasure_add {X E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {l : Filter ι}
    {u v : ι → X → E} {f g : X → E}
    (hu : TendstoInMeasure μ u l f) (hv : TendstoInMeasure μ v l g) :
    TendstoInMeasure μ (fun n x => u n x + v n x) l (fun x => f x + g x) := by
  rw [tendstoInMeasure_iff_norm] at hu hv ⊢
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  have hh := (hu (ε / 2) he).add (hv (ε / 2) he)
  simp only [zero_add] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro n
  apply (measure_mono (t := {x | ε / 2 ≤ ‖u n x - f x‖} ∪ {x | ε / 2 ≤ ‖v n x - g x‖}) ?_).trans
    (measure_union_le _ _)
  intro x hx
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
  have hnorm : ‖u n x + v n x - (f x + g x)‖ ≤ ‖u n x - f x‖ + ‖v n x - g x‖ := by
    convert norm_add_le (u n x - f x) (v n x - g x) using 1
    congr 1
    abel
  change ε ≤ ‖u n x + v n x - (f x + g x)‖ at hx
  linarith

lemma tendstoInMeasure_const_smul {X E ι 𝕜 : Type*} [MeasurableSpace X]
    [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {μ : Measure X} {l : Filter ι} {u : ι → X → E} {f : X → E}
    (hu : TendstoInMeasure μ u l f) (c : 𝕜) :
    TendstoInMeasure μ (fun n x => c • u n x) l (fun x => c • f x) := by
  rw [tendstoInMeasure_iff_norm] at hu ⊢
  intro ε hε
  have hc : 0 < ‖c‖ + 1 := by positivity
  have he : 0 < ε / (‖c‖ + 1) := div_pos hε hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hu (ε / (‖c‖ + 1)) he) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro x hx
  change ε ≤ ‖c • u n x - c • f x‖ at hx
  rw [← smul_sub, norm_smul] at hx
  change ε / (‖c‖ + 1) ≤ ‖u n x - f x‖
  rw [div_le_iff₀ hc]
  nlinarith [norm_nonneg (u n x - f x)]

lemma weak_bound_of_tendstoInMeasure {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {u : ℕ → X → E} {g : X → E}
    {a : ℕ → ℝ} {b C : ℝ}
    (hl : TendstoInMeasure μ u atTop g) (ha : Tendsto a atTop (𝓝 b))
    (hbound : ∀ n t, 0 < t → μ {x | t < ‖u n x‖} ≤
      ENNReal.ofReal (C / t) * ENNReal.ofReal (a n)) :
    ∀ t, 0 < t → μ {x | t < ‖g x‖} ≤ ENNReal.ofReal (2 * C / t) * ENNReal.ofReal b := by
  intro t ht
  have he : 0 < t / 2 := by positivity
  have herror := (tendstoInMeasure_iff_norm.mp hl) (t / 2) he
  have hcoef : C / (t / 2) = 2 * C / t := by ring
  have hb : Tendsto (fun n => ENNReal.ofReal (C / (t / 2)) * ENNReal.ofReal (a n))
      atTop (𝓝 (ENNReal.ofReal (C / (t / 2)) * ENNReal.ofReal b)) := by
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ha) (Or.inr ENNReal.ofReal_ne_top)
  have hsum := hb.add herror
  simp only [add_zero, hcoef] at hsum
  apply ge_of_tendsto hsum
  filter_upwards [] with n
  rw [← hcoef]
  apply (measure_mono (t := {x | t / 2 < ‖u n x‖} ∪
    {x | t / 2 ≤ ‖u n x - g x‖}) ?_).trans
    ((measure_union_le _ _).trans (add_le_add (hbound n (t / 2) he) le_rfl))
  intro x hx
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_le] at hn
  have hnorm : ‖g x‖ ≤ ‖u n x‖ + ‖u n x - g x‖ := by
    calc
      ‖g x‖ = ‖u n x - (u n x - g x)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  change t < ‖g x‖ at hx
  linarith




set_option maxHeartbeats 800000 in
theorem core_difference_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (C : ℝ) (_hC : 0 ≤ C)
    (hweak : WeakOneOnCore T C) (f g : L1 𝕜 d)
    (hf : MemLp (f : Space d → 𝕜) 2) (hg : MemLp (g : Space d → 𝕜) 2)
    (ε : ℝ) (hε : 0 < ε) :
    volume {x | ε ≤ ‖T.operator (hf.toLp f) x - T.operator (hg.toLp g) x‖} ≤
      ENNReal.ofReal (C / (ε / 2)) * ENNReal.ofReal ‖f - g‖ := by
  have h1 : Integrable (fun x => f x - g x) volume :=
    (memLp_one_iff_integrable.mp (Lp.memLp f)).sub
      (memLp_one_iff_integrable.mp (Lp.memLp g))
  have hb := hweak (fun x => f x - g x) h1 (hf.sub hg) (ε / 2) (by positivity)
  have he : T.operator ((hf.sub hg).toLp (fun x => f x - g x)) =
      T.operator (hf.toLp f) - T.operator (hg.toLp g) := by
    rw [← map_sub]
    congr 1
  have ha : (fun x => (T.operator ((hf.sub hg).toLp (fun x => f x - g x))) x) =ᵐ[volume]
      (fun x => T.operator (hf.toLp f) x - T.operator (hg.toLp g) x) := by
    rw [he]
    exact Lp.coeFn_sub _ _
  apply (measure_mono_ae (t := {x | ε / 2 < ‖T.operator ((hf.sub hg).toLp (fun x => f x - g x)) x‖}) ?_).trans
    (hb.trans_eq ?_)
  · filter_upwards [ha] with x hx hh
    rw [hx]
    change ε ≤ ‖T.operator (hf.toLp f) x - T.operator (hg.toLp g) x‖ at hh
    linarith
  · congr 1
    rw [ofReal_norm, Lp.enorm_def]
    exact eLpNorm_congr_ae (Lp.coeFn_sub f g).symm

set_option maxHeartbeats 800000 in
theorem core_images_cauchy {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (C : ℝ) (hC : 0 ≤ C)
    (hweak : WeakOneOnCore T C) (u : ℕ → L1 𝕜 d)
    (h2 : ∀ n, MemLp (u n : Space d → 𝕜) 2)
    (f : L1 𝕜 d) (hu : Tendsto u atTop (𝓝 f)) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N,
      volume {x | ε ≤ ‖T.operator ((h2 m).toLp (u m)) x -
        T.operator ((h2 n).toLp (u n)) x‖} ≤ ENNReal.ofReal δ := by
  intro ε hε δ hδ
  have hA : 0 ≤ C / (ε / 2) := div_nonneg hC (by positivity)
  let A := C / (ε / 2)
  have hη : 0 < δ / (A + 1) := div_pos hδ (by dsimp [A]; positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq (δ / (A + 1)) hη
  refine ⟨N, fun m hm n hn => (core_difference_bound T C hC hweak _ _ _ _ ε hε).trans ?_⟩
  rw [← ENNReal.ofReal_mul hA]
  apply ENNReal.ofReal_le_ofReal
  have hdist : ‖u m - u n‖ < δ / (A + 1) := by simpa [dist_eq_norm] using hN m hm n hn
  change A * ‖u m - u n‖ ≤ δ
  have hmul := mul_le_mul_of_nonneg_left hdist.le hA
  apply hmul.trans
  change A * (δ / (A + 1)) ≤ δ
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < A + 1)).mpr
  nlinarith
set_option maxHeartbeats 800000 in
theorem core_images_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (C : ℝ) (hC : 0 ≤ C)
    (hweak : WeakOneOnCore T C) (u : ℕ → L1 𝕜 d)
    (h2 : ∀ n, MemLp (u n : Space d → 𝕜) 2)
    (hu : Tendsto u atTop (𝓝 0)) :
    TendstoInMeasure volume (fun n =>
      (T.operator ((h2 n).toLp (u n)) : Space d → 𝕜)) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  have hn : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by simpa using hu.norm
  have hb : Tendsto (fun n => ENNReal.ofReal (C / (ε / 2)) * ENNReal.ofReal ‖u n‖)
      atTop (𝓝 0) := by
    simp_rw [← ENNReal.ofReal_mul (div_nonneg hC he.le)]
    simpa using ENNReal.tendsto_ofReal (hn.const_mul (C / (ε / 2)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
  intro n
  apply (measure_mono (t := {x | ε / 2 < ‖T.operator ((h2 n).toLp (u n)) x‖}) ?_).trans
    ((hweak _ (memLp_one_iff_integrable.mp (Lp.memLp (u n))) (h2 n) (ε / 2) he).trans_eq ?_)
  · intro x hx
    change ε ≤ ‖T.operator ((h2 n).toLp (u n)) x - 0‖ at hx
    simp only [sub_zero] at hx
    change ε / 2 < ‖T.operator ((h2 n).toLp (u n)) x‖
    linarith
  · change _ = ENNReal.ofReal (C / (ε / 2)) * ENNReal.ofReal ‖u n‖
    rw [← Lp.enorm_def, ofReal_norm]




variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

def coreSpace : Submodule 𝕜 (L1 𝕜 d) where
  carrier := {f | MemLp (f : Space d → 𝕜) 2 volume}
  zero_mem' := (memLp_congr_ae (Lp.coeFn_zero 𝕜 1 volume)).mpr (by simp)
  add_mem' hf hg := (memLp_congr_ae (Lp.coeFn_add _ _)).mpr (hf.add hg)
  smul_mem' a f hf := (memLp_congr_ae (Lp.coeFn_smul _ _)).mpr (hf.const_smul a)

def coreToL2 : coreSpace (𝕜 := 𝕜) (d := d) →ₗ[𝕜] L2 𝕜 d where
  toFun f := (show MemLp (f.val : Space d → 𝕜) 2 volume from f.property).toLp f.val
  map_add' f g := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans ((Lp.coeFn_add f.val g.val).trans
      (((Lp.coeFn_add _ _).trans ((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _))).symm))
  map_smul' a f := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans ((Lp.coeFn_smul a f.val).trans
      (((Lp.coeFn_smul a _).trans ((MemLp.coeFn_toLp _).const_smul a)).symm))

def coreMap (T : StandardConvolutionOperator 𝕜 d) :
    coreSpace (𝕜 := 𝕜) (d := d) →ₗ[𝕜] MeasurableClasses 𝕜 d where
  toFun f := (T.operator (coreToL2 f) : MeasurableClasses 𝕜 d)
  map_add' f g := by simp [coreToL2.map_add, map_add]
  map_smul' a f := by simp [coreToL2.map_smul, map_smul]; rfl


lemma core_dense_sequence (f : L1 𝕜 d) :
    ∃ u : ℕ → coreSpace (𝕜 := 𝕜) (d := d),
      Tendsto (fun n => (u n).val) atTop (𝓝 f) := by
  have hd := Lp.dense_hasCompactSupport_contDiff (F := 𝕜)
    (μ := (volume : Measure (Space d))) (p := 1) (by norm_num)
  obtain ⟨u, hu, hul⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose g hg hgcompact hgsmooth using hu
  have h2 (n : ℕ) : MemLp (u n : Space d → 𝕜) 2 volume :=
    (memLp_congr_ae (hg n)).mpr
      ((hgsmooth n).continuous.memLp_of_hasCompactSupport (hgcompact n))
  exact ⟨fun n => ⟨u n, h2 n⟩, hul⟩

lemma coreMap_weak (T : StandardConvolutionOperator 𝕜 d) {C : ℝ}
    (hweak : WeakOneOnCore T C) (f : coreSpace (𝕜 := 𝕜) (d := d))
    (t : ℝ) (ht : 0 < t) :
    volume {x | t < ‖coreMap T f x‖} ≤
      ENNReal.ofReal (C / t) * ENNReal.ofReal ‖f.val‖ := by
  have h2 : MemLp (f.val : Space d → 𝕜) 2 volume := f.property
  convert hweak f.val ((memLp_one_iff_integrable).mp (Lp.memLp f.val)) h2 t ht using 1
  · rfl
  · rw [← Lp.enorm_def, ofReal_norm]

/-- Graph of the extension defined by approximation from the original domain. -/
def coreLimit (T : StandardConvolutionOperator 𝕜 d) (f : L1 𝕜 d)
    (g : MeasurableClasses 𝕜 d) : Prop :=
  ∃ u : ℕ → coreSpace (𝕜 := 𝕜) (d := d),
    Tendsto (fun n => (u n).val) atTop (𝓝 f) ∧
      TendstoInMeasure volume (fun n => (coreMap T (u n) : Space d → 𝕜)) atTop g


lemma coreLimit_exists (T : StandardConvolutionOperator 𝕜 d) {C : ℝ} (hC : 0 ≤ C)
    (hweak : WeakOneOnCore T C) (f : L1 𝕜 d) :
    ∃ g : MeasurableClasses 𝕜 d, coreLimit T f g := by
  obtain ⟨u, hu⟩ := core_dense_sequence f
  have h2 (n : ℕ) : MemLp ((u n).val : Space d → 𝕜) 2 volume := (u n).property
  have hc := core_images_cauchy T C hC hweak (fun n => (u n).val) h2 f hu
  obtain ⟨g, hg, hlim⟩ := exists_tendstoInMeasure_of_cauchy volume
    (fun n => (coreMap T (u n) : Space d → 𝕜))
    (fun n => (coreMap T (u n)).aestronglyMeasurable) (by
      intro ε hε δ hδ
      obtain ⟨N, hN⟩ := hc ε hε δ hδ
      exact ⟨N, fun m n hm hn => hN m hm n hn⟩)
  exact ⟨AEEqFun.mk g hg, u, hu,
    hlim.congr_right (AEEqFun.coeFn_mk g hg).symm⟩

lemma coreLimit_unique (T : StandardConvolutionOperator 𝕜 d) {C : ℝ} (hC : 0 ≤ C)
    (hweak : WeakOneOnCore T C) {f : L1 𝕜 d} {g h : MeasurableClasses 𝕜 d}
    (hg : coreLimit T f g) (hh : coreLimit T f h) : g = h := by
  obtain ⟨u, hu, hug⟩ := hg
  obtain ⟨v, hv, hvh⟩ := hh
  let w : ℕ → coreSpace (𝕜 := 𝕜) (d := d) := fun n => v n - u n
  have hw : Tendsto (fun n => (w n).val) atTop (𝓝 0) := by
    simpa [w] using hv.sub hu
  have hw2 (n : ℕ) : MemLp ((w n).val : Space d → 𝕜) 2 volume := (w n).property
  have hzero := core_images_zero T C hC hweak (fun n => (w n).val) hw2 hw
  have hsum := tendstoInMeasure_add hzero hug
  have heq (n : ℕ) :
      (fun x => T.operator ((hw2 n).toLp (w n).val) x + coreMap T (u n) x) =ᵐ[volume]
        (coreMap T (v n) : Space d → 𝕜) := by
    have he : coreMap T (w n) + coreMap T (u n) = coreMap T (v n) := by
      rw [← map_add]
      simp [w]
    have he' := (AEEqFun.coeFn_add (coreMap T (w n)) (coreMap T (u n))).symm
    rw [he] at he'
    filter_upwards [he'] with x hx
    exact hx
  have hv_to_g : TendstoInMeasure volume
      (fun n => (coreMap T (v n) : Space d → 𝕜)) atTop g :=
    hsum.congr heq (Eventually.of_forall (fun x => zero_add (g x)))
  exact AEEqFun.ext (tendstoInMeasure_ae_unique hv_to_g hvh)

lemma coreLimit_add (T : StandardConvolutionOperator 𝕜 d)
    {f f' : L1 𝕜 d} {g g' : MeasurableClasses 𝕜 d}
    (hg : coreLimit T f g) (hg' : coreLimit T f' g') :
    coreLimit T (f + f') (g + g') := by
  obtain ⟨u, hu, hug⟩ := hg
  obtain ⟨v, hv, hvg⟩ := hg'
  refine ⟨fun n => u n + v n, hu.add hv, ?_⟩
  apply (tendstoInMeasure_add hug hvg).congr
  · intro n
    rw [map_add]
    filter_upwards [AEEqFun.coeFn_add (coreMap T (u n)) (coreMap T (v n))] with x hx
    exact hx.symm
  · exact (AEEqFun.coeFn_add _ _).symm

lemma coreLimit_smul (T : StandardConvolutionOperator 𝕜 d)
    {f : L1 𝕜 d} {g : MeasurableClasses 𝕜 d}
    (hg : coreLimit T f g) (a : 𝕜) : coreLimit T (a • f) (a • g) := by
  obtain ⟨u, hu, hug⟩ := hg
  refine ⟨fun n => a • u n, hu.const_smul a, ?_⟩
  apply (tendstoInMeasure_const_smul hug a).congr
  · intro n
    rw [map_smul]
    filter_upwards [AEEqFun.coeFn_smul a (coreMap T (u n))] with x hx
    exact hx.symm
  · filter_upwards [AEEqFun.coeFn_smul a g] with x hx
    exact hx.symm


lemma coreLimit_weak (T : StandardConvolutionOperator 𝕜 d) {C : ℝ}
    (hweak : WeakOneOnCore T C) {f : L1 𝕜 d} {g : MeasurableClasses 𝕜 d}
    (hg : coreLimit T f g) :
    ∀ t : ℝ, 0 < t → volume {x | t < ‖g x‖} ≤
      ENNReal.ofReal (2 * C / t) * ENNReal.ofReal ‖f‖ := by
  obtain ⟨u, hu, hug⟩ := hg
  exact weak_bound_of_tendstoInMeasure hug hu.norm
    (fun n t ht => coreMap_weak T hweak (u n) t ht)

lemma compatible_extension_exists (T : StandardConvolutionOperator 𝕜 d) {C : ℝ}
    (hC : 0 ≤ C) (hweak : WeakOneOnCore T C) :
    ∃ S : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d, IsCompatibleExtension T S := by
  classical
  choose F hF using (fun f : L1 𝕜 d => coreLimit_exists T hC hweak f)
  let S : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d :=
    { toFun := F
      map_add' := fun f g => coreLimit_unique T hC hweak (hF (f + g))
        (coreLimit_add T (hF f) (hF g))
      map_smul' := fun a f => coreLimit_unique T hC hweak (hF (a • f))
        (coreLimit_smul T (hF f) a) }
  refine ⟨S, ?_, ?_⟩
  · intro f h1 h2
    have h2' : MemLp (h1.toLp f : Space d → 𝕜) 2 volume :=
      (memLp_congr_ae h1.coeFn_toLp).mpr h2
    let a : coreSpace (𝕜 := 𝕜) (d := d) := ⟨h1.toLp f, h2'⟩
    have ha : coreLimit T a.val (coreMap T a) := by
      refine ⟨fun _ => a, tendsto_const_nhds, ?_⟩
      intro ε hε
      simp only [edist_self, not_le.mpr hε, Set.ofPred_false, measure_empty]
      exact tendsto_const_nhds
    have hEq : S (h1.toLp f) = coreMap T a := coreLimit_unique T hC hweak (hF a.val) ha
    rw [hEq]
    have he : coreToL2 a = h2.toLp f := h2'.toLp_congr h2 h1.coeFn_toLp
    change (T.operator (coreToL2 a) : Space d → 𝕜) =ᵐ[volume]
      (T.operator (h2.toLp f) : Space d → 𝕜)
    rw [he]
  · refine ⟨2 * C, by positivity, ?_⟩
    intro f t ht
    exact coreLimit_weak T hweak (hF f) t ht


/-- The weak endpoint operator on all L¹, compatible with the original L²
operator and unique as an almost-everywhere measurable linear map. -/
theorem unique_extension :
    Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11.UniqueExtension := by
  intro 𝕜 _ d T
  obtain ⟨C, hC, hweak⟩ := weak_core 𝕜 d T
  exact unique_extension_of_exists T (compatible_extension_exists T hC hweak)

end ExpandedFA.SingularIntegrals.CZWeak
