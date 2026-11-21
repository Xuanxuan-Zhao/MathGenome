import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.CriticalGNApproximation
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import Batteries.Tactic.OpenPrivate

noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology ContDiff
namespace P102.Sobolev.CriticalGNApproximation
open P102.U4
open private tuple_eLpNorm_le_sum represented_gradient derivative_norm_tendsto
  from MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole

/-- Norm convergence follows from convergence of the difference in Lp. -/
theorem norm_tendsto_of_error {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : ℕ → X → E} {g : X → E} (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 (eLpNorm g p μ)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr h
  have he := ht.enorm
  have heq (n : ℕ) : ‖(hf n).toLp (f n)‖ₑ = eLpNorm (f n) p μ := by
    rw [Lp.enorm_def, eLpNorm_congr_ae (hf n).coeFn_toLp]
  have heqg : ‖hg.toLp g‖ₑ = eLpNorm g p μ := by
    rw [Lp.enorm_def, eLpNorm_congr_ae hg.coeFn_toLp]
  simpa only [heq, heqg] using he

/-- Convergence in the Sobolev graph controls the actual Euclidean weak gradient. -/
theorem gradient_error_tendsto {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {v : ℕ → Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p}
    {u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p}
    (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun n => eLpNorm (weakGradient (v n) - weakGradient u) p volume)
      atTop (𝓝 0) := by
  have he : Tendsto (fun n => ∑ i : Fin d,
      ENNReal.ofReal ‖sobolevDerivative (v n) (firstIndex i) - sobolevDerivative u (firstIndex i)‖)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => derivative_norm_tendsto hv (firstIndex i))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ => bot_le) (fun n => ?_)
  let g (i : Fin d) : Space d → 𝕜 :=
    (sobolevDerivative (v n) (firstIndex i) - sobolevDerivative u (firstIndex i) :
      DomainLp 𝕜 (⊤ : Opens (Space d)) p)
  have hg (i : Fin d) : MemLp (g i) p volume := by
    simpa [g] using Lp.memLp (sobolevDerivative (v n) (firstIndex i) - sobolevDerivative u (firstIndex i))
  have hrep : weakGradient (v n) - weakGradient u =ᵐ[volume]
      (fun x => (WithLp.toLp 2 (fun i => g i x) : EuclideanSpace 𝕜 (Fin d))) := by
    have hi (i : Fin d) : g i =ᵐ[volume]
        (fun x => sobolevDerivative (v n) (firstIndex i) x - sobolevDerivative u (firstIndex i) x) := by
      exact (Lp.coeFn_sub _ _).filter_mono (by simp)
    filter_upwards [ae_all_iff.mpr hi] with x hx
    ext i
    exact (hx i).symm
  rw [eLpNorm_congr_ae hrep]
  apply (tuple_eLpNorm_le_sum Fact.out g hg).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  simpa [g, ofReal_norm] using (Lp.enorm_def
    (sobolevDerivative (v n) (firstIndex i) - sobolevDerivative u (firstIndex i))).symm

/-- A single diagonal sequence approximates both the Sobolev graph and Lr. -/
theorem simultaneous_density {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (r : ℝ≥0) (hr : 1 ≤ r)
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p)
    (hu : MemLp (sobolevUnderlying u) r volume) :
    ∃ (f : ℕ → WholeTests d 𝕜) (w : ℕ → Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p),
      (∀ n, RepresentsSobolev (f n) (w n)) ∧
      Tendsto w atTop (𝓝 u) ∧
      Tendsto (fun n => eLpNorm ((f n : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) r volume)
        atTop (𝓝 0) := by
  obtain ⟨χ, hχ, hχone⟩ := exists_unitSobolevCutoff d
  obtain ⟨v, hvrep, hvcompact, hvconv⟩ := wholeSpace_cutoff 1 p hp χ hχ hχone u
  let a : WholeTests d 𝕜 := TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  let A : ℕ → WholeTests d 𝕜 := dilatedCutoff a
  have hArep (n : ℕ) : (sobolevUnderlying (v n) : Space d → 𝕜) =ᵐ[volume]
      fun x => A n x * sobolevUnderlying u x := hvrep n
  have hAnorm (n : ℕ) (x : Space d) : ‖A n x‖ ≤ 1 := by
    change ‖(χ (((n + 1 : ℕ) : ℝ)⁻¹ • x) : 𝕜)‖ ≤ 1
    rw [RCLike.norm_ofReal, abs_of_nonneg (hχ _).1]
    exact (hχ _).2
  have ha0 : a (0 : Space d) = 1 := by
    change (χ (0 : Space d) : 𝕜) = 1
    rw [hχone 0 (by simp)]
    simp
  have hAlim (x : Space d) : Tendsto (fun n => A n x) atTop (𝓝 1) := by
    simpa only [testPartialWord, ContinuousLinearMap.id_apply, ite_true, ha0]
      using (dilatedCutoff_word_limits a []).2 x
  have hvr (n : ℕ) : MemLp (sobolevUnderlying (v n)) r volume :=
    (memLp_congr_ae (hArep n)).mpr
      (((A n).continuous.memLp_of_hasCompactSupport (p := ⊤) (A n).hasCompactSupport).mul hu)
  have hvLr : Tendsto (fun n => eLpNorm
      ((sobolevUnderlying (v n) : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) r volume) atTop (𝓝 0) := by
    apply eLpNorm_tendsto_zero_of_dominated
      (show (r : ℝ≥0∞) ≠ 0 by exact_mod_cast (zero_lt_one.trans_le hr).ne') ENNReal.coe_ne_top
      (fun n => (hvr n).aestronglyMeasurable.sub hu.aestronglyMeasurable)
      (hu.const_smul (2 : ℝ))
    · intro n
      filter_upwards [hArep n] with x hx
      change ‖sobolevUnderlying (v n) x - sobolevUnderlying u x‖ ≤ ‖(2 : ℝ) • sobolevUnderlying u x‖
      rw [hx, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        _ ≤ ‖A n x * sobolevUnderlying u x‖ + ‖sobolevUnderlying u x‖ := norm_sub_le _ _
        _ ≤ 1 * ‖sobolevUnderlying u x‖ + ‖sobolevUnderlying u x‖ := by
          rw [norm_mul]
          gcongr
          exact hAnorm n x
        _ = _ := by ring
    · filter_upwards [ae_all_iff.mpr hArep] with x hx
      have ht := ((hAlim x).mul_const (sobolevUnderlying u x)).sub_const (sobolevUnderlying u x)
      simpa only [Pi.sub_apply, ← hx, one_mul, sub_self] using ht
  let ρ := sobolevMollifierKernel d 𝕜
  have hρ := sobolevMollifierKernel_conditions d 𝕜
  choose w hw using fun n => wholeSpace_mollification 1 p hp ρ hρ (v n) (hvcompact n)
  let F (n : ℕ) (ε : ℝ) : Space d → 𝕜 :=
    localConvolution (regularDistribution ⊤ (sobolevUnderlying (v n))) (ρ ε)
  have hFLr (n : ℕ) : Tendsto (fun ε => eLpNorm
      (F n ε - (sobolevUnderlying (v n) : Space d → 𝕜)) r volume) (𝓝[>] 0) (𝓝 0) := by
    have hli : LocallyIntegrable (sobolevUnderlying (v n) : Space d → 𝕜) volume := by
      simpa using (Lp.memLp (sobolevUnderlying (v n))).locallyIntegrable (Fact.out : 1 ≤ p)
    simp only [F, localConvolution_regular_whole hli]
    change Tendsto (fun ε => eLpNorm (fun x =>
      (∫ y, ρ ε (x - y) * sobolevUnderlying (v n) y) - sobolevUnderlying (v n) x) r volume)
      (𝓝[>] 0) (𝓝 0)
    exact
      (P102.U2.ApproximateIdentities.lp_recovery volume (fun ε => (ρ ε : Space d → 𝕜))
        hρ.1 r (by exact_mod_cast hr) ENNReal.coe_ne_top (sobolevUnderlying (v n)) (hvr n)).2
  have hchoose (n : ℕ) : ∃ ε : ℝ, 0 < ε ∧
      sobolevSumError (w n ε) (v n) < ((n + 1 : ℕ) : ℝ)⁻¹ ∧
      eLpNorm (F n ε - (sobolevUnderlying (v n) : Space d → 𝕜)) r volume <
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ)⁻¹) := by
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hs := (tendsto_order.mp (hw n).2.2).2 _ hpos
    have hrsmall := (tendsto_order.mp (hFLr n)).2 _ (ENNReal.ofReal_pos.mpr hpos)
    obtain ⟨ε, hε, hεr, hεpos⟩ := (hs.and (hrsmall.and self_mem_nhdsWithin)).exists
    exact ⟨ε, hεpos, hε, hεr⟩
  choose ε hεpos hεsmall hεr using hchoose
  let f (n : ℕ) : WholeTests d 𝕜 :=
    ⟨F n (ε n), ((hw n).1 (ε n) (hεpos n)).1,
      ((hw n).1 (ε n) (hεpos n)).2.1, subset_univ _⟩
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hwconv : Tendsto (fun n => w n (ε n)) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hvconv' : Tendsto (fun n => ‖v n - u‖) atTop (𝓝 0) := by
      simpa only [sobolevSumError_eq_norm] using hvconv
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hinv.add hvconv')
    calc
      ‖w n (ε n) - u‖ ≤ ‖w n (ε n) - v n‖ + ‖v n - u‖ := by
        simpa only [dist_eq_norm] using dist_triangle (w n (ε n)) (v n) u
      _ ≤ _ := add_le_add (by simpa only [sobolevSumError_eq_norm, Nat.cast_add, Nat.cast_one] using (hεsmall n).le) le_rfl
  refine ⟨f, fun n => w n (ε n), fun n => ((hw n).1 (ε n) (hεpos n)).2.2.1, hwconv, ?_⟩
  have hupper := (ENNReal.tendsto_ofReal hinv).add hvLr
  simp only [ENNReal.ofReal_zero, zero_add] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => bot_le) (fun n => ?_)
  calc
    _ = eLpNorm ((F n (ε n) - (sobolevUnderlying (v n) : Space d → 𝕜)) +
        ((sobolevUnderlying (v n) : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜))) r volume := by
      congr 1
      ext x
      change F n (ε n) x - sobolevUnderlying u x =
        (F n (ε n) x - sobolevUnderlying (v n) x) +
          (sobolevUnderlying (v n) x - sobolevUnderlying u x)
      abel
    _ ≤ eLpNorm (F n (ε n) - (sobolevUnderlying (v n) : Space d → 𝕜)) r volume +
        eLpNorm ((sobolevUnderlying (v n) : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) r volume :=
      eLpNorm_add_le (by exact_mod_cast hr)
    _ ≤ _ := add_le_add (hεr n).le le_rfl

/-- The whole-space simultaneous approximation used in the critical GN limit. -/
theorem approximation : CriticalGNApproximationExpected.Approximation := by
  intro d _hd r hr 𝕜 _ _ u hu
  obtain ⟨f, v, hrep, hv, hLr⟩ := simultaneous_density (by simp) r hr u hu
  have hzero (n : ℕ) : (sobolevUnderlying (v n) : Space d → 𝕜) =ᵐ[volume] f n := by
    simpa [sobolevUnderlying, zeroSobolevIndex, multiPartial, partialWord] using
      hrep n (zeroSobolevIndex d 1)
  have hLp : Tendsto (fun n => eLpNorm
      ((f n : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) (d : ℝ≥0∞) volume) atTop (𝓝 0) := by
    have ht := derivative_norm_tendsto hv (zeroSobolevIndex d 1)
    apply ht.congr'
    exact Eventually.of_forall fun n => by
      have heq : ((f n : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) =ᵐ[volume]
          (sobolevUnderlying (v n) - sobolevUnderlying u : DomainLp 𝕜 (⊤ : Opens (Space d)) (d : ℝ≥0∞)) := by
        have hs := Lp.coeFn_sub (sobolevUnderlying (v n)) (sobolevUnderlying u)
        simp only [Opens.coe_top, Measure.restrict_univ] at hs
        exact ((hzero n).symm.sub EventuallyEq.rfl).trans hs.symm
      dsimp only
      rw [eLpNorm_congr_ae heq]
      simpa [sobolevUnderlying, ofReal_norm] using
        (Lp.enorm_def (sobolevUnderlying (v n) - sobolevUnderlying u))
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (show (d : ℝ≥0∞) ≠ 0 from ne_of_gt (zero_lt_one.trans_le Fact.out)) hLp).exists_seq_tendsto_ae
  have hg (n : ℕ) : MemLp (fun x =>
      (WithLp.toLp 2 (fun i : Fin d => fderiv ℝ (f n) x (coordinateVector d i)) :
        EuclideanSpace 𝕜 (Fin d))) (d : ℝ≥0∞) volume :=
    (memLp_congr_ae (represented_gradient (f n) (v n) (hrep n))).mp (weakGradient_memLp (v n))
  have hge : Tendsto (fun n => eLpNorm ((fun x =>
      (WithLp.toLp 2 (fun i : Fin d => fderiv ℝ (f n) x (coordinateVector d i)) :
        EuclideanSpace 𝕜 (Fin d))) - weakGradient u) (d : ℝ≥0∞) volume) atTop (𝓝 0) := by
    apply (gradient_error_tendsto hv).congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae
      ((represented_gradient (f n) (v n) (hrep n)).sub EventuallyEq.rfl)
  have hgnorm := norm_tendsto_of_error hg (weakGradient_memLp u) hge
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hrnorm := norm_tendsto_of_error
    (fun n => (f n).continuous.memLp_of_hasCompactSupport (p := (r : ℝ≥0∞)) (f n).hasCompactSupport)
    hu hLr
  refine ⟨fun n => f (ns n), fun n => ⟨(f (ns n)).contDiff.of_le (by simp),
    (f (ns n)).hasCompactSupport⟩, hae,
    hgnorm.comp hns.tendsto_atTop, hrnorm.comp hns.tendsto_atTop⟩

end P102.Sobolev.CriticalGNApproximation
