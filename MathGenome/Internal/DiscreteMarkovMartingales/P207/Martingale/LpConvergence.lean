import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.LpConvergence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.StrongMaximal
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UIMartingaleClosure

/-!
Higher-moment martingale convergence, paper.tex §6.6 (W35).

Doob's finite-horizon bound controls the running absolute maxima uniformly
in Lp. Their extended supremum is finite almost everywhere; Fatou gives an
Lp real representative dominating all times simultaneously. Domination by
this representative gives UI at exponent one, allowing terminal closure to
supply the fixed limit and conditional representation. Domination also gives
uniform p-integrability, so the general Vitali theorem gives Lp convergence.

This uses the maximal-envelope argument of Durrett, Probability: Theory and
Examples, fifth edition, Theorem 4.4.6 (p. 237), with terminal closure retained:
https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf.
-/

open MeasureTheory Filter
open scoped MeasureTheory Topology NNReal ENNReal
universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- A common Lp bound and Doob's finite inequality give one Lp envelope. -/
theorem exists_lp_martingale_envelope (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (p : ℝ) (hp : 1 < p) (R : ℝ≥0)
    (hbdd : ∀ n, eLpNorm (M n) (ENNReal.ofReal p) μ ≤ R) :
    ∃ Z : Ω → ℝ, MemLp Z (ENNReal.ofReal p) μ ∧
      ∀ᵐ ω ∂μ, ∀ n, |M n ω| ≤ Z ω := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hLp (n : ℕ) : MemLp (M n) (ENNReal.ofReal p) μ :=
    (hbdd n).trans_lt ENNReal.coe_lt_top
  let A := fun n => finiteMax (fun k ω => |M k ω|) n
  have hAm (n : ℕ) : Measurable (A n) :=
    Finset.measurable_range_sup'' fun k _ => by
      simpa only [Real.norm_eq_abs] using ((hM.1 k).mono (ℱ.le k) le_rfl).norm
  have hmono (ω : Ω) : Monotone (fun n => A n ω) := by
    apply monotone_nat_of_le_succ
    intro n
    change finiteMax _ n ω ≤ finiteMax _ (n + 1) ω
    rw [finiteMax_succ]
    exact le_max_left _ _
  have hA0 (n : ℕ) (ω : Ω) : 0 ≤ A n ω := by
    have h : A 0 ω ≤ A n ω := hmono ω (Nat.zero_le n)
    rw [show A 0 ω = |M 0 ω| from congrFun (finiteMax_zero _) ω] at h
    exact (abs_nonneg _).trans h
  let B : ℝ≥0 := ⟨p / (p - 1) * R, by positivity⟩
  have hAbdd (n : ℕ) : eLpNorm (A n) (ENNReal.ofReal p) μ ≤ B := by
    have hfin : IsMartingaleUpTo M ℱ μ n :=
      ⟨fun k _ => hM.1 k, fun k _ => hM.2.1 k, fun k _ => hM.2.2 k⟩
    obtain ⟨ha, hb⟩ := strong_maximal_martingale μ ℱ M n hfin p hp (hLp n)
    rw [← ofReal_lpNorm ha]
    apply ENNReal.ofReal_le_coe.mpr
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ p / (p - 1))
    exact ENNReal.toReal_mono ENNReal.coe_ne_top (hbdd n)
  let Z : Ω → ℝ := fun ω => (⨆ n, ‖A n ω‖ₑ).toReal
  have hZm : Measurable Z := (Measurable.iSup fun n => (hAm n).enorm).ennreal_toReal
  have hmn (ω : Ω) : Monotone (fun n => ‖A n ω‖ₑ) := by
    intro i j hij
    change ‖A i ω‖ₑ ≤ ‖A j ω‖ₑ
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hA0 i ω), abs_of_nonneg (hA0 j ω)]
    exact ENNReal.ofReal_le_ofReal (hmono ω hij)
  have hfinite : ∀ᵐ ω ∂μ, (⨆ n, ‖A n ω‖ₑ) < ∞ := by
    filter_upwards [ae_bdd_liminf_atTop_of_eLpNorm_bdd
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) hAbdd] with ω hω
    rwa [(tendsto_atTop_iSup (hmn ω)).liminf_eq] at hω
  have ht : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [hfinite] with ω hω
    have ht := (ENNReal.tendsto_toReal hω.ne).comp (tendsto_atTop_iSup (hmn ω))
    simpa only [Z, Function.comp_def, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hA0 _ _), ENNReal.toReal_ofReal (hA0 _ _)] using ht
  have hZbdd : eLpNorm Z (ENNReal.ofReal p) μ ≤ B :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hAbdd)
      (fun n => (hAm n).aestronglyMeasurable) hZm.aestronglyMeasurable ht
  refine ⟨Z, hZbdd.trans_lt ENNReal.coe_lt_top, ?_⟩
  filter_upwards [hfinite] with ω hω n
  have hle : ‖A n ω‖ₑ ≤ ⨆ k, ‖A k ω‖ₑ := le_iSup (fun k => ‖A k ω‖ₑ) n
  have hn : A n ω ≤ Z ω := by
    have hh := ENNReal.toReal_mono hω.ne hle
    simpa only [Z, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hA0 _ _),
      ENNReal.toReal_ofReal (hA0 _ _)] using hh
  apply le_trans _ hn
  exact Finset.le_sup' (fun k => |M k ω|) (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- Norm-bounded version, used to keep the analytic argument independent of
whether a moment bound is written with integrals or extended Lp norms. -/
theorem lp_martingale_convergence_of_eLpNorm_bdd
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (p : ℝ) (hp : 1 < p) (R : ℝ≥0)
    (hbdd : ∀ n, eLpNorm (M n) (ENNReal.ofReal p) μ ≤ R) :
    Measurable[terminalSigma ℱ] (ℱ.limitProcess M μ) ∧
      MemLp (ℱ.limitProcess M μ) (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (ℱ.limitProcess M μ ω))) ∧
      Tendsto (fun n => eLpNorm (M n - ℱ.limitProcess M μ) (ENNReal.ofReal p) μ)
        atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[ℱ.limitProcess M μ | ℱ n] := by
  have hp' : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hmeas (n : ℕ) : AEStronglyMeasurable (M n) μ :=
    ((hM.1 n).mono (ℱ.le n) le_rfl).aestronglyMeasurable
  obtain ⟨Z, hZ, henv⟩ := exists_lp_martingale_envelope μ ℱ M hM p hp R hbdd
  have hdom (n : ℕ) : (fun ω => ‖M n ω‖ₑ) ≤ᵐ[μ] (fun ω => ‖Z ω‖ₑ) := by
    filter_upwards [henv] with ω hω
    simp only [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ((hω n).trans (le_abs_self _))
  have hconst1 : UniformIntegrable (fun _ : ℕ => Z) 1 μ :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top (hZ.mono_exponent hp')
  have hui1 : UniformIntegrable M 1 μ := by
    obtain ⟨R1, hR1⟩ := hconst1.2
    refine ⟨hconst1.1.ae_mono hmeas hdom, R1, fun n => ?_⟩
    exact (eLpNorm_mono_enorm_ae (hmeas n) (hdom n)).trans (hR1 n)
  have hui : Martingale.SourceUniformIntegrable μ M :=
    (Martingale.sourceUniformIntegrable_iff_uniformIntegrable μ M).mpr hui1
  have hterm := ui_martingale_terminal μ ℱ M hM hui
  have hlim : MemLp (ℱ.limitProcess M μ) (ENNReal.ofReal p) μ :=
    Filtration.memLp_limitProcess_of_eLpNorm_bdd hmeas hbdd
  have huip : UnifIntegrable M (ENNReal.ofReal p) μ :=
    (uniformIntegrable_const (ι := ℕ) hp' ENNReal.ofReal_ne_top hZ).1.ae_mono hmeas hdom
  exact ⟨hterm.1, hlim, hterm.2.2.1,
    tendsto_Lp_finite_of_tendsto_ae hp' ENNReal.ofReal_ne_top hmeas hlim huip hterm.2.2.1,
    hterm.2.2.2.2⟩

/-- The source theorem with genuine finite p-th moments and a common real
moment bound, for every real exponent greater than one. -/
theorem lp_martingale_convergence
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (p : ℝ) (hp : 1 < p)
    (hpow : ∀ n, Integrable (fun ω => |M n ω| ^ p) μ)
    (C : ℝ) (hbdd : ∀ n, (∫ ω, |M n ω| ^ p ∂μ) ≤ C) :
    Measurable[terminalSigma ℱ] (ℱ.limitProcess M μ) ∧
      MemLp (ℱ.limitProcess M μ) (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (ℱ.limitProcess M μ ω))) ∧
      Tendsto (fun n => eLpNorm (M n - ℱ.limitProcess M μ) (ENNReal.ofReal p) μ)
        atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[ℱ.limitProcess M μ | ℱ n] := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hmeas (n : ℕ) : AEStronglyMeasurable (M n) μ :=
    ((hM.1 n).mono (ℱ.le n) le_rfl).aestronglyMeasurable
  have hLp (n : ℕ) : MemLp (M n) (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff (hmeas n) hpne ENNReal.ofReal_ne_top).mp
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using hpow n
  have hC0 : 0 ≤ C := (integral_nonneg (fun ω =>
    Real.rpow_nonneg (abs_nonneg (M 0 ω)) p)).trans (hbdd 0)
  let R : ℝ≥0 := ⟨C ^ p⁻¹, Real.rpow_nonneg hC0 _⟩
  have hnorm (n : ℕ) : eLpNorm (M n) (ENNReal.ofReal p) μ ≤ R := by
    rw [← ofReal_lpNorm (hLp n)]
    apply ENNReal.ofReal_le_coe.mpr
    rw [lpNorm_eq_integral_norm_rpow_toReal hpne ENNReal.ofReal_ne_top (hmeas n)]
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le]
    exact Real.rpow_le_rpow (integral_nonneg (fun ω =>
      Real.rpow_nonneg (abs_nonneg (M n ω)) p)) (hbdd n) (inv_nonneg.mpr hp0.le)
  exact lp_martingale_convergence_of_eLpNorm_bdd μ ℱ M hM p hp R hnorm

/-- Existential formulation, explicitly retaining the UI terminal choice. -/
theorem exists_lp_martingale_terminal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (p : ℝ) (hp : 1 < p)
    (hpow : ∀ n, Integrable (fun ω => |M n ω| ^ p) μ)
    (C : ℝ) (hbdd : ∀ n, (∫ ω, |M n ω| ^ p ∂μ) ≤ C) :
    ∃ Y : Ω → ℝ, Y =ᵐ[μ] ℱ.limitProcess M μ ∧
      Measurable[terminalSigma ℱ] Y ∧ MemLp Y (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => eLpNorm (M n - Y) (ENNReal.ofReal p) μ) atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[Y | ℱ n] :=
  ⟨ℱ.limitProcess M μ, Filter.EventuallyEq.rfl,
    lp_martingale_convergence μ ℱ M hM p hp hpow C hbdd⟩

end P207
